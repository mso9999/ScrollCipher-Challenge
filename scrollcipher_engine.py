#!/usr/bin/env python3
"""
ScrollCipher Engine -- reference implementation.

A geometric stream cipher with continuous-state keying.  Maps plaintext
symbols onto glyph nodes arranged on a unit circle and uses coupled
rotational motion on a parametric scroll-expander spiral to generate
real-valued turn counts (ciphertext).

This module contains no UI dependencies and can be used headlessly for
encode, decode, key generation, serialization, and analysis.

Usage::

    from scrollcipher_engine import KeyGenerator, Engine, serialize_key, engine_from_key

    kg = KeyGenerator()
    base_pts, params, runtime = kg.generate()
    eng = Engine(base_pts, params, runtime)
    key = serialize_key(params, runtime, eng)
    turns, _ = eng.encode("HELLO WORLD")
    eng2 = engine_from_key(key)
    decoded, _ = eng2.decode(turns)
    assert decoded == "HELLO WORLD"
"""

from __future__ import annotations

import bisect
from dataclasses import dataclass, field
from datetime import datetime
import json
import math
from pathlib import Path
from typing import Any, Tuple

import numpy as np
from mpmath import mp as _mp

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------
EPS = 1e-9
NODE_SPACING_MIN = 0.05
NODE_SPACING_MAX = 0.50
MICRO = 0.01
COARSE_BATCH = 50

RNG = np.random.default_rng()

# ---------------------------------------------------------------------------
# Pi-digit cache for differential spacing
# ---------------------------------------------------------------------------
_PI_DIGIT_CACHE: str = ""


def pi_digits(offset: int, count: int) -> list[int]:
    """Return *count* decimal digits of pi starting at position *offset*
    (0-indexed after the '3.', so offset=0 gives '1', offset=1 gives '4', etc.)."""
    global _PI_DIGIT_CACHE
    needed = offset + count
    if len(_PI_DIGIT_CACHE) < needed:
        _mp.dps = needed + 60
        pi_str = _mp.nstr(_mp.pi, needed + 20, strip_zeros=False)
        _PI_DIGIT_CACHE = pi_str.replace(".", "")[1:]  # drop leading '3'
    return [int(_PI_DIGIT_CACHE[offset + i]) for i in range(count)]


def compute_gap_spacings(pi_offset: int, count: int) -> list[float]:
    """Compute per-glyph gap spacings from pi digits at the given offset.

    Each digit d_i (0-9) maps linearly to [NODE_SPACING_MIN, NODE_SPACING_MAX].
    Returns a list of *count* gap widths.
    """
    digits = pi_digits(pi_offset, count)
    span = NODE_SPACING_MAX - NODE_SPACING_MIN
    return [NODE_SPACING_MIN + span * d / 9.0 for d in digits]


def cumulative_spacings(gaps: list[float]) -> list[float]:
    """Return cumulative positions [0, gap[0], gap[0]+gap[1], ...]."""
    cum = [0.0]
    for g in gaps:
        cum.append(cum[-1] + g)
    return cum


# ---------------------------------------------------------------------------
# SpiralParams
# ---------------------------------------------------------------------------
@dataclass
class SpiralParams:
    c1: float
    c2: float
    c3: float
    c4: float
    c5: float
    n_turns: float
    orbital_radius: float
    d: float
    u_min: float
    u_max: float


# ---------------------------------------------------------------------------
# RuntimeConfig
# ---------------------------------------------------------------------------
@dataclass
class RuntimeConfig:
    units_turn: float
    rad_turn: float
    ascii_rad_turn: float
    node_spacing: float
    direction_mode: int
    latch_mode: int
    rewrap_reset_mode: int
    ascii_count: int
    glyph_order: list[int] = field(default_factory=list)
    pi_offset: int = -1  # -1 = disabled (uniform spacing); >=0 = pi-digit offset

    def __post_init__(self) -> None:
        if not self.glyph_order:
            self.glyph_order = list(range(self.ascii_count))
        self._rebuild_index()

    def _rebuild_index(self) -> None:
        self._code_to_index = [0] * self.ascii_count
        for idx, code in enumerate(self.glyph_order):
            if 0 <= code < self.ascii_count:
                self._code_to_index[code] = idx

    @property
    def code_to_index(self) -> list[int]:
        return self._code_to_index


# ---------------------------------------------------------------------------
# Geometry primitives
# ---------------------------------------------------------------------------
def paper_curve_coeffs(
    u: np.ndarray, p: SpiralParams
) -> Tuple[np.ndarray, np.ndarray]:
    """Return a(U), b(U) from the intrinsic-curve coordinate map."""
    a = (
        (p.c2 - 6.0 * p.c4)
        + (2.0 * p.c3 - 24.0 * p.c5) * u
        + 3.0 * p.c4 * (u**2)
        + 4.0 * p.c5 * (u**3)
    )
    b = (
        (2.0 * p.c3 - 24.0 * p.c5)
        + 6.0 * p.c4 * u
        + 12.0 * p.c5 * (u**2)
    )
    return a, b


def paper_spiral_xy(u: np.ndarray, p: SpiralParams) -> np.ndarray:
    a, b = paper_curve_coeffs(u, p)
    x = a * np.sin(u) + b * np.cos(u)
    y = b * np.sin(u) - a * np.cos(u)
    return np.column_stack((x, y))


def orientation(a: np.ndarray, b: np.ndarray, c: np.ndarray) -> float:
    return (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])


def segments_intersect(
    p1: np.ndarray, p2: np.ndarray, q1: np.ndarray, q2: np.ndarray
) -> bool:
    o1 = orientation(p1, p2, q1)
    o2 = orientation(p1, p2, q2)
    o3 = orientation(q1, q2, p1)
    o4 = orientation(q1, q2, p2)
    return (o1 * o2 < 0.0) and (o3 * o4 < 0.0)


def has_self_intersection(points: np.ndarray) -> bool:
    n = points.shape[0]
    step = max(1, n // 220)
    pts = points[::step]
    m = pts.shape[0]
    if m < 5:
        return False
    for i in range(m - 1):
        p1, p2 = pts[i], pts[i + 1]
        for j in range(i + 2, m - 1):
            if abs(i - j) <= 1:
                continue
            q1, q2 = pts[j], pts[j + 1]
            if segments_intersect(p1, p2, q1, q2):
                return True
    return False


def normalize_and_align(
    points: np.ndarray,
) -> Tuple[np.ndarray, float]:
    centered = points - points.mean(axis=0)
    radii = np.linalg.norm(centered, axis=1)
    r_max = float(np.max(radii))
    if r_max < EPS:
        raise ValueError("Degenerate spiral: max radius too small.")
    unit = centered / r_max
    unit_radii = np.linalg.norm(unit, axis=1)
    i_anchor = int(np.argmax(unit_radii))
    anchor = unit[i_anchor]
    angle = math.atan2(anchor[1], anchor[0])
    delta = (math.pi / 2.0) - angle
    c, s = math.cos(delta), math.sin(delta)
    rot = np.array([[c, -s], [s, c]])
    aligned = unit @ rot.T
    return aligned, delta


def wrap_to_pi(angle: np.ndarray | float) -> np.ndarray | float:
    return (angle + math.pi) % (2.0 * math.pi) - math.pi


def rotate_points(points: np.ndarray, theta: float) -> np.ndarray:
    c, s = math.cos(theta), math.sin(theta)
    rot = np.array([[c, -s], [s, c]])
    return points @ rot.T


def rotate_point(point: np.ndarray, theta: float) -> np.ndarray:
    c, s = math.cos(theta), math.sin(theta)
    return np.array(
        [c * point[0] - s * point[1], s * point[0] + c * point[1]]
    )


def build_motion_path(
    points: np.ndarray,
) -> Tuple[np.ndarray, np.ndarray]:
    """Build inward->outward path from near origin to near anchor (0,1)."""
    start_idx = int(
        np.argmin(np.linalg.norm(points - np.array([0.0, 0.0]), axis=1))
    )
    anchor_idx = int(
        np.argmin(np.linalg.norm(points - np.array([0.0, 1.0]), axis=1))
    )
    if start_idx <= anchor_idx:
        path = points[start_idx : anchor_idx + 1]
    else:
        path = points[anchor_idx : start_idx + 1][::-1]
    if path.shape[0] < 2:
        path = points.copy()
    if np.linalg.norm(path[0]) > np.linalg.norm(path[-1]):
        path = path[::-1]
    seg = np.linalg.norm(np.diff(path, axis=0), axis=1)
    cum = np.concatenate(([0.0], np.cumsum(seg)))
    return path, cum


def point_at_arc(
    path: np.ndarray, cum_arc: np.ndarray, s: float
) -> np.ndarray:
    if path.shape[0] == 0:
        return np.array([0.0, 0.0])
    if path.shape[0] == 1:
        return path[0]
    s_clamped = float(np.clip(s, 0.0, cum_arc[-1]))
    idx = int(np.searchsorted(cum_arc, s_clamped, side="right") - 1)
    idx = max(0, min(idx, path.shape[0] - 2))
    ds = cum_arc[idx + 1] - cum_arc[idx]
    if ds < EPS:
        return path[idx]
    alpha = (s_clamped - cum_arc[idx]) / ds
    return (1.0 - alpha) * path[idx] + alpha * path[idx + 1]


# ---------------------------------------------------------------------------
# Spiral generation
# ---------------------------------------------------------------------------
def sample_paper_params(
    rng: np.random.Generator | None = None,
) -> SpiralParams:
    if rng is None:
        rng = RNG
    c1 = 0.0
    n_turns = float(rng.uniform(3.0, 12.0))
    r_low = max(1.5, 2.4241 * n_turns - 16.1332)
    orbital_radius = float(rng.uniform(r_low, 60.0))
    d_low = 0.5 * orbital_radius
    d_high = 30.0
    d = d_high if d_low >= d_high else float(rng.uniform(d_low, d_high))
    c2 = float(rng.uniform(-4.0, 4.0))

    c3_lo_1 = 1.0145 * n_turns - 8.8014
    c3_hi_1 = -0.40411 * n_turns + 18.0718
    c3_lo_2 = 0.083725 * d - 4.8712
    c3_hi_2 = 0.54374 * d + 0.63304
    c3_low = max(c3_lo_1, c3_lo_2)
    c3_high = min(c3_hi_1, c3_hi_2)
    if c3_low >= c3_high:
        raise ValueError("No feasible c3 interval from strict constraints.")
    c3 = float(rng.uniform(c3_low, c3_high))

    c4_low = -0.058902 * c3 - 0.016956
    c4_high = -0.083835 * c3 + 1.1011
    if c4_low >= c4_high:
        raise ValueError("No feasible c4 interval from strict constraints.")
    c4 = float(rng.uniform(c4_low, c4_high))

    c5_low = -0.016401 * c4 - 0.0013445
    c5_upper_cap = 0.38923 * math.exp(-0.64318 * n_turns) + 0.0014341
    c5_high = min(0.02, c5_upper_cap)
    if c5_low >= c5_high:
        raise ValueError("No feasible c5 interval from strict constraints.")
    c5 = float(rng.uniform(c5_low, c5_high))

    return SpiralParams(
        c1=c1,
        c2=c2,
        c3=c3,
        c4=c4,
        c5=c5,
        n_turns=n_turns,
        orbital_radius=orbital_radius,
        d=d,
        u_min=0.0,
        u_max=2.0 * math.pi * n_turns,
    )


def is_viable_spiral(points: np.ndarray) -> bool:
    if points.shape[0] < 20:
        return False
    if not np.all(np.isfinite(points)):
        return False
    centered = points - points.mean(axis=0)
    radii = np.linalg.norm(centered, axis=1)
    if np.max(radii) < 1e-5:
        return False
    dr = np.diff(radii)
    negative_ratio = float(np.mean(dr < 0.0))
    if negative_ratio > 0.48:
        return False
    if has_self_intersection(points):
        return False
    return True


def generate_valid_spiral(
    max_attempts: int = 400, rng: np.random.Generator | None = None
) -> Tuple[np.ndarray, SpiralParams]:
    for _ in range(max_attempts):
        try:
            params = sample_paper_params(rng)
        except ValueError:
            continue
        u = np.linspace(params.u_min, params.u_max, 1300)
        pts = paper_spiral_xy(u, params)
        if not is_viable_spiral(pts):
            continue
        aligned, _ = normalize_and_align(pts)
        if not np.all(np.isfinite(aligned)):
            continue
        if float(np.max(np.linalg.norm(aligned, axis=1))) > 1.0000001:
            continue
        return aligned, params
    raise RuntimeError(
        "Failed to generate a valid spiral in the allotted attempts."
    )


def try_build_aligned_spiral(params: SpiralParams) -> np.ndarray | None:
    u = np.linspace(params.u_min, params.u_max, 1300)
    pts = paper_spiral_xy(u, params)
    if not is_viable_spiral(pts):
        return None
    try:
        aligned, _ = normalize_and_align(pts)
    except ValueError:
        return None
    if float(np.max(np.linalg.norm(aligned, axis=1))) > 1.0000001:
        return None
    return aligned


def clip_slider_params(
    base: SpiralParams,
    c2: float,
    c3: float,
    c4: float,
    c5: float,
    n_turns: float,
) -> SpiralParams:
    c3_lo_1 = 1.0145 * n_turns - 8.8014
    c3_hi_1 = -0.40411 * n_turns + 18.0718
    c3_lo_2 = 0.083725 * base.d - 4.8712
    c3_hi_2 = 0.54374 * base.d + 0.63304
    c3_low = max(c3_lo_1, c3_lo_2)
    c3_high = min(c3_hi_1, c3_hi_2)
    c3_use = float(np.clip(c3, c3_low, c3_high))
    c4_low = -0.058902 * c3_use - 0.016956
    c4_high = -0.083835 * c3_use + 1.1011
    c4_use = float(np.clip(c4, c4_low, c4_high))
    c5_low = -0.016401 * c4_use - 0.0013445
    c5_upper_cap = 0.38923 * math.exp(-0.64318 * n_turns) + 0.0014341
    c5_high = min(0.02, c5_upper_cap)
    c5_use = float(np.clip(c5, c5_low, c5_high))
    return SpiralParams(
        c1=0.0,
        c2=float(np.clip(c2, -4.0, 4.0)),
        c3=c3_use,
        c4=c4_use,
        c5=c5_use,
        n_turns=float(np.clip(n_turns, 3.0, 12.0)),
        orbital_radius=base.orbital_radius,
        d=base.d,
        u_min=0.0,
        u_max=2.0 * math.pi * float(np.clip(n_turns, 3.0, 12.0)),
    )


# ---------------------------------------------------------------------------
# ASCII / glyph utilities
# ---------------------------------------------------------------------------
def build_ascii_nodes(
    anchor_theta: float,
    spacing: float | list[float],
    direction_sign: int,
    node_count: int,
) -> dict[str, np.ndarray]:
    """Build glyph node positions on the unit circle.

    *spacing* may be a single float (uniform) or a list of per-gap spacings
    (differential, from pi-offset).
    """
    if isinstance(spacing, (list, np.ndarray)) and len(spacing) >= node_count:
        cum = np.zeros(node_count)
        for i in range(1, node_count):
            cum[i] = cum[i - 1] + spacing[i - 1]
        arc = cum * float(direction_sign)
    else:
        s = float(spacing) if not isinstance(spacing, (list, np.ndarray)) else float(spacing[0])
        idx = np.arange(node_count, dtype=float)
        arc = idx * s * float(direction_sign)
    angles_unwrapped = anchor_theta + arc
    angles_wrapped = (angles_unwrapped + math.pi) % (2.0 * math.pi) - math.pi
    wraps = np.floor(np.abs(arc) / (2.0 * math.pi)).astype(int)
    return {
        "index": np.arange(node_count, dtype=int),
        "ascii": np.arange(node_count, dtype=int),
        "wrap_n": wraps,
        "theta": angles_wrapped,
        "x": np.cos(angles_wrapped),
        "y": np.sin(angles_wrapped),
    }


def glyph_for_ascii(code: int) -> str:
    if 32 <= code <= 126:
        return chr(code)
    return "."


def identity_glyph_order(count: int) -> list[int]:
    return list(range(max(0, int(count))))


def direction_for_index_mode(i: int, mode: int) -> str:
    if mode == 0:
        return "CW"
    if mode == 1:
        return "CCW"
    if mode == 2:
        return "CW" if (i % 2) == 0 else "CCW"
    if mode == 3:
        return "CCW" if (i % 2) == 0 else "CW"
    n = mode
    current = "CW" if (n % 2) == 0 else "CCW"
    if i == 0:
        return current
    for idx in range(1, i + 1):
        if ((idx + 1) % n) == 0:
            continue
        current = "CCW" if current == "CW" else "CW"
    return current


def latch_for_index_mode(i: int, mode: int) -> bool:
    if mode == 0:
        return False
    if mode == 1:
        return True
    n = mode
    nth = ((i + 1) % n) == 0
    if (n % 2) == 0:
        return nth
    return not nth


def should_reset_rewrap_mode(found_count: int, mode: int) -> bool:
    if mode == 0:
        return True
    if mode == 1:
        return (found_count % 2) == 0
    return (found_count % mode) == 0


def round_sigfigs(x: float, n: int) -> float:
    if x == 0.0:
        return 0.0
    magnitude = math.floor(math.log10(abs(x)))
    return round(x, -int(magnitude) + (n - 1))


# ---------------------------------------------------------------------------
# Engine -- core encode/decode
# ---------------------------------------------------------------------------
class Engine:
    """Stateful ScrollCipher engine.  Holds the spiral geometry, runtime
    configuration, and mutable motion/reader state.  Provides deterministic
    ``encode`` and ``decode`` methods."""

    def __init__(
        self,
        base_pts: np.ndarray,
        params: SpiralParams,
        runtime: RuntimeConfig,
    ) -> None:
        self.base_pts = base_pts
        self.params = params
        self.runtime = runtime
        self.base_path_pts, self.base_path_cum = build_motion_path(base_pts)

        self.s_pos = 0.0
        self.rotation = 0.0
        self.counter_rotation = 0.0
        self.anchor_base_theta = math.pi / 2.0

        self.reader_initialized = False
        self.reader_rel_prev = 0.0
        self.reader_arc_prev = 0.0
        self.reader_arc = 0.0

        self.seed_spacing = runtime.node_spacing
        self.pi_offset = runtime.pi_offset
        self.pi_offset_seed = runtime.pi_offset
        self._recompute_spacings()

    def _recompute_spacings(self) -> None:
        """Recompute per-glyph gap spacings and cumulative positions."""
        n = self.runtime.ascii_count
        if self.pi_offset >= 0:
            self._gap_spacings = compute_gap_spacings(self.pi_offset, n)
        else:
            self._gap_spacings = [self.runtime.node_spacing] * n
        self._cum_spacings = cumulative_spacings(self._gap_spacings)

    # -- internal helpers --------------------------------------------------

    @property
    def _total_arc(self) -> float:
        if self.base_path_cum.shape[0] == 0:
            return 0.0
        return float(self.base_path_cum[-1])

    def _anchor_theta(self) -> float:
        return float(self.anchor_base_theta + self.counter_rotation)

    def _theta_intersect(self) -> float:
        pxy_base = point_at_arc(
            self.base_path_pts, self.base_path_cum, self.s_pos
        )
        pxy = rotate_point(pxy_base, self.rotation)
        return math.atan2(float(pxy[1]), float(pxy[0]))

    # -- reader ------------------------------------------------------------

    def reset_reader(self) -> None:
        self.reader_initialized = False
        self.reader_rel_prev = 0.0
        self.reader_arc_prev = 0.0
        self.reader_arc = 0.0

    def reset_reader_preserve_theta(
        self, glyph_theta: float | None = None
    ) -> None:
        theta = (
            glyph_theta
            if glyph_theta is not None
            else self._theta_intersect()
        )
        rel = float(wrap_to_pi(theta - self._anchor_theta()))
        rel_wrap1 = rel % (2.0 * math.pi)
        self.reader_initialized = True
        self.reader_rel_prev = rel
        self.reader_arc_prev = rel_wrap1
        self.reader_arc = rel_wrap1
        self.snap_tracer_to_theta(theta)

    def _unwrap_rel(self, rel_raw: float, ref: float) -> float:
        return float(
            rel_raw
            + (2.0 * math.pi) * round((ref - rel_raw) / (2.0 * math.pi))
        )

    def advance_reader(self) -> None:
        rel_raw = float(
            wrap_to_pi(self._theta_intersect() - self._anchor_theta())
        )
        if not self.reader_initialized:
            self.reader_initialized = True
            self.reader_rel_prev = rel_raw
            self.reader_arc_prev = self.reader_arc
            return
        rel = self._unwrap_rel(rel_raw, self.reader_rel_prev)
        d_rel = rel - self.reader_rel_prev
        self.reader_arc_prev = self.reader_arc
        self.reader_arc = max(0.0, self.reader_arc + abs(d_rel))
        self.reader_rel_prev = rel

    # -- glyph lookup ------------------------------------------------------

    def _period(self) -> float:
        return self._cum_spacings[self.runtime.ascii_count]

    def _glyph_position(self, idx: int) -> float:
        """Cumulative angular offset for glyph at wound-line index *idx*."""
        return self._cum_spacings[idx]

    def theta_for_code(self, code: int) -> float | None:
        if code < 0 or code >= self.runtime.ascii_count:
            return None
        idx = self.runtime.code_to_index[code]
        return float(
            wrap_to_pi(
                self._anchor_theta() + self._glyph_position(idx)
            )
        )

    def reader_code(self) -> int:
        period = self._period()
        if period <= 0.0:
            return -1
        arc_mod = self.reader_arc % period
        n = self.runtime.ascii_count
        pos = bisect.bisect_right(self._cum_spacings, arc_mod, 0, n) - 1
        pos = max(0, min(pos, n - 1))
        dist_lo = abs(arc_mod - self._cum_spacings[pos])
        if pos + 1 < n:
            dist_hi = abs(arc_mod - self._cum_spacings[pos + 1])
            if dist_hi < dist_lo:
                pos = pos + 1
        else:
            dist_wrap = abs(arc_mod - period)
            if dist_wrap < dist_lo:
                pos = 0
        return int(self.runtime.glyph_order[pos % n])

    def _first_cross_fraction(
        self, code: int, arc0: float, arc1: float
    ) -> float | None:
        if code < 0 or code >= self.runtime.ascii_count:
            return None
        period = self._period()
        if period <= 0.0:
            return None
        target_idx = self.runtime.code_to_index[code]
        target0 = self._glyph_position(target_idx)
        a0, a1 = float(arc0), float(arc1)
        if a1 < a0:
            a0, a1 = a1, a0
        eps = 1e-12
        k = int(math.ceil(((a0 - eps) - target0) / period))
        target = target0 + float(k) * period
        if target > (a1 + eps):
            return None
        span = a1 - a0
        if span <= eps:
            return 1.0
        frac = (target - a0) / span
        return float(min(1.0, max(0.0, frac)))

    # -- state snapshot / restore ------------------------------------------

    def snapshot(
        self,
    ) -> tuple[float, float, float, float, bool, float, float, float]:
        return (
            self.s_pos,
            self.rotation,
            self.counter_rotation,
            self.anchor_base_theta,
            self.reader_initialized,
            self.reader_rel_prev,
            self.reader_arc_prev,
            self.reader_arc,
        )

    def restore(
        self,
        snap: tuple[float, float, float, float, bool, float, float, float],
    ) -> None:
        (
            self.s_pos,
            self.rotation,
            self.counter_rotation,
            self.anchor_base_theta,
            self.reader_initialized,
            self.reader_rel_prev,
            self.reader_arc_prev,
            self.reader_arc,
        ) = snap

    # -- analytical override -----------------------------------------------

    def _analytical_phase_deltas(
        self, turns_val: float, phase_idx: int
    ) -> tuple[float, float]:
        """Single-multiply rotation/counter change, eliminating FP drift."""
        is_latched = latch_for_index_mode(
            int(phase_idx), int(self.runtime.latch_mode)
        )
        if is_latched:
            rot_delta = turns_val * self.runtime.rad_turn
            ctr_delta = -turns_val * self.runtime.ascii_rad_turn
        else:
            direction = direction_for_index_mode(
                int(phase_idx), int(self.runtime.direction_mode)
            )
            dir_sign = -1.0 if direction == "CW" else 1.0
            rot_delta = dir_sign * turns_val * self.runtime.rad_turn
            ctr_delta = -dir_sign * turns_val * self.runtime.ascii_rad_turn
        return rot_delta, ctr_delta

    # -- micro-step integration --------------------------------------------

    def _apply_micro_delta(self, delta: float, phase_idx: int) -> None:
        ds = (delta / (2.0 * math.pi)) * self.runtime.units_turn
        total_arc = self._total_arc
        self.s_pos += ds
        wrapped = False
        if total_arc > EPS:
            s_use = self.s_pos % total_arc
            wrapped = abs(s_use - self.s_pos) > EPS
            self.s_pos = s_use
        latch = latch_for_index_mode(
            int(phase_idx), int(self.runtime.latch_mode)
        )
        anchor_delta = abs(delta) if latch else delta
        self.rotation = (
            self.rotation
            + (anchor_delta / (2.0 * math.pi)) * self.runtime.rad_turn
        ) % (2.0 * math.pi)
        self.counter_rotation = (
            self.counter_rotation
            - (anchor_delta / (2.0 * math.pi)) * self.runtime.ascii_rad_turn
        ) % (2.0 * math.pi)
        if wrapped:
            theta = self._theta_intersect()
            anchor_theta = self._anchor_theta()
            rel_raw = float(wrap_to_pi(theta - anchor_theta))
            self.reader_rel_prev = rel_raw
        else:
            self.advance_reader()

    def apply_knob_delta(self, delta: float, phase_idx: int) -> None:
        rem = abs(float(delta))
        if rem <= 0.0:
            return
        sign = -1.0 if float(delta) < 0.0 else 1.0
        while rem > 1e-15:
            d = sign * min(MICRO, rem)
            self._apply_micro_delta(d, phase_idx)
            rem -= abs(d)

    # -- snap helpers ------------------------------------------------------

    def snap_reader_to_code(
        self, code: int, glyph_theta: float | None = None
    ) -> None:
        if code < 0 or code >= self.runtime.ascii_count:
            return
        period = self._period()
        if period <= 0.0:
            return
        target_idx = self.runtime.code_to_index[code]
        target = self._glyph_position(target_idx)
        k = int(round((self.reader_arc - target) / period))
        snapped = target + float(k) * period
        self.reader_arc_prev = snapped
        self.reader_arc = snapped
        theta = (
            glyph_theta
            if glyph_theta is not None
            else self._theta_intersect()
        )
        rel_raw = float(wrap_to_pi(theta - self._anchor_theta()))
        self.reader_initialized = True
        self.reader_rel_prev = self._unwrap_rel(
            rel_raw, self.reader_rel_prev
        )

    def snap_tracer_to_theta(self, target_theta: float) -> None:
        if self.base_path_pts.shape[0] < 2:
            return
        desired = float(wrap_to_pi(target_theta - self.rotation))
        base_angles = np.arctan2(
            self.base_path_pts[:, 1], self.base_path_pts[:, 0]
        )
        err = np.abs(wrap_to_pi(base_angles - desired))
        min_err = float(np.min(err))
        cands = np.where(err <= (min_err + 1e-6))[0]
        if cands.size == 0:
            idx = int(np.argmin(err))
        else:
            idx = int(np.min(cands))
        idx = max(0, min(idx, self.base_path_cum.shape[0] - 1))
        self.s_pos = float(self.base_path_cum[idx])
        self.advance_reader()

    def _phase_transition(
        self,
        code: int,
        phase_idx: int,
        total_phases: int,
        glyph_theta: float | None,
    ) -> bool:
        """Post-snap phase transition.  Returns True if rewrap reset."""
        did_reset = False
        if phase_idx < total_phases - 1:
            if self.pi_offset >= 0:
                self.pi_offset += code
                self._recompute_spacings()
            else:
                updated = float(
                    np.clip(
                        float(self.seed_spacing) * (float(code) / 90.0),
                        NODE_SPACING_MIN,
                        NODE_SPACING_MAX,
                    )
                )
                self.runtime.node_spacing = updated

            self.runtime._rebuild_index()
            found_count = phase_idx + 1
            did_reset = should_reset_rewrap_mode(
                found_count, self.runtime.rewrap_reset_mode
            )
            if did_reset:
                if self.pi_offset >= 0:
                    self.pi_offset = self.pi_offset_seed
                    self._recompute_spacings()
                else:
                    self.runtime.node_spacing = self.seed_spacing
                self.runtime._rebuild_index()
                self.anchor_base_theta = math.pi / 2.0
                self.counter_rotation = 0.0
            else:
                self.anchor_base_theta = self._anchor_theta()
                self.counter_rotation = 0.0
            self.reset_reader_preserve_theta(glyph_theta=glyph_theta)
        return did_reset

    # ---------------------------------------------------------------
    # Encode: coarse-fine search
    # ---------------------------------------------------------------
    def encode(
        self, message: str, max_radians: float = 300.0
    ) -> tuple[list[float], list[dict[str, Any]]]:
        codes = [ord(c) for c in message]
        turns: list[float] = []
        logs: list[dict[str, Any]] = []
        self.reset_reader()
        phase_rot_start = self.rotation
        phase_ctr_start = self.counter_rotation
        max_micro = int(max_radians / MICRO)

        for i, code in enumerate(codes):
            direction = direction_for_index_mode(
                i, self.runtime.direction_mode
            )
            sign = 1.0 if direction == "CCW" else -1.0
            phase_turns = 0.0
            found = False
            total_steps = 0

            while total_steps < max_micro:
                batch = min(COARSE_BATCH, max_micro - total_steps)
                snap = self.snapshot()
                arc0 = float(self.reader_arc)
                for _ in range(batch):
                    self._apply_micro_delta(sign * MICRO, i)
                arc1 = float(self.reader_arc)
                frac = self._first_cross_fraction(code, arc0, arc1)
                if frac is None:
                    phase_turns += float(batch) * MICRO / (2.0 * math.pi)
                    total_steps += batch
                    continue
                self.restore(snap)
                for _ in range(batch):
                    snap_fine = self.snapshot()
                    arc0_f = float(self.reader_arc)
                    self._apply_micro_delta(sign * MICRO, i)
                    arc1_f = float(self.reader_arc)
                    frac_f = self._first_cross_fraction(
                        code, arc0_f, arc1_f
                    )
                    if frac_f is not None:
                        self.restore(snap_fine)
                        d_eff = sign * MICRO * float(frac_f)
                        self._apply_micro_delta(d_eff, i)
                        phase_turns += abs(d_eff) / (2.0 * math.pi)
                        found = True
                        break
                    phase_turns += MICRO / (2.0 * math.pi)
                if found:
                    break
                total_steps += batch

            if not found:
                raise RuntimeError(
                    f"encode timeout at phase {i + 1} code={code}"
                )

            rot_delta, ctr_delta = self._analytical_phase_deltas(
                phase_turns, i
            )
            self.rotation = (phase_rot_start + rot_delta) % (2.0 * math.pi)
            self.counter_rotation = (phase_ctr_start + ctr_delta) % (
                2.0 * math.pi
            )

            th = self.theta_for_code(code)
            if th is not None:
                self.snap_tracer_to_theta(th)
            self.snap_reader_to_code(code, glyph_theta=th)
            turns.append(phase_turns)

            did_reset = self._phase_transition(code, i, len(codes), th)
            phase_rot_start = self.rotation
            phase_ctr_start = self.counter_rotation

            logs.append(
                {
                    "phase": i + 1,
                    "target_code": code,
                    "direction": direction,
                    "turns": phase_turns,
                    "reader_arc": self.reader_arc,
                    "did_reset": did_reset,
                }
            )
        return turns, logs

    # ---------------------------------------------------------------
    # Decode: direct analytical motion + reader_code
    # ---------------------------------------------------------------
    def decode(
        self, turns: list[float]
    ) -> tuple[str, list[dict[str, Any]]]:
        out: list[str] = []
        logs: list[dict[str, Any]] = []
        self.reset_reader()
        phase_rot_start = self.rotation
        phase_ctr_start = self.counter_rotation

        for i, t in enumerate(turns):
            direction = direction_for_index_mode(
                i, self.runtime.direction_mode
            )
            sign = 1.0 if direction == "CCW" else -1.0
            delta = sign * float(t) * 2.0 * math.pi
            self.apply_knob_delta(delta, i)

            rot_delta, ctr_delta = self._analytical_phase_deltas(
                float(t), i
            )
            self.rotation = (phase_rot_start + rot_delta) % (2.0 * math.pi)
            self.counter_rotation = (phase_ctr_start + ctr_delta) % (
                2.0 * math.pi
            )

            code = self.reader_code()
            if 0 <= code <= 255:
                out.append(chr(code))
            else:
                out.append("?")

            th = self.theta_for_code(code)
            if th is not None:
                self.snap_tracer_to_theta(th)
            self.snap_reader_to_code(code, glyph_theta=th)

            did_reset = self._phase_transition(code, i, len(turns), th)
            phase_rot_start = self.rotation
            phase_ctr_start = self.counter_rotation

            logs.append(
                {
                    "phase": i + 1,
                    "decoded_code": code,
                    "direction": direction,
                    "turns": t,
                    "reader_arc": self.reader_arc,
                    "did_reset": did_reset,
                }
            )
        return "".join(out), logs


# ---------------------------------------------------------------------------
# Key generation
# ---------------------------------------------------------------------------
class KeyGenerator:
    """Produces randomized ScrollCipher keys."""

    def __init__(self, rng: np.random.Generator | None = None) -> None:
        self.rng = rng if rng is not None else np.random.default_rng()

    def generate(
        self, ascii_count: int = 128, pi_spacing: bool = True
    ) -> tuple[np.ndarray, SpiralParams, RuntimeConfig]:
        base_pts, params = generate_valid_spiral(rng=self.rng)
        glyph_order = self.rng.permutation(ascii_count).astype(int).tolist()
        rand_units = float(self.rng.integers(1, 100)) / 10.0
        rand_rad = float(self.rng.integers(1, 100)) / 10.0
        rand_ascii_rad = float(self.rng.integers(1, 100)) / 10.0
        rand_spacing_digit = int(self.rng.integers(0, 10))
        rand_spacing = (float(rand_spacing_digit) + 1.0) / 20.0
        pi_offset = int(self.rng.integers(0, 100_000)) if pi_spacing else -1
        runtime = RuntimeConfig(
            units_turn=rand_units,
            rad_turn=rand_rad,
            ascii_rad_turn=rand_ascii_rad,
            node_spacing=rand_spacing,
            direction_mode=int(self.rng.integers(0, 10)),
            latch_mode=int(self.rng.integers(0, 10)),
            rewrap_reset_mode=int(self.rng.integers(0, 10)),
            ascii_count=ascii_count,
            glyph_order=glyph_order,
            pi_offset=pi_offset,
        )
        return base_pts, params, runtime


# ---------------------------------------------------------------------------
# Key serialization / deserialization
# ---------------------------------------------------------------------------
def serialize_key(
    params: SpiralParams, runtime: RuntimeConfig, engine: Engine
) -> dict[str, Any]:
    return {
        "version": 1,
        "created_at": datetime.now().isoformat(),
        "spiral_params": {
            "c1": params.c1,
            "c2": params.c2,
            "c3": params.c3,
            "c4": params.c4,
            "c5": params.c5,
            "n_turns": params.n_turns,
            "orbital_radius": params.orbital_radius,
            "d": params.d,
            "u_min": params.u_min,
            "u_max": params.u_max,
        },
            "runtime": {
                "units_turn": runtime.units_turn,
                "rad_turn": runtime.rad_turn,
                "ascii_rad_turn": runtime.ascii_rad_turn,
                "node_spacing": runtime.node_spacing,
                "direction_mode": runtime.direction_mode,
                "latch_mode": runtime.latch_mode,
                "rewrap_reset_mode": runtime.rewrap_reset_mode,
                "ascii_count": runtime.ascii_count,
                "glyph_order": runtime.glyph_order,
                "pi_offset": runtime.pi_offset,
            },
        "state": {
            "rotation": engine.rotation,
            "counter_rotation": engine.counter_rotation,
            "anchor_base_theta": engine.anchor_base_theta,
            "s_pos": engine.s_pos,
            "knob_angle": math.pi / 2.0,
        },
    }


def save_key(key: dict[str, Any], path: Path) -> None:
    path.write_text(json.dumps(key, indent=2), encoding="utf-8")


def load_key(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def save_turns(turns: list[float], path: Path) -> None:
    with path.open("w", encoding="utf-8") as f:
        f.write("turns\n")
        for t in turns:
            f.write(f"{float(t):.17g}\n")


def load_turns(path: Path) -> list[float]:
    turns: list[float] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if line == "" or line.lower() == "turns":
            continue
        turns.append(float(line))
    return turns


def engine_from_key(key: dict[str, Any]) -> Engine:
    """Reconstruct an Engine from a serialized key dict."""
    sp = key["spiral_params"]
    params = SpiralParams(
        c1=float(sp["c1"]),
        c2=float(sp["c2"]),
        c3=float(sp["c3"]),
        c4=float(sp["c4"]),
        c5=float(sp["c5"]),
        n_turns=float(sp["n_turns"]),
        orbital_radius=float(sp["orbital_radius"]),
        d=float(sp["d"]),
        u_min=float(sp["u_min"]),
        u_max=float(sp["u_max"]),
    )
    pts = try_build_aligned_spiral(params)
    if pts is None:
        raise RuntimeError("Could not rebuild spiral from key params")
    rt = key["runtime"]
    runtime = RuntimeConfig(
        units_turn=float(rt["units_turn"]),
        rad_turn=float(rt["rad_turn"]),
        ascii_rad_turn=float(rt["ascii_rad_turn"]),
        node_spacing=float(rt["node_spacing"]),
        direction_mode=int(rt["direction_mode"]),
        latch_mode=int(rt["latch_mode"]),
        rewrap_reset_mode=int(rt["rewrap_reset_mode"]),
        ascii_count=int(rt.get("ascii_count", 128)),
        glyph_order=list(rt.get("glyph_order", [])),
        pi_offset=int(rt.get("pi_offset", -1)),
    )
    eng = Engine(pts, params, runtime)
    st = key["state"]
    eng.rotation = float(st["rotation"])
    eng.counter_rotation = float(st["counter_rotation"])
    eng.anchor_base_theta = float(st["anchor_base_theta"])
    eng.s_pos = float(st["s_pos"])
    eng.reset_reader()
    return eng
