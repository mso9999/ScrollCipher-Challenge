# ScrollCipher Cryptanalysis Challenge

**ScrollCipher** is an experimental geometric stream cipher that maps
plaintext symbols onto glyph nodes arranged along a wound line on a unit
circle and uses coupled rotational motion along a parametric scroll machine
spiral to generate real-valued ciphertext. Each plaintext character produces
a fractional turn count; decryption replays the turn sequence to recover the
original text.

This repository contains the reference implementation, test vectors, and
three cryptanalysis challenge instances of increasing difficulty. We invite
the cryptographic community to attempt key recovery or plaintext recovery.

> **Paper:** M. S. Orosz, "ScrollCipher: A Geometric Stream Cipher with
> Continuous-State Keying on Scroll Machine Curves," March 2026.

## Quick Start

```bash
pip install -r requirements.txt
python scrollcipher_engine.py          # runs built-in self-test
```

Verify your setup with the included test vectors:

```python
import json
from scrollcipher_engine import engine_from_key

with open("test_vectors.json") as f:
    vectors = json.load(f)

for v in vectors:
    eng = engine_from_key(v["key"])
    decoded, _ = eng.decode(v["turns"])
    assert decoded == v["plaintext"], f"FAIL: {v['name']}"
    print(f"  PASS: {v['name']}")
```

## Challenge Instances

### Level 1 — Easy (Permutation Recovery)

**File:** `challenge_level1.json`

Recover the 128-element glyph permutation σ given:
- All other key parameters (spiral coefficients, rates, modes, pi-offset)
- The ciphertext (5 turn values)
- The plaintext length (5 characters)

**Hint:** The plaintext is a common English greeting in uppercase.

### Level 2 — Medium (Full Key + Plaintext Recovery)

**File:** `challenge_level2.json`

Recover the key and plaintext given:
- The ciphertext only (20 turn values)
- The plaintext length (20 characters)

**Known:** alphabet size = 128, pi-offset differential spacing is enabled.

### Level 3 — Hard (Full Key + Plaintext Recovery, No Hints)

**File:** `challenge_level3.json`

Recover the key and plaintext given:
- The ciphertext only (100 turn values)
- The plaintext length (100 characters)
- No hints.

## How the Cipher Works

1. A **scroll machine spiral** (parameterised by coefficients c₂…c₅ and
   turn count N) is generated and normalised to fit within the unit circle.
2. A **wound glyph line** wraps 128 ASCII characters around the unit circle
   with per-node spacing derived from digits of π starting at offset O.
3. A **tracer** moves along the spiral while the spiral frame **rotates**
   and the glyph anchor **counter-rotates**. The relative angle between
   the tracer's radial projection and the glyph anchor determines which
   character the reader is pointing at.
4. For each plaintext character, the system advances until the reader
   crosses the target glyph. The number of knob turns required is the
   **ciphertext** — a real number.
5. After each character, the pi-offset advances by the character's ASCII
   code, completely reconfiguring all glyph positions (cipher feedback).

## Key Space

The discrete key space alone has ~10²²³ configurations (~743 bits):
- Glyph permutation: 128! ≈ 10²¹⁵
- Pi-digit offset: O ∈ {0, …, 10⁵}
- Direction, latch, rewrap modes: 10³ combinations

Plus 13 continuous real-valued parameters (spiral geometry, rates, initial
state) contributing additional entropy bounded by machine precision.

## Reporting Results

If you successfully recover a key or plaintext from any challenge instance,
please open an issue in this repository describing your approach. We are
particularly interested in:
- The computational cost of your attack
- Whether it generalises beyond the specific challenge instance
- Any structural weaknesses identified in the cipher

## Formal Verification (Lean 4)

Key security lemmas from the paper have been formally verified in the
Lean 4 proof assistant with Mathlib. See [`lean4-proofs/`](lean4-proofs/)
for proof scripts and build instructions. Verified results include:
- Markov mixing convergence bounds (Proposition 1)
- Correctness under bounded precision (Theorem 2)
- IND-CPA game-hopping advantage bound (Theorem 1)

## Files

| File | Description |
|------|-------------|
| `scrollcipher_engine.py` | Reference Python implementation (encode, decode, key generation) |
| `test_vectors.json` | 6 test vectors with keys, plaintexts, and turn values |
| `challenge_level1.json` | Level 1 challenge (easy — permutation recovery) |
| `challenge_level2.json` | Level 2 challenge (medium — full recovery, 20 chars) |
| `challenge_level3.json` | Level 3 challenge (hard — full recovery, 100 chars) |
| `lean4-proofs/` | Lean 4 formal verification of key lemmas |
| `requirements.txt` | Python dependencies |

## License

MIT — see [LICENSE](LICENSE).
