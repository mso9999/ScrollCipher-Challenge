/-
  ScrollCipher: Formal verification of the correctness theorem.

  Corresponds to Theorem 2 in the paper.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Real

noncomputable section

/-- Minimum inter-glyph angular spacing under pi-offset differential spacing. -/
def δ_min : ℝ := 0.05

/-- Maximum turn value magnitude (empirical bound). -/
def max_turn : ℝ := 10

/-- The precision error when storing a turn value t with p significant
    decimal figures: |error| ≤ |t| × 10^(1-p). -/
def precisionError (t : ℝ) (p : ℕ) : ℝ := |t| * (10 : ℝ) ^ (1 - (p : ℤ))

/-- Precision error is non-negative. -/
theorem precisionError_nonneg (t : ℝ) (p : ℕ) : 0 ≤ precisionError t p := by
  unfold precisionError
  apply mul_nonneg (abs_nonneg t)
  positivity

/-- For |t| < max_turn, the precision error is bounded by 10^(2-p). -/
theorem precisionError_bound (t : ℝ) (p : ℕ) (ht : |t| < max_turn) :
    precisionError t p < (10 : ℝ) ^ (2 - (p : ℤ)) := by
  unfold precisionError max_turn at *
  have h10 : (0 : ℝ) < (10 : ℝ) ^ (1 - (p : ℤ)) := by positivity
  calc |t| * (10 : ℝ) ^ (1 - (p : ℤ))
      < 10 * (10 : ℝ) ^ (1 - (p : ℤ)) := by
        exact mul_lt_mul_of_pos_right ht h10
    _ = (10 : ℝ) ^ (2 - (p : ℤ)) := by
        have : (10 : ℝ) ≠ 0 := by norm_num
        rw [show (2 : ℤ) - (p : ℤ) = 1 + (1 - (p : ℤ)) from by ring]
        rw [zpow_add₀ this, zpow_one]

/-- The nearest-glyph lookup succeeds when the reader arc error is
    less than half the minimum inter-glyph spacing. -/
def lookupSucceeds (error : ℝ) : Prop := error < δ_min / 2

/-- Half of δ_min equals 0.025. -/
theorem half_δ_min : δ_min / 2 = 0.025 := by unfold δ_min; norm_num

/-- Sufficient condition: 10^(2-p) < δ_min/2 implies lookup success. -/
theorem precision_sufficient (p : ℕ)
    (hp : (10 : ℝ) ^ (2 - (p : ℤ)) < δ_min / 2)
    (t : ℝ) (ht : |t| < max_turn) :
    lookupSucceeds (precisionError t p) := by
  unfold lookupSucceeds
  exact lt_trans (precisionError_bound t p ht) hp

/-- At p = 4: 10^(-2) = 0.01 < 0.025. Theoretical minimum. -/
theorem four_sigfigs_sufficient :
    (10 : ℝ) ^ (2 - (4 : ℤ)) < δ_min / 2 := by
  unfold δ_min; norm_num

/-- At p = 7 (empirical threshold): 10^(-5) < 0.025. -/
theorem seven_sigfigs_sufficient :
    (10 : ℝ) ^ (2 - (7 : ℤ)) < δ_min / 2 := by
  unfold δ_min; norm_num

/-- At p = 17 (IEEE 754 double): 10^(-15) < 0.025. -/
theorem double_precision_sufficient :
    (10 : ℝ) ^ (2 - (17 : ℤ)) < δ_min / 2 := by
  unfold δ_min; norm_num

/-- Phase state: the 4-tuple that evolves during encryption. -/
structure PhaseState where
  s_pos : ℝ
  θ_rot : ℝ
  θ_ctr : ℝ
  pi_offset : ℕ
  deriving DecidableEq

/-- The analytical override recomputes rotation angles from the
    exact turn count, eliminating micro-step drift. -/
def analyticalOverride (state : PhaseState) (turn ρ α : ℝ) : PhaseState where
  s_pos := state.s_pos
  θ_rot := state.θ_rot + turn * ρ
  θ_ctr := state.θ_ctr - turn * α
  pi_offset := state.pi_offset

/-- Phase transition advances the pi-offset by the character code. -/
def phaseTransition (state : PhaseState) (charCode : ℕ) : PhaseState where
  s_pos := state.s_pos
  θ_rot := state.θ_rot
  θ_ctr := state.θ_ctr
  pi_offset := state.pi_offset + charCode

/-- If encoder and decoder start in the same state and use the same
    turn value, their post-phase states are identical. -/
theorem phase_correctness
    (enc_state dec_state : PhaseState)
    (h_same : enc_state = dec_state)
    (turn ρ α : ℝ) (charCode : ℕ) :
    phaseTransition (analyticalOverride enc_state turn ρ α) charCode =
    phaseTransition (analyticalOverride dec_state turn ρ α) charCode := by
  subst h_same; rfl

/-- Inductive correctness: if initial states match and every phase
    preserves state equality, then all states are equal. -/
theorem inductive_correctness
    (n : ℕ) (states_enc states_dec : Fin (n + 1) → PhaseState)
    (h_init : states_enc 0 = states_dec 0)
    (h_step : ∀ i : Fin n,
      states_enc i.castSucc = states_dec i.castSucc →
      states_enc i.succ = states_dec i.succ) :
    ∀ k : ℕ, (hk : k < n + 1) → states_enc ⟨k, hk⟩ = states_dec ⟨k, hk⟩ := by
  intro k
  induction k with
  | zero => intro _; exact h_init
  | succ k ih =>
    intro hk
    have hk' : k < n := Nat.lt_of_succ_lt_succ hk
    have hkn : k < n + 1 := Nat.lt_of_lt_of_le hk' (Nat.le_succ n)
    exact h_step ⟨k, hk'⟩ (ih hkn)

end
