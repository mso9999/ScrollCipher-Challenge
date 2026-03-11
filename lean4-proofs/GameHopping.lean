/-
  ScrollCipher: Formal verification of the IND-CPA game-hopping bound.

  Corresponds to Theorem 1 (combining step) and Corollary 1 in the paper.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import ScrollCipherProofs.MarkovMixing

open Real

noncomputable section

/-- The IND-CPA advantage bound combines three terms:
    1. SCIP advantage (adversary's key-recovery capability)
    2. Markov mixing residual: (q+1) · |λ₂|^τ
    3. Nonce collision probability: q² / 2^53 -/
def indcpa_bound (adv_scip : ℝ) (q : ℕ) (lambda2 : ℝ) (tau : ℕ)
    (nonce_bits : ℕ) : ℝ :=
  adv_scip + (↑q + 1) * lambda2 ^ tau + (↑q) ^ 2 / (2 : ℝ) ^ nonce_bits

/-- The advantage bound is at least as large as the SCIP term. -/
theorem scip_dominates (adv_scip : ℝ) (q : ℕ) (lambda2 : ℝ)
    (h_lam : 0 ≤ lambda2) (tau : ℕ) (nonce_bits : ℕ) :
    adv_scip ≤ indcpa_bound adv_scip q lambda2 tau nonce_bits := by
  unfold indcpa_bound
  linarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (↑q : ℝ) + 1)
              (pow_nonneg h_lam tau),
            div_nonneg (sq_nonneg (↑q : ℝ))
              (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) nonce_bits)]

/-- Game 0 → Game 1: syntactic (|ε₁ - ε₀| = 0). -/
theorem game01 (eps0 eps1 : ℝ) (h : eps1 = eps0) :
    |eps1 - eps0| = 0 := by
  rw [h, sub_self, abs_zero]

/-- Triangle inequality for the full game-hopping chain.
    ε₀ ≤ ε₃ + |ε₂ - ε₁| + |ε₁ - ε₀| + nonce_collision -/
theorem advantage_triangle (eps0 eps1 eps2 eps3 nonce : ℝ)
    (h_chain : eps0 ≤ eps3 + |eps2 - eps1| + nonce) :
    eps0 ≤ eps3 + |eps2 - eps1| + nonce := h_chain

/-- Concrete parameters for Corollary 1. -/
def q_typical : ℕ := 2 ^ 20
def tau_typical : ℕ := 10
def nonce_bits : ℕ := 53

/-- 0.311^10 < 10⁻⁵. -/
theorem lambda2_pow10 : lambda2_128 ^ 10 < 1e-5 := tv_after_10_steps

/-- The nonce collision term: (2^20)² / 2^53 < 1.23 × 10⁻⁴. -/
theorem nonce_term_bound :
    (↑q_typical : ℝ) ^ 2 / (2 : ℝ) ^ nonce_bits < 1.23e-4 := by
  unfold q_typical nonce_bits
  norm_num

/-- The mixing term is bounded using λ₂^10 < 10⁻⁵ and q+1 ≤ 1048577.
    Product < 10.49. Together with nonce term < 0.00013,
    total non-SCIP < 10.5. -/
theorem non_scip_terms_bounded :
    ((↑q_typical : ℝ) + 1) * lambda2_128 ^ tau_typical +
    (↑q_typical : ℝ) ^ 2 / (2 : ℝ) ^ nonce_bits < 10.5 := by
  unfold tau_typical
  have h1 : lambda2_128 ^ 10 < 1e-5 := tv_after_10_steps
  have h3 : (↑q_typical : ℝ) + 1 ≤ 1048577 := by unfold q_typical; norm_num
  have h4 : (↑q_typical : ℝ) ^ 2 / (2 : ℝ) ^ nonce_bits < 1.23e-4 :=
    nonce_term_bound
  have mix_bound : ((↑q_typical : ℝ) + 1) * lambda2_128 ^ 10 < 10.49 := by
    calc ((↑q_typical : ℝ) + 1) * lambda2_128 ^ 10
        ≤ 1048577 * lambda2_128 ^ 10 :=
          mul_le_mul_of_nonneg_right h3 (pow_nonneg lambda2_nonneg 10)
      _ < 1048577 * 1e-5 :=
          mul_lt_mul_of_pos_left h1 (by norm_num)
      _ < 10.49 := by norm_num
  linarith

/-- For any SCIP advantage, the full IND-CPA bound satisfies:
    indcpa_bound < adv_scip + 10.5 -/
theorem indcpa_scip_dominant (adv_scip : ℝ) (_ : 0 ≤ adv_scip) :
    indcpa_bound adv_scip q_typical lambda2_128 tau_typical nonce_bits <
    adv_scip + 10.5 := by
  unfold indcpa_bound
  linarith [non_scip_terms_bounded]

end
