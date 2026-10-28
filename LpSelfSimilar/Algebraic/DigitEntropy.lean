module

public import LpSelfSimilar.Algebraic.SparseDigitInjectivity
public import LpSelfSimilar.Algebraic.UnitDigits
public import LpSelfSimilar.Bernoulli.SparseEntropy

@[expose] public section

/-!
The full algebraic entropy input of revised Lemma 3.6, with exact constant 8.

Nonunits have the preserved exact digit entropy n log(2). For units, an actual
expanding conjugate supplies spacing k<=2B with injective sparse digits, and the
proved uniform-subset atom bound gives n/(8B). This elementary degree-dependent
argument replaces the stronger Breuillard–Varju Gaussian entropy-rate input for
the precise bound required here. No entropy estimate, Gaussian identity, matrix
construction, absolute continuity or distinctness of full words is assumed.
-/

open LpSelfSimilar.Bernoulli LpSelfSimilar.Entropy

namespace LpSelfSimilar.Algebraic

/-- The entropy assertion of revised (3.8), for the actual finite fair-sign law
and canonical complexity. Includes algebraic units and all finite word lengths. -/
theorem digit_entropy_ge_length_div_eight_complexity {r : ℝ} (hr : IsAlgebraic ℚ r)
    (hr0 : 0 < r) (hr1 : r < 1) (n : ℕ) :
    (n : ℝ) / (8 * complexity r) ≤
      finiteEntropy (digitPMF r n) (digitPMF_support_finite _ _) := by
  have hB := complexity_pos hr hr0 hr1
  by_cases hu : IsAlgebraicUnit r
  · obtain ⟨k, hk, hkB, hinj⟩ := exists_sparse_digit_spacing hu.2.1 hr0 hr1
    exact digit_entropy_ge_div_eight_of_sparse_injectivity hB hk hkB hinj n
  · rw [digit_entropy_of_not_isAlgebraicUnit hr0.ne' hu]
    have hB3 := three_le_complexity hr hr0 hr1
    have hlog : (1 : ℝ) / 2 ≤ Real.log 2 := by
      have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h
      exact h
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    apply (div_le_iff₀ (by positivity : 0 < 8 * complexity r)).mpr
    have h1 : (1 : ℝ) ≤ Real.log 2 * (8 * complexity r) := by nlinarith
    have h := mul_le_mul_of_nonneg_left h1 hn
    nlinarith

end LpSelfSimilar.Algebraic
