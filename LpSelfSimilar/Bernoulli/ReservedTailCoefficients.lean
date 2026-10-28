module

public import LpSelfSimilar.Bernoulli.ReservedTailAngles
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

/-!
# Summable coefficients of the actual reserved tail

The selected tail has geometric coefficients `theta^(ell+j)/r`. Their exact sum
and the logarithmic-gap comparison give the strict bound `2/chi` required for
the tail's first two derivative estimates.
-/

open LpSelfSimilar.Analysis

namespace LpSelfSimilar.Bernoulli

/-- The rescaled coefficients of any contracting geometric tail have their exact sum. -/
theorem hasSum_tail_coefficients {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (ell : ℕ) (r : ℝ) :
    HasSum (fun j : ℕ ↦ θ ^ (ell + j) / r) ((θ ^ ell / r) / (1 - θ)) := by
  have hs := (hasSum_geometric_of_lt_one hθ0 hθ1).mul_left (θ ^ ell / r)
  have he : (fun j : ℕ ↦ θ ^ (ell + j) / r) = (fun j : ℕ ↦ (θ ^ ell / r) * θ ^ j) := by
    funext j
    rw [pow_add]
    ring
  rw [he]
  simpa only [div_eq_mul_inv] using hs

/-- The actual selected tail has rescaled coefficient sum strictly below `2/chi`. -/
theorem reservedTailStart_coefficient_sum_lt {θ ε r : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hgap : -Real.log θ ≤ 1 / 250) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 100000)
    (hr : 0 < r) (hrχ : r ≤ -Real.log θ) :
    (∑' j : ℕ, θ ^ (reservedTailStart θ ε r + j) / r) < 2 / (-Real.log θ) := by
  rw [(hasSum_tail_coefficients hθ0.le hθ1 (reservedTailStart θ ε r) r).tsum_eq]
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  have hq := (reservedTailStart_angle_bounds hθ0 hθ1 hgap hε0 hε hr hrχ 1 (by simpa)).2
  simp only [abs_one, one_mul] at hq
  have hm := mul_lt_mul_of_pos_right hq hχ
  have ht := mul_le_mul_of_nonneg_right (reserved_tail_parameter_lower hθ0 hgap) hχ.le
  have hlin := parameter_mul_log_gap_le hθ0
  apply (div_lt_iff₀ (sub_pos.mpr hθ1)).mpr
  rw [div_mul_eq_mul_div]
  apply (lt_div_iff₀ hχ).mpr
  nlinarith

end LpSelfSimilar.Bernoulli
