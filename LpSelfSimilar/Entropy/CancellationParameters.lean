module

public import LpSelfSimilar.Entropy.SixteenAtomCancellation

@[expose] public section

/-!
# Explicit entropy-cancellation parameters

For `J >= 3`, choose slope `log(150J)/((13/40)*log 2)` and remainder
`log(1+1/(10J))/log 2`. Their positivity, exact exponential identity and remainder
bound retain the constants used when integrating the conditional inequality.
-/

namespace LpSelfSimilar.Entropy

/-- Slope converting cancellation into entropy in bits. -/
noncomputable def cancellationSlope (J : ℝ) : ℝ :=
  Real.log (150 * J) / ((13 / 40 : ℝ) * Real.log 2)

/-- Exact remainder in the logarithmic specialization of the sixteen-atom bound. -/
noncomputable def cancellationRemainder (J : ℝ) : ℝ :=
  Real.log (1 + 1 / (10 * J)) / Real.log 2

theorem cancellationSlope_pos {J : ℝ} (hJ : 3 ≤ J) : 0 < cancellationSlope J := by
  have ht : 0 < Real.log (150 * J) := Real.log_pos (by linarith)
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold cancellationSlope
  positivity

/-- The sixteen-atom exponential remainder is exactly the chosen logarithmic remainder. -/
theorem cancellation_remainder_at_slope {J : ℝ} (hJ : 3 ≤ J) :
    Real.log (1 + 15 * (2 : ℝ) ^ (-cancellationSlope J * (13 / 40 : ℝ))) / Real.log 2 =
      cancellationRemainder J := by
  have hJ0 : 0 < J := by linarith
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have he : (2 : ℝ) ^ (-cancellationSlope J * (13 / 40 : ℝ)) = 1 / (150 * J) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hex : Real.log 2 * (-cancellationSlope J * (13 / 40 : ℝ)) =
        -Real.log (150 * J) := by
      unfold cancellationSlope
      field_simp
    rw [hex, Real.exp_neg, Real.exp_log (by positivity), one_div]
  have hcoeff : 15 * (1 / (150 * J)) = 1 / (10 * J) := by field_simp; ring
  rw [he, hcoeff]
  rfl

theorem cancellationRemainder_nonneg {J : ℝ} (hJ : 0 < J) : 0 ≤ cancellationRemainder J := by
  have harg : 1 ≤ 1 + 1 / (10 * J) := le_add_of_nonneg_right (by positivity)
  exact div_nonneg (Real.log_nonneg harg) (Real.log_nonneg (by norm_num))

/-- The exact elementary upper bound for the logarithmic remainder. -/
theorem cancellationRemainder_le {J : ℝ} (hJ : 0 < J) :
    cancellationRemainder J ≤ 1 / (10 * J * Real.log 2) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 1 / (10 * J))
  unfold cancellationRemainder
  apply (div_le_iff₀ hl).mpr
  have he : 1 / (10 * J * Real.log 2) * Real.log 2 = 1 / (10 * J) := by field_simp
  rw [he]
  linarith

end LpSelfSimilar.Entropy
