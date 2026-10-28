module

public import LpSelfSimilar.Bernoulli.PackingLengths
public import Mathlib.Analysis.SpecialFunctions.Log.PosLog

@[expose] public section

/-!
# The packing scales lie below the logarithmic gap

The defining base length is more than sufficient to force the spatial scale
2^(-R) below chi for every R at or above the packing threshold. This derives
the range needed by the reserved-tail construction instead of assuming it.
-/

namespace LpSelfSimilar.Bernoulli

/-- A simple explicit large logarithmic scale makes its dyadic spatial scale at most chi. -/
theorem dyadic_scale_le_of_two_le_gap_mul {χ R : ℝ} (hχ : 0 < χ) (hR : 2 ≤ χ * R) :
    (2 : ℝ) ^ (-R) ≤ χ := by
  have hRpos : 0 < R := by nlinarith
  have hl : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_left hl (mul_nonneg hχ.le hRpos.le)
  have hg : 1 ≤ χ * (R * Real.log 2) := by nlinarith
  have he := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (R * Real.log 2)) hχ.le
  have hh : 1 ≤ χ * Real.exp (R * Real.log 2) := by nlinarith
  have heq : (2 : ℝ) ^ (-R) = (Real.exp (R * Real.log 2))⁻¹ := by
    rw [Real.rpow_def_of_pos (by norm_num), ← Real.exp_neg]
    congr 1
    ring
  rw [heq]
  apply (mul_le_mul_iff_right₀ (Real.exp_pos (R * Real.log 2))).mp
  rw [mul_inv_cancel₀ (Real.exp_ne_zero _)]
  simpa only [mul_comm] using hh

/-- All packing scales automatically lie in the range required by the reserved tail. -/
theorem dyadic_scale_le_gap_of_packing_threshold {χ ρ L R : ℝ}
    (hχ : 0 < χ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L)
    (hR : packingScaleThreshold χ ρ L ≤ R) : (2 : ℝ) ^ (-R) ≤ χ := by
  have hJ := LpSelfSimilar.Entropy.three_le_separation_entropy_ratio hρ hρ1 hL
  have ht := six_lt_packingLogScale hJ
  have hbase := (div_le_iff₀ hχ).mp (packingBaseLength_lower_bound χ (L / ρ))
  have hprod : 18 ≤ (L / ρ) * packingLogScale (L / ρ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hJ) (sub_nonneg.mpr ht.le)]
  have hn : 2 ≤ χ * (packingBaseLength χ (L / ρ) : ℝ) := by nlinarith
  have hnR : (packingBaseLength χ (L / ρ) : ℝ) ≤ R := by
    have hnonneg : (0 : ℝ) ≤ packingBaseLength χ (L / ρ) := by positivity
    have he : (packingBaseLength χ (L / ρ) : ℝ) ≤ packingScaleThreshold χ ρ L := by
      unfold packingScaleThreshold
      nlinarith
    exact he.trans hR
  exact dyadic_scale_le_of_two_le_gap_mul hχ
    (hn.trans (mul_le_mul_of_nonneg_left hnR hχ.le))

end LpSelfSimilar.Bernoulli
