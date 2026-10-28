module

public import LpSelfSimilar.Bernoulli.DetailSmoothingEstimate
public import Mathlib.MeasureTheory.Function.Floor

@[expose] public section

/-!
# Measurability and scale extent of the smoothing length count

Each count fiber lies in an interval starting at zero and ending at R0*N^T.
This upper volume bound suffices for summing the detail estimate, and includes
the tail-only fiber T=0. The upper endpoint is strict even at exact powers.
-/

open MeasureTheory LpSelfSimilar.Analysis LpSelfSimilar.Entropy

namespace LpSelfSimilar.Bernoulli

/-- The actual zero-extended logarithmic count is measurable for all numerical parameters. -/
theorem measurable_smoothingLengthCount (χ ρ L : ℝ) :
    Measurable (smoothingLengthCount χ ρ L) := by
  unfold smoothingLengthCount packingLengthCount geometricLengthCount
  apply Measurable.ite (by measurability)
  · fun_prop
  · fun_prop

/-- Every scale is strictly below the upper endpoint associated with its actual count. -/
theorem lt_threshold_mul_pow_smoothingLengthCount {χ ρ L : ℝ}
    (hχ : 0 < χ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L) (R : ℝ) :
    R < packingScaleThreshold χ ρ L *
      (packingLengthMultiplier (L / ρ) : ℝ) ^ smoothingLengthCount χ ρ L R := by
  have hA := packingScaleThreshold_pos hχ hρ hρ1 hL
  by_cases hR : packingScaleThreshold χ ρ L ≤ R
  · have hN := twenty_seven_le_packingLengthMultiplier
      (three_le_separation_entropy_ratio hρ hρ1 hL)
    have hN1 : (1 : ℝ) < packingLengthMultiplier (L / ρ) := by
      exact_mod_cast (show 1 < packingLengthMultiplier (L / ρ) by omega)
    have hh := ratio_lt_pow_geometricLengthCount hN1 ((one_le_div hA).mpr hR)
    rw [smoothingLengthCount_of_le hR, packingLengthCount]
    exact (div_lt_iff₀ hA).mp hh |>.trans_eq (mul_comm _ _)
  · rw [smoothingLengthCount_of_lt (lt_of_not_ge hR), pow_zero, mul_one]
    exact lt_of_not_ge hR

end LpSelfSimilar.Bernoulli
