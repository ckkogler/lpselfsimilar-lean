module

public import LpSelfSimilar.Geometry.PositiveAffine

@[expose] public section

/-!
# Transporting a coarse small-set bound through a positive affine map

The Lebesgue Jacobian changes the height constant by the reciprocal scale;
the additive mass error is unchanged. This allows the original Gaussian
approximation to be used without separately transporting an L1 norm.
-/

open MeasureTheory Set
open LpSelfSimilar.Geometry
open scoped ENNReal

namespace LpSelfSimilar.Analysis

/-- The exact reciprocal-scale height in a pushed-forward small-set estimate. -/
theorem positiveAffine_map_small_set_bound (q : PositiveAffine) (μ : Measure ℝ)
    {C K e : ℝ} (hC : 0 ≤ C) (hK : C * q.scale⁻¹ ≤ K)
    (hbound : ∀ E : Set ℝ, MeasurableSet E →
      μ E ≤ ENNReal.ofReal C * volume E + ENNReal.ofReal e)
    {E : Set ℝ} (hE : MeasurableSet E) :
    μ.map q E ≤ ENNReal.ofReal K * volume E + ENNReal.ofReal e := by
  rw [Measure.map_apply q.measurable hE]
  calc
    _ ≤ ENNReal.ofReal C * volume (q ⁻¹' E) + ENNReal.ofReal e := hbound _ (hE.preimage q.measurable)
    _ = ENNReal.ofReal (C * q.scale⁻¹) * volume E + ENNReal.ofReal e := by
      rw [q.volume_preimage, ← mul_assoc, ← ENNReal.ofReal_mul hC]
    _ ≤ _ := add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal hK) le_rfl) le_rfl

end LpSelfSimilar.Analysis
