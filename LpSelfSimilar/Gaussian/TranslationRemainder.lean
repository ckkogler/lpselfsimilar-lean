module

public import LpSelfSimilar.Gaussian.SpatialDerivativeNorm
public import LpSelfSimilar.Analysis.TranslationTaylor

@[expose] public section

/-!
The Gaussian L1 Taylor remainder used by the Lindeberg replacement proof of
Lemma 3.2. Its constant is the single unit-variance third spatial derivative
norm, and the variance scaling is exactly `y^(-5/2)`.
-/

open MeasureTheory Real

namespace LpSelfSimilar.Gaussian

lemma integral_abs_firstKernel_translationRemainder_le {y : ℝ} (hy : 0 < y) (u : ℝ) :
    (∫ x, |translationRemainder (firstKernel y) u x|) ≤
      |u| ^ 3 / 6 * (y⁻¹ ^ 2 / Real.sqrt y * thirdSpatialNorm) := by
  have hD : Integrable (iteratedDeriv 3 (firstKernel y)) volume := by
    rw [iteratedDeriv_firstKernel_three hy]
    exact integrable_thirdSpatialKernel hy
  have h := integral_abs_translationRemainder_le
    ((contDiff_firstKernel y).of_le (by simp)) hD u
  rw [iteratedDeriv_firstKernel_three hy, integral_abs_thirdSpatialKernel hy] at h
  exact h

end LpSelfSimilar.Gaussian
