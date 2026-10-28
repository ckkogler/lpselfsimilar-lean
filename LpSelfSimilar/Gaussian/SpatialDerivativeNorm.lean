module

public import LpSelfSimilar.Gaussian.SpatialDerivatives
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

@[expose] public section

/-!
Exact scaling of the L1 norm of the third spatial derivative of the first
variance derivative. The resulting `y^(-5/2)` estimate has one absolute constant.
-/

open MeasureTheory Real

namespace LpSelfSimilar.Gaussian

noncomputable def thirdSpatialNorm : ℝ := ∫ x, |thirdSpatialKernel 1 x|

lemma thirdSpatialNorm_nonneg : 0 ≤ thirdSpatialNorm := integral_nonneg (fun _ ↦ abs_nonneg _)

lemma thirdSpatialKernel_scale {y : ℝ} (hy : 0 < y) (x : ℝ) :
    thirdSpatialKernel y x = y⁻¹ ^ 3 * thirdSpatialKernel 1 (x / Real.sqrt y) := by
  have hs := Real.sqrt_pos.mpr hy
  have hsq := Real.sq_sqrt hy.le
  unfold thirdSpatialKernel
  rw [kernel_scale hy]
  simp only [one_pow, mul_one]
  generalize hz : Real.sqrt y = z at *
  simp only [← hsq]
  field_simp
  <;> ring

lemma integral_abs_thirdSpatialKernel {y : ℝ} (hy : 0 < y) :
    (∫ x, |thirdSpatialKernel y x|) = y⁻¹ ^ 2 / Real.sqrt y * thirdSpatialNorm := by
  have hs := Real.sqrt_pos.mpr hy
  have hsq := Real.sq_sqrt hy.le
  simp_rw [thirdSpatialKernel_scale hy, abs_mul,
    abs_of_pos (pow_pos (inv_pos.mpr hy) 3)]
  rw [integral_const_mul, Measure.integral_comp_div (fun x ↦ |thirdSpatialKernel 1 x|),
    abs_of_pos hs, smul_eq_mul]
  unfold thirdSpatialNorm
  field_simp
  rw [hsq]

end LpSelfSimilar.Gaussian
