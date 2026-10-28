module

public import LpSelfSimilar.Gaussian.Kernel
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

@[expose] public section

/-!
The normalization of Gaussian detail. Its definition is exactly the inverse
L1 norm used in Section 3. Scaling is proved by a real change of variables,
and strict positivity follows from continuity and the value at the origin.
-/

open MeasureTheory Real

namespace LpSelfSimilar.Gaussian

/-- The L1 norm of the first variance derivative at variance one. -/
noncomputable def firstNorm : ℝ := ∫ x, |firstKernel 1 x|

lemma firstNorm_pos : 0 < firstNorm := by
  apply integral_pos_of_integrable_nonneg_nonzero
    (continuous_firstKernel 1).abs (integrable_firstKernel (by norm_num)).abs
    (fun x ↦ abs_nonneg _) (x := 0)
  have hk := kernel_pos (by norm_num : (0 : ℝ) < 1) 0
  rw [abs_ne_zero]
  norm_num only [firstKernel, zero_pow (by decide : 2 ≠ 0), one_pow, zero_sub, mul_one]
  exact mul_ne_zero (by norm_num) hk.ne'

/-- The exact normalization `Q = ‖η₁⁽¹⁾‖₁⁻¹`. -/
noncomputable def detailNormalization : ℝ := firstNorm⁻¹

lemma detailNormalization_pos : 0 < detailNormalization := inv_pos.mpr firstNorm_pos

lemma integral_abs_firstKernel {y : ℝ} (hy : 0 < y) :
    (∫ x, |firstKernel y x|) = y⁻¹ * firstNorm := by
  have hs : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  simp_rw [firstKernel_scale hy, abs_mul, abs_of_pos (inv_pos.mpr hy),
    abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hy))]
  rw [integral_const_mul, Measure.integral_comp_div (fun x ↦ |firstKernel 1 x|),
    abs_of_pos (Real.sqrt_pos.mpr hy), smul_eq_mul]
  dsimp [firstNorm]
  field_simp

lemma detailNormalization_mul_firstNorm : detailNormalization * firstNorm = 1 :=
  inv_mul_cancel₀ firstNorm_pos.ne'

lemma normalized_firstKernel_norm {r : ℝ} (hr : 0 < r) :
    r ^ 2 * detailNormalization * (∫ x, |firstKernel (r ^ 2) x|) = 1 := by
  rw [integral_abs_firstKernel (by positivity)]
  calc
    r ^ 2 * detailNormalization * ((r ^ 2)⁻¹ * firstNorm) =
        (r ^ 2 * (r ^ 2)⁻¹) * (detailNormalization * firstNorm) := by ring
    _ = 1 := by rw [mul_inv_cancel₀ (by positivity), detailNormalization_mul_firstNorm, one_mul]

end LpSelfSimilar.Gaussian
