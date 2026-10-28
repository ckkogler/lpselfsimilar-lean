module

public import LpSelfSimilar.Gaussian.Kernel
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

@[expose] public section

/-!
Third absolute moments of centered Gaussian laws, including variance zero.
Scaling reduces every moment to one fixed finite unit-variance moment; this
supplies an absolute constant for Gaussian replacement of bounded summands.
-/

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

namespace LpSelfSimilar.Gaussian

lemma integrable_gaussian_abs_pow (v : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ ↦ |x| ^ n) (gaussianReal 0 v) := by
  have h : MemLp (id : ℝ → ℝ) (n : ℝ≥0∞) (gaussianReal 0 v) :=
    memLp_id_gaussianReal' _ (by simp)
  simpa only [Real.norm_eq_abs, id_eq] using h.integrable_norm_pow'

noncomputable def unitThirdMoment : ℝ := ∫ x : ℝ, |x| ^ 3 ∂gaussianReal 0 1

lemma unitThirdMoment_nonneg : 0 ≤ unitThirdMoment := integral_nonneg (fun _ ↦ by positivity)

lemma gaussian_eq_map_scaled_unit (v : ℝ≥0) :
    gaussianReal 0 v = (gaussianReal 0 1).map (fun x ↦ Real.sqrt (v : ℝ) * x) := by
  rw [gaussianReal_map_const_mul, mul_zero]
  congr 1
  ext
  simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one, mul_one]
  exact (Real.sq_sqrt v.coe_nonneg).symm

lemma gaussian_thirdMoment (v : ℝ≥0) :
    (∫ x : ℝ, |x| ^ 3 ∂gaussianReal 0 v) = Real.sqrt (v : ℝ) ^ 3 * unitThirdMoment := by
  rw [gaussian_eq_map_scaled_unit v, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [abs_mul, mul_pow, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [integral_const_mul]
  rfl

lemma gaussian_thirdMoment_le {v : ℝ≥0} {R : ℝ} (hR : 0 ≤ R) (hv : (v : ℝ) ≤ R ^ 2) :
    (∫ x : ℝ, |x| ^ 3 ∂gaussianReal 0 v) ≤ unitThirdMoment * R * (v : ℝ) := by
  rw [gaussian_thirdMoment]
  have hs : Real.sqrt (v : ℝ) ≤ R := (Real.sqrt_le_iff).mpr ⟨hR, hv⟩
  have he : Real.sqrt (v : ℝ) ^ 3 = (v : ℝ) * Real.sqrt (v : ℝ) := by
    rw [pow_succ, Real.sq_sqrt v.coe_nonneg]
  rw [he]
  have h := mul_le_mul_of_nonneg_left hs
    (mul_nonneg unitThirdMoment_nonneg v.coe_nonneg)
  nlinarith

end LpSelfSimilar.Gaussian
