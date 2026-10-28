module

public import LpSelfSimilar.Gaussian.TranslationRemainder
public import LpSelfSimilar.Gaussian.AbsoluteMoments
public import LpSelfSimilar.Gaussian.Semigroup
public import LpSelfSimilar.Analysis.MomentMatching
public import LpSelfSimilar.Probability.BoundedMoments

@[expose] public section

/-!
One Lindeberg replacement step. A bounded centered summand is compared with the
centered Gaussian of the same second moment. All moment and integrability
conditions are derived from boundedness or the proved Gaussian moment formulas.
-/

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace LpSelfSimilar.Gaussian

noncomputable def replacementConstant : ℝ :=
  (1 + unitThirdMoment) * thirdSpatialNorm / 6

lemma replacementConstant_nonneg : 0 ≤ replacementConstant := by
  unfold replacementConstant
  positivity [unitThirdMoment_nonneg, thirdSpatialNorm_nonneg]

lemma integral_sq_gaussian (v : ℝ≥0) : (∫ u : ℝ, u ^ 2 ∂gaussianReal 0 v) = v := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral (X := fun u : ℝ ↦ u) (by fun_prop), integral_id_gaussianReal] at h
  simpa only [sub_zero] using h

/-- Quantitative error of replacing one bounded centered law by its Gaussian. -/
theorem firstSmooth_sub_gaussian_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {R y : ℝ} (hR : 0 ≤ R) (hy : 0 < y) (hb : ∀ᵐ u ∂μ, |u| ≤ R)
    (hm : (∫ u : ℝ, u ∂μ) = 0) (v : ℝ≥0)
    (hv : (∫ u : ℝ, u ^ 2 ∂μ) = v) :
    (∫ x, |firstSmooth μ y x - firstKernel ((v : ℝ) + y) x|) ≤
      replacementConstant * R * (v : ℝ) * (y⁻¹ ^ 2 / Real.sqrt y) := by
  have hμ1 := integrable_id_of_ae_bound μ hR hb
  have hμ2 := integrable_sq_of_ae_bound μ hR hb
  have hμ3 := integrable_abs_pow_of_ae_bound μ hR hb 3
  have hν1 : Integrable (fun u : ℝ ↦ u) (gaussianReal 0 v) := by
    apply (integrable_norm_iff (by fun_prop)).mp
    simpa only [Real.norm_eq_abs, pow_one] using integrable_gaussian_abs_pow v 1
  have hν2 : Integrable (fun u : ℝ ↦ u ^ 2) (gaussianReal 0 v) := by
    simpa only [sq_abs] using integrable_gaussian_abs_pow v 2
  have h1 : deriv (firstKernel y) = firstSpatialKernel y :=
    funext (fun x ↦ (hasDerivAt_firstKernel_space hy x).deriv)
  have h2 : deriv (firstSpatialKernel y) = secondSpatialKernel y :=
    funext (fun x ↦ (hasDerivAt_firstSpatialKernel_space hy x).deriv)
  have hD1 : Integrable (deriv (firstKernel y)) volume := by
    rw [h1]; exact integrable_firstSpatialKernel hy
  have hD2 : Integrable (iteratedDeriv 2 (firstKernel y)) volume := by
    simp only [iteratedDeriv_succ, iteratedDeriv_zero, h1, h2]
    exact integrable_secondSpatialKernel hy
  have hD3 : Integrable (iteratedDeriv 3 (firstKernel y)) volume := by
    rw [iteratedDeriv_firstKernel_three hy]
    exact integrable_thirdSpatialKernel hy
  have hcomp := integral_abs_averageTranslate_sub_le μ (gaussianReal 0 v)
    ((contDiff_firstKernel y).of_le (by simp)) (abs_firstKernel_le hy)
    (integrable_firstKernel hy) hD1 hD2 hD3 hμ1 hν1 hμ2 hν2 hμ3
    (integrable_gaussian_abs_pow v 3)
    (by rw [hm, integral_id_gaussianReal]) (by rw [hv, integral_sq_gaussian])
  have he (x : ℝ) : averageTranslate (gaussianReal 0 v) (firstKernel y) x =
      firstKernel ((v : ℝ) + y) x := firstSmooth_gaussian v hy x
  simp_rw [he] at hcomp
  rw [iteratedDeriv_firstKernel_three hy, integral_abs_thirdSpatialKernel hy] at hcomp
  have hμbound := integral_abs_cube_le_of_ae_bound μ hR hb
  rw [hv] at hμbound
  have hvR : (v : ℝ) ≤ R ^ 2 := by rw [← hv]; exact integral_sq_le_of_ae_bound μ hR hb
  have hνbound := gaussian_thirdMoment_le hR hvR
  apply hcomp.trans
  have hsum := add_le_add hμbound hνbound
  have hmul := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hsum (by norm_num : (0 : ℝ) ≤ 6))
    (show 0 ≤ y⁻¹ ^ 2 / Real.sqrt y * thirdSpatialNorm by positivity [thirdSpatialNorm_nonneg])
  convert hmul using 1 <;> try rfl
  unfold replacementConstant
  ring

end LpSelfSimilar.Gaussian
