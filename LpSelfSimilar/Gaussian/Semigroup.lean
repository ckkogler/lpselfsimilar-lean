module

public import LpSelfSimilar.Gaussian.SmoothingMeasure
public import LpSelfSimilar.Gaussian.Detail
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section

/-!
Gaussian convolution adds variances. Equality of the continuous densities upgrades
the measure semigroup law to a pointwise identity. Differentiation then gives
the first-derivative semigroup and the exact ordinary detail of a Gaussian.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real Set Filter
open scoped Topology NNReal

namespace LpSelfSimilar.Gaussian

lemma smooth_gaussian (v : ℝ≥0) {y : ℝ} (hy : 0 < y) :
    smooth (gaussianReal 0 v) y = kernel ((v : ℝ) + y) := by
  have hsum : 0 < (v : ℝ) + y := by positivity
  have hv : v + NNReal.mk y hy.le = NNReal.mk ((v : ℝ) + y) hsum.le := by
    ext
    rfl
  have hne : (NNReal.mk ((v : ℝ) + y) hsum.le) ≠ 0 := by
    intro h
    have he := congrArg (fun t : ℝ≥0 ↦ (t : ℝ)) h
    exact hsum.ne' (by simpa using he)
  have hm : volume.withDensity (fun x ↦ ENNReal.ofReal (smooth (gaussianReal 0 v) y x)) =
      volume.withDensity (fun x ↦ ENNReal.ofReal (kernel ((v : ℝ) + y) x)) := by
    rw [← convolution_gaussian_eq_withDensity _ hy, gaussianReal_conv_gaussianReal,
      zero_add, hv, gaussianReal_of_var_ne_zero _ hne, gaussianPDF_def]
    simp_rw [kernel_eq_gaussianPDFReal hsum.le]
  have hae := (withDensity_eq_iff_of_sigmaFinite
    (continuous_smooth_space (gaussianReal 0 v) hy).measurable.ennreal_ofReal.aemeasurable
    (continuous_kernel ((v : ℝ) + y)).measurable.ennreal_ofReal.aemeasurable).mp hm
  apply eq_of_ae_eq (μ := volume) _ (continuous_smooth_space _ hy) (continuous_kernel _)
  filter_upwards [hae] with x hx
  have ht := congrArg ENNReal.toReal hx
  simpa only [ENNReal.toReal_ofReal (smooth_nonneg _ hy _),
    ENNReal.toReal_ofReal (kernel_pos hsum x).le] using ht

lemma firstSmooth_gaussian (v : ℝ≥0) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    firstSmooth (gaussianReal 0 v) y x = firstKernel ((v : ℝ) + y) x := by
  have hsum : 0 < (v : ℝ) + y := by positivity
  have hk := (hasDerivAt_kernel_variance hsum x).comp y (h := fun z : ℝ ↦ (v : ℝ) + z)
    ((hasDerivAt_id y).const_add (v : ℝ))
  have he : (fun z ↦ smooth (gaussianReal 0 v) z x) =ᶠ[𝓝 y]
      (fun z ↦ kernel ((v : ℝ) + z) x) := by
    filter_upwards [Ioi_mem_nhds hy] with z hz
    exact congrFun (smooth_gaussian v hz) x
  have hk' : HasDerivAt (fun z ↦ kernel ((v : ℝ) + z) x)
      (firstKernel ((v : ℝ) + y) x) y := by
    convert hk using 1 <;> first | rfl | simp only [mul_one]
  exact (hasDerivAt_smooth_variance (gaussianReal 0 v) hy x).unique
    (hk'.congr_of_eventuallyEq he)

/-- Exact Gaussian detail: added Gaussian variance reduces detail by `r²/(r²+v)`. -/
lemma detail_gaussian (v : ℝ≥0) {r : ℝ} (hr : 0 < r) :
    detail (gaussianReal 0 v) r = r ^ 2 / (r ^ 2 + (v : ℝ)) := by
  have hy : 0 < r ^ 2 := sq_pos_of_pos hr
  have hsum : 0 < (v : ℝ) + r ^ 2 := by positivity
  unfold detail
  change r ^ 2 * detailNormalization * (∫ x, |firstSmooth (gaussianReal 0 v) (r ^ 2) x|) = _
  simp_rw [firstSmooth_gaussian v hy]
  rw [integral_abs_firstKernel hsum]
  unfold detailNormalization
  have hn := firstNorm_pos
  field_simp
  <;> ring

end LpSelfSimilar.Gaussian
