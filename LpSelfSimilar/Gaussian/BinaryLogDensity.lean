module

public import LpSelfSimilar.Gaussian.BinaryInformationIntegral
public import LpSelfSimilar.Gaussian.BinaryOutputIntegrals

@[expose] public section

/-!
# Log-density and integrability for the binary Gaussian law

The exact density factorization expresses its logarithm as a quadratic plus
log cosh. Gaussian second moments and the linear log-cosh bound prove genuine
integrability under each component and hence under the actual mixture. These
facts justify the subsequent differential-entropy computation for every real
amplitude, including zero.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real

namespace LpSelfSimilar.Gaussian

/-- Logarithm of the standard Gaussian density with its exact normalization. -/
theorem log_kernel_one (x : ℝ) :
    log (kernel 1 x) = -log (sqrt (2 * Real.pi)) - x ^ 2 / 2 := by
  have hs : sqrt (2 * Real.pi) ≠ 0 := (sqrt_pos.mpr (by positivity)).ne'
  simp only [kernel, mul_one]
  rw [log_mul (inv_ne_zero hs) (exp_ne_zero _), log_inv, log_exp]
  ring

/-- The actual mixture log-density is a quadratic plus log cosh. -/
theorem log_binaryGaussianDensity (u x : ℝ) :
    log (binaryGaussianDensity u x) =
      -log (sqrt (2 * Real.pi)) - x ^ 2 / 2 - u ^ 2 / 2 + log (cosh (u * x)) := by
  rw [binaryGaussianDensity_eq_cosh,
    log_mul (mul_ne_zero (kernel_pos (y := 1) (by norm_num) x).ne' (exp_ne_zero _))
      (cosh_pos _).ne',
    log_mul (kernel_pos (y := 1) (by norm_num) x).ne' (exp_ne_zero _),
    log_exp, log_kernel_one]
  ring

/-- The square is integrable under every variance-one Gaussian component. -/
theorem integrable_sq_gaussian_unit (a : ℝ) :
    Integrable (fun x : ℝ => x ^ 2) (gaussianReal a 1) :=
  (memLp_two_iff_integrable_sq (by fun_prop)).mp (memLp_id_gaussianReal 2)

/-- The exact second moment of a variance-one Gaussian component. -/
theorem integral_sq_gaussian_unit (a : ℝ) :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal a 1) = a ^ 2 + 1 := by
  have h := variance_eq_sub (memLp_id_gaussianReal (μ := a) (v := 1) 2)
  change variance (fun x : ℝ => x) (gaussianReal a 1) =
    (∫ x : ℝ, x ^ 2 ∂gaussianReal a 1) - (∫ x : ℝ, x ∂gaussianReal a 1) ^ 2 at h
  rw [variance_fun_id_gaussianReal, integral_id_gaussianReal] at h
  norm_num only [NNReal.coe_one] at h
  linarith

/-- The standard Gaussian log-density is integrable under every Gaussian component. -/
theorem integrable_log_kernel_one_gaussian (a : ℝ) :
    Integrable (fun x : ℝ => log (kernel 1 x)) (gaussianReal a 1) := by
  simp_rw [log_kernel_one]
  exact (integrable_const _).sub ((integrable_sq_gaussian_unit a).div_const 2)

/-- Each component has a finite expectation of the absolute mixture log-density. -/
theorem integrable_log_binaryGaussianDensity_gaussian (u a : ℝ) :
    Integrable (fun x : ℝ => log (binaryGaussianDensity u x)) (gaussianReal a 1) := by
  simp_rw [log_binaryGaussianDensity]
  exact (((integrable_const _).sub ((integrable_sq_gaussian_unit a).div_const 2)).sub
    (integrable_const _)).add (integrable_log_cosh_gaussian u a)

/-- Integrable component tests are integrable under the actual finite mixture. -/
theorem integrable_binaryGaussianLaw_of_components (u : ℝ) {f : ℝ → ℝ}
    (hf : Measurable f) (hp : Integrable f (gaussianReal u 1))
    (hn : Integrable f (gaussianReal (-u) 1)) : Integrable f (binaryGaussianLaw u) := by
  rw [binaryGaussianLaw_eq_channel_mixture]
  apply (Measure.integrable_comp_iff hf.aestronglyMeasurable).mpr
  constructor
  · refine ae_of_all _ (fun b => ?_)
    rw [binary_channel_component_eq_gaussian]
    cases b
    · exact hn
    · exact hp
  · exact Integrable.of_finite

/-- The actual mixture has an integrable log-density, not just a total real integral. -/
theorem integrable_log_binaryGaussianDensity (u : ℝ) :
    Integrable (fun x : ℝ => log (binaryGaussianDensity u x)) (binaryGaussianLaw u) := by
  apply integrable_binaryGaussianLaw_of_components u
    ((continuous_binaryGaussianDensity u).measurable.log)
  · exact integrable_log_binaryGaussianDensity_gaussian u u
  · exact integrable_log_binaryGaussianDensity_gaussian u (-u)

/-- The mixture log-density is even in the observed coordinate. -/
theorem log_binaryGaussianDensity_neg (u x : ℝ) :
    log (binaryGaussianDensity u (-x)) = log (binaryGaussianDensity u x) := by
  simp only [log_binaryGaussianDensity, neg_sq, mul_neg, cosh_neg]

end LpSelfSimilar.Gaussian
