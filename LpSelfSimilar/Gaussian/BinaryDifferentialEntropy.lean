module

public import LpSelfSimilar.Gaussian.BinaryLogDensity
public import LpSelfSimilar.Entropy.DifferentialEntropy

@[expose] public section

/-!
# Differential entropy of the binary Gaussian channel

Both the standard Gaussian and the actual binary output have integrable
canonical log-densities and integrable density-times-log-density. Computing
their differential entropies from the established mixture and moments gives
exactly the existing finite KL information. The statement includes every real
amplitude and does not assume any entropy or moment identity.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real
open LpSelfSimilar.Entropy

namespace LpSelfSimilar.Gaussian

/-- The component expectation of the mixture log-density, with all constants explicit. -/
theorem integral_log_binaryGaussianDensity_gaussian (u a : ℝ) :
    (∫ x, log (binaryGaussianDensity u x) ∂gaussianReal a 1) =
      -log (sqrt (2 * Real.pi)) - (a ^ 2 + 1) / 2 - u ^ 2 / 2 +
        ∫ x, log (cosh (u * x)) ∂gaussianReal a 1 := by
  have hi : Integrable (fun x : ℝ => -log (sqrt (2 * Real.pi)) - x ^ 2 / 2)
      (gaussianReal a 1) :=
    (integrable_const _).sub ((integrable_sq_gaussian_unit a).div_const 2)
  have hib : Integrable (fun x : ℝ => -log (sqrt (2 * Real.pi)) - x ^ 2 / 2 - u ^ 2 / 2)
      (gaussianReal a 1) := hi.sub (integrable_const (u ^ 2 / 2))
  simp_rw [log_binaryGaussianDensity]
  rw [integral_add hib (integrable_log_cosh_gaussian u a),
    integral_sub hi (integrable_const (u ^ 2 / 2)),
    integral_sub (integrable_const _) ((integrable_sq_gaussian_unit a).div_const 2),
    integral_div, integral_sq_gaussian_unit]
  simp

/-- The standard Gaussian log-density expectation has its usual finite value. -/
theorem integral_log_kernel_standardGaussian :
    (∫ x, log (kernel 1 x) ∂gaussianReal 0 1) = -log (sqrt (2 * Real.pi)) - 1 / 2 := by
  simp_rw [log_kernel_one]
  rw [integral_sub (integrable_const _) ((integrable_sq_gaussian_unit 0).div_const 2),
    integral_div, integral_sq_gaussian_unit]
  simp

/-- Finiteness for the canonical standard Gaussian log-density. -/
theorem integrable_log_rnDeriv_standardGaussian :
    Integrable (fun x => log (((gaussianReal 0 1).rnDeriv volume x).toReal))
      (gaussianReal 0 1) := by
  apply integrable_log_rnDeriv_of_density _ (continuous_kernel 1).measurable
    (fun x => (kernel_pos (y := 1) (by norm_num) x).le)
    (by simpa only [sub_zero] using gaussianReal_unit_eq_withDensity 0)
  exact integrable_log_kernel_one_gaussian 0

/-- The conventional density-times-log-density integral is finite for the standard Gaussian. -/
theorem integrable_kernel_mul_log_kernel :
    Integrable (fun x : ℝ => kernel 1 x * log (kernel 1 x)) volume := by
  apply (integrable_log_density_iff (gaussianReal 0 1) (continuous_kernel 1).measurable
    (fun x => (kernel_pos (y := 1) (by norm_num) x).le)
    (by simpa only [sub_zero] using gaussianReal_unit_eq_withDensity 0)).mp
  exact integrable_log_kernel_one_gaussian 0

/-- The canonical standard Gaussian differential entropy, with exact normalization. -/
theorem differentialEntropy_standardGaussian :
    differentialEntropy (gaussianReal 0 1) = log (sqrt (2 * Real.pi)) + 1 / 2 := by
  rw [differentialEntropy_eq_neg_integral_log_density _ (continuous_kernel 1).measurable
    (fun x => (kernel_pos (y := 1) (by norm_num) x).le)
    (by simpa only [sub_zero] using gaussianReal_unit_eq_withDensity 0),
    integral_log_kernel_standardGaussian]
  ring

/-- Finiteness for the actual output law's canonical log-density. -/
theorem integrable_log_rnDeriv_binaryGaussianLaw (u : ℝ) :
    Integrable (fun x => log (((binaryGaussianLaw u).rnDeriv volume x).toReal))
      (binaryGaussianLaw u) :=
  integrable_log_rnDeriv_of_density _ (continuous_binaryGaussianDensity u).measurable
    (fun x => (binaryGaussianDensity_pos u x).le) (binaryGaussianLaw_eq_withDensity u)
    (integrable_log_binaryGaussianDensity u)

/-- The conventional output density-times-log-density integral is genuinely finite. -/
theorem integrable_binaryGaussianDensity_mul_log (u : ℝ) :
    Integrable (fun x => binaryGaussianDensity u x * log (binaryGaussianDensity u x)) volume :=
  (integrable_log_density_iff _ (continuous_binaryGaussianDensity u).measurable
    (fun x => (binaryGaussianDensity_pos u x).le) (binaryGaussianLaw_eq_withDensity u)).mp
    (integrable_log_binaryGaussianDensity u)

/-- The actual binary output differential entropy, computed using reflection symmetry. -/
theorem differentialEntropy_binaryGaussianLaw (u : ℝ) :
    differentialEntropy (binaryGaussianLaw u) =
      log (sqrt (2 * Real.pi)) + 1 / 2 + u ^ 2 -
        ∫ x, log (cosh (u * x)) ∂gaussianReal u 1 := by
  rw [differentialEntropy_eq_neg_integral_log_density _
    (continuous_binaryGaussianDensity u).measurable
    (fun x => (binaryGaussianDensity_pos u x).le) (binaryGaussianLaw_eq_withDensity u),
    integral_binaryGaussianLaw_of_even u (integrable_log_binaryGaussianDensity u)
      ((continuous_binaryGaussianDensity u).measurable.log) (log_binaryGaussianDensity_neg u),
    integral_log_binaryGaussianDensity_gaussian]
  ring

/-- The existing finite KL information is exactly the difference of differential entropies. -/
theorem binaryGaussianInformation_eq_differentialEntropy_sub (u : ℝ) :
    binaryGaussianInformation u =
      differentialEntropy (binaryGaussianLaw u) - differentialEntropy (gaussianReal 0 1) := by
  rw [binaryGaussianInformation_eq_sq_sub_integral, differentialEntropy_binaryGaussianLaw,
    differentialEntropy_standardGaussian]
  ring

end LpSelfSimilar.Gaussian
