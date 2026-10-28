module

public import LpSelfSimilar.Gaussian.BinaryChannelLaw
public import LpSelfSimilar.Analysis.LogCoshRegularity

@[expose] public section

/-!
# Explicit integral for actual binary Gaussian information

The finite KL channel definition reduces to either Gaussian component by
reflection symmetry. The positive component has mean u, giving the fixed-noise
formula I(u) = u^2 - E log cosh(u^2 + u*G). Integrability follows from the
linear log-cosh bound and the Gaussian first moment. Thus this is an identity
for the established information definition, not a new surrogate definition.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real
open LpSelfSimilar.Analysis

namespace LpSelfSimilar.Gaussian

/-- Reflection identifies the two component log-likelihood integrals. -/
theorem integral_binary_likelihood_neg (u : ℝ) :
    (∫ x, ((-u) * x - log (cosh ((-u) * x))) ∂gaussianReal (-u) 1) =
      ∫ x, (u * x - log (cosh (u * x))) ∂gaussianReal u 1 := by
  rw [← gaussianReal_map_neg (μ := u) (v := 1), integral_map (by fun_prop) (by fun_prop)]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by simp only [neg_mul_neg])

/-- The finite KL information equals the explicit one-component likelihood integral. -/
theorem binaryGaussianInformation_eq_integral (u : ℝ) :
    binaryGaussianInformation u =
      ∫ x, (u * x - log (cosh (u * x))) ∂gaussianReal u 1 := by
  unfold binaryGaussianInformation Entropy.additiveInformation
  rw [Entropy.finiteInformation_toReal]
  simp_rw [← binaryGaussianLaw_eq_channel_mixture, binary_channel_component_eq_gaussian]
  simp only [Fintype.sum_bool, PMF.uniformOfFintype_apply, Fintype.card_bool,
    ENNReal.toReal_inv, ENNReal.toReal_ofNat, Bool.false_eq_true, ite_false, ite_true]
  rw [gaussian_binary_klDiv_toReal u, ← binaryGaussianLaw_neg u,
    gaussian_binary_klDiv_toReal (-u), integral_binary_likelihood_neg]
  norm_num <;> ring

/-- The log-cosh term is integrable under a Gaussian at every real amplitude. -/
theorem integrable_log_cosh_gaussian (u a : ℝ) :
    Integrable (fun x : ℝ => log (cosh (u * x))) (gaussianReal a 1) := by
  have hi : Integrable (fun x : ℝ => x) (gaussianReal a 1) :=
    (memLp_id_gaussianReal (μ := a) (v := 1) 1).integrable (by norm_num)
  exact integrable_log_cosh (hi.const_mul u)

/-- Subtracting the actual finite Gaussian expectation yields the centered formula. -/
theorem binaryGaussianInformation_eq_sq_sub_integral (u : ℝ) :
    binaryGaussianInformation u = u ^ 2 - ∫ x, log (cosh (u * x)) ∂gaussianReal u 1 := by
  have hi : Integrable (fun x : ℝ => x) (gaussianReal u 1) :=
    (memLp_id_gaussianReal (μ := u) (v := 1) 1).integrable (by norm_num)
  rw [binaryGaussianInformation_eq_integral, integral_sub (hi.const_mul u)
    (integrable_log_cosh_gaussian u u), integral_const_mul, integral_id_gaussianReal]
  ring

/-- An integral against the fixed standard noise, suitable for dominated differentiation. -/
theorem binaryGaussianInformation_eq_standard_integral (u : ℝ) :
    binaryGaussianInformation u =
      u ^ 2 - ∫ x, log (cosh (u ^ 2 + u * x)) ∂gaussianReal 0 1 := by
  rw [binaryGaussianInformation_eq_sq_sub_integral]
  have hg : gaussianReal u 1 = (gaussianReal 0 1).map (fun x : ℝ => x + u) := by
    rw [gaussianReal_map_add_const]; simp
  have hc : Continuous (fun x : ℝ => log (cosh (u * x))) :=
    continuous_log_cosh.comp (continuous_const.mul continuous_id)
  rw [hg, integral_map (by fun_prop) hc.aestronglyMeasurable]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by congr 2; ring)

end LpSelfSimilar.Gaussian
