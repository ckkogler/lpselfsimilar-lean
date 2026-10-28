module

public import LpSelfSimilar.Bernoulli.SmoothedGaussianPlancherel
public import LpSelfSimilar.Fourier.AmplitudeSquareIntegrability
public import LpSelfSimilar.Analysis.QuadraticDifferenceEnergy

@[expose] public section

/-!
# Square-integrable energies for the actual smoothed Gaussian error

The previously proved L1 Fourier pairs and their derivative pairs imply
square integrability of the actual amplitudes. The squared triangle bound
then supplies both Gaussian-error components, justifying all later integral
splits and sums without adding an analytic hypothesis.
-/

open MeasureTheory
open LpSelfSimilar.Fourier LpSelfSimilar.Gaussian LpSelfSimilar.Analysis

namespace LpSelfSimilar.Bernoulli

/-- The actual smoothed amplitude, derivative, and both Gaussian error components have L1 energies. -/
theorem integrable_smoothedGaussian_fourier_energy_components {θ ε : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hε : 0 < ε) :
    let F := angularFourier (fun x => (varianceNormalizedSmoothing θ ε x : ℂ))
    Integrable (fun u : ℝ => ‖F u‖ ^ 2) ∧
    Integrable (fun u : ℝ => ‖deriv F u‖ ^ 2) ∧
    Integrable (fun u : ℝ => ‖F u - standardGaussianAmplitude u‖ ^ 2) ∧
    Integrable (fun u : ℝ => ‖deriv F u - deriv standardGaussianAmplitude u‖ ^ 2) := by
  let F := angularFourier (fun x => (varianceNormalizedSmoothing θ ε x : ℂ))
  have hF : ContDiff ℝ 1 F := contDiff_one_angularFourier_varianceNormalizedSmoothing hθ0 hθ1 hε
  have hG : ContDiff ℝ 1 standardGaussianAmplitude :=
    contDiff_standardGaussianAmplitude.of_le (by simp)
  have hiF := integrable_angularFourier_varianceNormalizedSmoothing_and_deriv hθ0 hθ1 hε
  have hf := integrable_sq_norm_of_integrable_angularInverseFourier hF.continuous hiF.1
    (integrable_angularInverseFourier_angularFourier_varianceNormalizedSmoothing hθ0 hθ1 hε)
  have hdf := integrable_sq_norm_of_integrable_angularInverseFourier hF.continuous_deriv_one hiF.2
    (integrable_inverse_deriv_smoothedFourier hθ0 hθ1 hε)
  have hg := integrable_sq_norm_of_integrable_angularInverseFourier hG.continuous
    integrable_standardGaussianAmplitude integrable_inverse_standardGaussianAmplitude
  have hdg := integrable_sq_norm_of_integrable_angularInverseFourier hG.continuous_deriv_one
    integrable_deriv_standardGaussianAmplitude integrable_inverse_deriv_standardGaussianAmplitude
  exact ⟨hf, hdf,
    integrable_sq_norm_sub_of_sq hF.continuous.aestronglyMeasurable
      hG.continuous.aestronglyMeasurable hf hg,
    integrable_sq_norm_sub_of_sq hF.continuous_deriv_one.aestronglyMeasurable
      hG.continuous_deriv_one.aestronglyMeasurable hdf hdg⟩

end LpSelfSimilar.Bernoulli
