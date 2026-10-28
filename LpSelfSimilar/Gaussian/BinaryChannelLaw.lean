module

public import LpSelfSimilar.Probability.MapProbability

public import LpSelfSimilar.Gaussian.BinaryChannelDensity
public import LpSelfSimilar.Entropy.DensityLikelihood

@[expose] public section

/-!
# Binary Gaussian output law and its actual likelihood

The output law is the convolution of the fair two-point amplitude law with
the standard Gaussian. It is also exactly the mixture of the additive channel
used in the information definition. Its explicit positive density identifies
the true Radon--Nikodym log-likelihood of each component, so KL integrals can
be computed without assuming a differential-entropy formula.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real

namespace LpSelfSimilar.Gaussian

noncomputable def binaryGaussianLaw (u : ℝ) : Measure ℝ :=
  ((PMF.uniformOfFintype Bool).toMeasure.map (fun b ↦ if b then u else -u)) ∗
    gaussianReal 0 1

instance binaryGaussianLaw_isProbabilityMeasure (u : ℝ) :
    IsProbabilityMeasure (binaryGaussianLaw u) := by
  have : IsProbabilityMeasure
      ((PMF.uniformOfFintype Bool).toMeasure.map (fun b ↦ if b then u else -u)) :=
    LpSelfSimilar.Probability.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  unfold binaryGaussianLaw
  infer_instance

theorem binaryGaussianLaw_eq_withDensity (u : ℝ) :
    binaryGaussianLaw u = volume.withDensity (fun x ↦ ENNReal.ofReal (binaryGaussianDensity u x)) :=
  binary_gaussian_convolution_eq_withDensity u

theorem binaryGaussianLaw_eq_channel_mixture (u : ℝ) :
    binaryGaussianLaw u =
      (additiveNoiseKernel (gaussianReal 0 1)).comap
        (fun b : Bool ↦ if b then u else -u) (measurable_of_countable _) ∘ₘ
          (PMF.uniformOfFintype Bool).toMeasure :=
  (Entropy.additive_channel_mixture _ _ _).symm

theorem binaryGaussianDensity_neg_amplitude (u x : ℝ) :
    binaryGaussianDensity (-u) x = binaryGaussianDensity u x := by
  simp only [binaryGaussianDensity, sub_neg_eq_add, sub_eq_add_neg]
  ring

theorem binaryGaussianLaw_neg (u : ℝ) : binaryGaussianLaw (-u) = binaryGaussianLaw u := by
  simp_rw [binaryGaussianLaw_eq_withDensity, binaryGaussianDensity_neg_amplitude]

/-- Every component is the usual Gaussian with that sign's mean and variance one. -/
theorem binary_channel_component_eq_gaussian (u : ℝ) (b : Bool) :
    (additiveNoiseKernel (gaussianReal 0 1)).comap
        (fun b : Bool ↦ if b then u else -u) (measurable_of_countable _) b =
      gaussianReal (if b then u else -u) 1 := by
  rw [Kernel.comap_apply, additiveNoiseKernel_apply, gaussianReal_map_const_add]
  simp

theorem gaussianReal_unit_eq_withDensity (a : ℝ) :
    gaussianReal a 1 = volume.withDensity (fun x ↦ ENNReal.ofReal (kernel 1 (x - a))) := by
  rw [gaussianReal_of_var_ne_zero _ (by norm_num), gaussianPDF_def]
  congr 1

/-- Pointwise log-likelihood of the positive-mean component against the mixture. -/
theorem log_kernel_sub_div_binaryGaussianDensity (u x : ℝ) :
    log (kernel 1 (x - u) / binaryGaussianDensity u x) = u * x - log (cosh (u * x)) := by
  have hc : kernel 1 x * exp (-(u ^ 2) / 2) ≠ 0 :=
    mul_ne_zero (kernel_pos (y := 1) (by norm_num) x).ne' (exp_ne_zero _)
  rw [kernel_one_sub_eq, binaryGaussianDensity_eq_cosh, mul_div_mul_left _ _ hc,
    log_div (exp_ne_zero _) (cosh_pos _).ne', log_exp]

/-- Actual almost-everywhere log-likelihood, identified using Radon--Nikodym derivatives. -/
theorem gaussian_binary_llr (u : ℝ) :
    llr (gaussianReal u 1) (binaryGaussianLaw u) =ᵐ[gaussianReal u 1]
      fun x ↦ u * x - log (cosh (u * x)) := by
  have h := Entropy.llr_eq_log_density_ratio volume (gaussianReal u 1) (binaryGaussianLaw u)
    (f := fun x ↦ kernel 1 (x - u)) (g := binaryGaussianDensity u)
    (by fun_prop) (continuous_binaryGaussianDensity u).measurable
    (fun x ↦ (kernel_pos (y := 1) (by norm_num) _).le) (binaryGaussianDensity_pos u)
    (gaussianReal_unit_eq_withDensity u) (binaryGaussianLaw_eq_withDensity u)
  exact h.trans (ae_of_all _ (log_kernel_sub_div_binaryGaussianDensity u))

/-- The actual component KL divergence is the corresponding Gaussian integral. -/
theorem gaussian_binary_klDiv_toReal (u : ℝ) :
    (InformationTheory.klDiv (gaussianReal u 1) (binaryGaussianLaw u)).toReal =
      ∫ x, (u * x - log (cosh (u * x))) ∂gaussianReal u 1 := by
  have h := Entropy.toReal_klDiv_eq_integral_log_density_ratio
    volume (gaussianReal u 1) (binaryGaussianLaw u)
    (f := fun x ↦ kernel 1 (x - u)) (g := binaryGaussianDensity u)
    (by fun_prop) (continuous_binaryGaussianDensity u).measurable
    (fun x ↦ (kernel_pos (y := 1) (by norm_num) _).le) (binaryGaussianDensity_pos u)
    (gaussianReal_unit_eq_withDensity u) (binaryGaussianLaw_eq_withDensity u)
  rw [h]
  apply integral_congr_ae
  exact ae_of_all _ (log_kernel_sub_div_binaryGaussianDensity u)

end LpSelfSimilar.Gaussian
