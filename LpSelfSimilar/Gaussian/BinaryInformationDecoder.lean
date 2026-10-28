module

public import LpSelfSimilar.Gaussian.BinaryInformationBounds
public import LpSelfSimilar.Gaussian.BinarySignLaw
public import LpSelfSimilar.Entropy.BinaryDecisionDivergence

@[expose] public section

/-!
# High-amplitude binary Gaussian information

KL data processing through the actual sign decoder gives the binary entropy
lower bound. At amplitude two its proved error is below 1/32. Combined with
the quadratic upper bound at amplitude 2/M, this yields a strict information
gain above 0.516, and hence above one half, whenever M is at least exp 2.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory InformationTheory Real Set
open scoped ENNReal
open LpSelfSimilar.Probability

namespace LpSelfSimilar.Gaussian

/-- The actual component divergence is finite by the finite-channel entropy bound. -/
theorem gaussian_binary_klDiv_ne_top (u : ℝ) :
    klDiv (gaussianReal u 1) (binaryGaussianLaw u) ≠ ∞ := by
  have h := Entropy.channel_klDiv_ne_top (PMF.uniformOfFintype Bool)
    ((additiveNoiseKernel (gaussianReal 0 1)).comap
      (fun b : Bool => if b then u else -u) (measurable_of_countable _))
    (i := true) (by simp [PMF.uniformOfFintype_apply])
  simpa only [← binaryGaussianLaw_eq_channel_mixture,
    binary_channel_component_eq_gaussian, ite_true] using h

/-- The sign decoder bounds actual information by its binary conditional error. -/
theorem binaryGaussianInformation_ge_sign_entropy (u : ℝ) :
    log 2 - binEntropy (((gaussianReal 0 1) (Ioi u)).toReal) ≤ binaryGaussianInformation u := by
  have h := Entropy.binary_decision_le_toReal_klDiv
    (gaussianReal u 1) (binaryGaussianLaw u) measurable_nonnegativeSign
    (binaryGaussianLaw_sign_masses u) (gaussian_binary_klDiv_ne_top u)
  rw [gaussian_positive_component_sign_error, gaussian_binary_klDiv_toReal,
    ← binaryGaussianInformation_eq_integral] at h
  exact h

/-- The exact amplitude-two information bound from the source's sign estimator. -/
theorem binaryGaussianInformation_two_lower :
    log 2 - (1 + log 32) / 32 ≤ binaryGaussianInformation 2 := by
  have h := Entropy.small_binary_error_le_toReal_klDiv
    (gaussianReal 2 1) (binaryGaussianLaw 2) measurable_nonnegativeSign
    (binaryGaussianLaw_sign_masses 2) (gaussian_binary_klDiv_ne_top 2)
    gaussian_positive_component_sign_error_two_lt.le
  rwa [gaussian_binary_klDiv_toReal, ← binaryGaussianInformation_eq_integral] at h

/-- The low-amplitude term in the high-scale comparison has its exact Gaussian bound. -/
theorem binaryGaussianInformation_two_div_le {M : ℝ} (hM : exp 2 ≤ M) :
    binaryGaussianInformation (2 / M) ≤ 2 * exp (-4) := by
  have hpos : 0 < M := (exp_pos _).trans_le hM
  have he : exp (2 : ℝ) ^ 2 = exp 4 := by
    rw [pow_two, ← exp_add]; norm_num
  calc
    _ ≤ (2 / M) ^ 2 / 2 := binaryGaussianInformation_le_half_sq (by positivity)
    _ ≤ (2 / exp 2) ^ 2 / 2 := by gcongr
    _ = 2 * exp (-4) := by rw [div_pow, he, exp_neg]; ring

/-- The strict 0.516 margin is retained for every scale M>=exp 2. -/
theorem binaryGaussianInformation_high_scale_margin {M : ℝ} (hM : exp 2 ≤ M) :
    (516 / 1000 : ℝ) < binaryGaussianInformation 2 - binaryGaussianInformation (2 / M) := by
  linarith [binaryGaussianInformation_two_lower, binaryGaussianInformation_two_div_le hM,
    Entropy.binary_decoder_information_margin]

/-- A positive amplitude supplies the required uniform one-half gain at every high scale. -/
theorem exists_binaryGaussianInformation_half_gain {M : ℝ} (hM : exp 2 ≤ M) :
    ∃ u : ℝ, 0 < u ∧ (1 / 2 : ℝ) ≤
      binaryGaussianInformation (u * M) - binaryGaussianInformation u := by
  have hpos : 0 < M := (exp_pos _).trans_le hM
  refine ⟨2 / M, by positivity, ?_⟩
  rw [div_mul_cancel₀ _ hpos.ne']
  linarith [binaryGaussianInformation_high_scale_margin hM]

end LpSelfSimilar.Gaussian
