module

public import LpSelfSimilar.Bernoulli.SmoothedGaussianApproximation
public import LpSelfSimilar.Bernoulli.SmoothedGaussianRescaling
public import LpSelfSimilar.Bernoulli.SmoothingDensity
public import LpSelfSimilar.Analysis.BoundedTestLimit

@[expose] public section

/-!
# The strict Gaussian error in the working regularity criterion

Positive variance normalization preserves the L1 norm. The actual smoothed
law is within 9*chi/5 of the Gaussian of variance (1-theta^2) inverse.
The proved nonnegative density differs from this smoothing by less than
chi/100. Their L1 triangle inequality gives the strict 2*chi conclusion
with the original entropy and separation hypotheses and no assumed density.
The separate sharp L2 conclusion of the working criterion is not proved here.
-/

open MeasureTheory Set
open LpSelfSimilar.Analysis LpSelfSimilar.Fourier LpSelfSimilar.Gaussian LpSelfSimilar.Entropy
open scoped ENNReal

namespace LpSelfSimilar.Bernoulli

/-- The Gaussian approximation at the original variance scale, with exact constant nine fifths. -/
theorem integral_abs_original_packing_smoothedGaussianError_lt {θ ρ L : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hgap : -Real.log θ ≤ 1 / 250)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L)
    (hsmall : (-Real.log θ) * packingLogScale (L / ρ) ^ 2 ≤ ρ / 2) :
    (∫ x : ℝ, |measureFunctionConvolution (convolution θ)
      (rescaledKernel (-Real.log θ) (quinticSmoothingKernel (packingFrequencyWidth (L / ρ)))) x -
        kernel ((1 - θ ^ 2)⁻¹) x|) < (9 / 5 : ℝ) * (-Real.log θ) := by
  rw [← integral_abs_smoothedGaussianError_eq_original hθ0 hθ1
    (packingFrequencyWidth_pos (three_le_separation_entropy_ratio hρ hρ1 hL))]
  exact integral_abs_packing_smoothedGaussianError_lt hθ0 hθ1 hgap hρ hρ1 hL hsmall

/-- The working entropy/separation criterion gives an actual nonnegative density with strict 2*chi Gaussian error. -/
theorem bernoulli_exists_density_with_gaussian_error {θ ρ L : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hgap : -Real.log θ ≤ 1 / 250)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L)
    (hC : Real.log (2 / (1 - θ) + 2) / Real.log 2 ≤ L + 2)
    (hsmall : (-Real.log θ) * packingLogScale (L / ρ) ^ 2 ≤ ρ / 2)
    (hentropy : ∀ n : ℕ, 0 < n →
      ρ * n ≤ finiteEntropy (digitPMF θ n) (digitPMF_support_finite θ n) / Real.log 2)
    (hsep : ∀ n : ℕ, 0 < n → ∀ x ∈ (digitPMF θ n).support,
      ∀ y ∈ (digitPMF θ n).support, x ≠ y → (2 : ℝ) ^ (-(L * n)) ≤ |x - y|) :
    ∃ f : ℝ → ℝ, Measurable f ∧ Integrable f ∧ (∀ x, 0 ≤ f x) ∧
      convolution θ = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
      (∫ x : ℝ, |f x - kernel ((1 - θ ^ 2)⁻¹) x|) < 2 * (-Real.log θ) := by
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  have hε := packingFrequencyWidth_pos (three_le_separation_entropy_ratio hρ hρ1 hL)
  obtain ⟨f, hfm, hfi, hf0, heq, herror⟩ :=
    bernoulli_exists_density_with_smoothing_error hθ0 hθ1 hgap hρ hρ1 hL hC hsmall hentropy hsep
  refine ⟨f, hfm, hfi, hf0, heq, ?_⟩
  let s := measureFunctionConvolution (convolution θ)
    (rescaledKernel (-Real.log θ) (quinticSmoothingKernel (packingFrequencyWidth (L / ρ))))
  have his : Integrable s := integrable_measureFunctionConvolution (convolution θ)
    (continuous_rescaledKernel (continuous_quinticSmoothingKernel hε) _)
    (integrable_rescaledKernel (integrable_quinticSmoothingKernel hε) hχ.ne')
  have hig : Integrable (kernel ((1 - θ ^ 2)⁻¹)) := integrable_kernel (by
    exact inv_nonneg.mpr (variance_scale_pos hθ0.le hθ1).le)
  have ht := integral_abs_sub_triangle hfi his hig
  have hg := integral_abs_original_packing_smoothedGaussianError_lt hθ0 hθ1 hgap hρ hρ1 hL hsmall
  change (∫ x : ℝ, |f x - s x|) < (-Real.log θ) / 100 at herror
  change (∫ x : ℝ, |s x - kernel ((1 - θ ^ 2)⁻¹) x|) < (9 / 5 : ℝ) * (-Real.log θ) at hg
  linarith

end LpSelfSimilar.Bernoulli
