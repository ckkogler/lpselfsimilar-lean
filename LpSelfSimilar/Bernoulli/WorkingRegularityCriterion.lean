module

public import LpSelfSimilar.Bernoulli.GaussianApproximation
public import LpSelfSimilar.Bernoulli.GaussianApproximationL2

@[expose] public section

/-!
# Complete working regularity criterion

Proposition 1.3 holds at its displayed entropy, separation and numerical
hypotheses. The actual fair-sign Bernoulli law has a measurable nonnegative
L2 density and strict Gaussian L1 error less than 2*chi, with variance
(1-theta^2) inverse. Entropy is in bits, expressed by dividing the established
natural-logarithm finite entropy by log 2. All analytic inputs, including
removal of smoothing, normalization and the sharp L2 upgrade, are proved.
-/

open MeasureTheory Set
open LpSelfSimilar.Analysis LpSelfSimilar.Fourier LpSelfSimilar.Gaussian LpSelfSimilar.Entropy
open scoped ENNReal

namespace LpSelfSimilar.Bernoulli

/-- Proposition 1.3: the exact working criterion gives an actual L2 density and strict 2*chi Gaussian error. -/
theorem working_regularity_criterion {θ ρ L : ℝ}
    (hθhalf : 1 / 2 < θ) (hθ1 : θ < 1) (hgap : -Real.log θ ≤ 1 / 250)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L)
    (hC : Real.log (2 / (1 - θ) + 2) / Real.log 2 ≤ L + 2)
    (hsmall : (-Real.log θ) * packingLogScale (L / ρ) ^ 2 ≤ ρ / 2)
    (hentropy : ∀ n : ℕ, 0 < n →
      ρ * n ≤ finiteEntropy (digitPMF θ n) (digitPMF_support_finite θ n) / Real.log 2)
    (hsep : ∀ n : ℕ, 0 < n → ∀ x ∈ (digitPMF θ n).support,
      ∀ y ∈ (digitPMF θ n).support, x ≠ y → (2 : ℝ) ^ (-(L * n)) ≤ |x - y|) :
    ∃ f : ℝ → ℝ, Measurable f ∧ Integrable f volume ∧ (∀ x, 0 ≤ f x) ∧
      convolution θ = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
      MemLp f 2 volume ∧
      (∫ x : ℝ, |f x - kernel ((1 - θ ^ 2)⁻¹) x|) < 2 * (-Real.log θ) := by
  have hθ0 : 0 < θ := by linarith
  obtain ⟨f, hfm, hfi, hf0, hrep, herr⟩ :=
    bernoulli_exists_density_with_gaussian_error hθ0 hθ1 hgap hρ hρ1 hL hC hsmall hentropy hsep
  exact ⟨f, hfm, hfi, hf0, hrep,
    bernoulli_density_memLp_two_of_gaussian_error hθ0 hθ1 hgap hfm hfi hf0 hrep herr.le, herr⟩

end LpSelfSimilar.Bernoulli
