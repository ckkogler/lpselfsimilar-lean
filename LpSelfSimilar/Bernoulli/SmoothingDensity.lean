module

public import LpSelfSimilar.Bernoulli.SmoothingLimit
public import LpSelfSimilar.Fourier.QuinticSmoothingDensity

@[expose] public section

/-!
# The nonnegative Bernoulli density and the full smoothing error (5.8)

The full working criterion gives the actual integrated detail bound. The
proved kernel construction and weak/L1 identification then give a measurable
nonnegative integrable density of the original Bernoulli convolution, with
error strictly below chi/100 from its initial quintic smoothing. No density,
absolute continuity or compact-support hypothesis is added.
-/

open MeasureTheory Set
open LpSelfSimilar.Analysis LpSelfSimilar.Entropy
open scoped ENNReal

namespace LpSelfSimilar.Bernoulli

/-- The full working criterion gives the original Bernoulli law a density with exact error (5.8). -/
theorem bernoulli_exists_density_with_smoothing_error {θ ρ L : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hgap : -Real.log θ ≤ 1 / 250)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L)
    (hC : Real.log (2 / (1 - θ) + 2) / Real.log 2 ≤ L + 2)
    (hsmall : (-Real.log θ) * (packingLogScale (L / ρ)) ^ 2 ≤ ρ / 2)
    (hentropy : ∀ n : ℕ, 0 < n →
      ρ * n ≤ finiteEntropy (digitPMF θ n) (digitPMF_support_finite θ n) / Real.log 2)
    (hsep : ∀ n : ℕ, 0 < n → ∀ x ∈ (digitPMF θ n).support,
      ∀ y ∈ (digitPMF θ n).support, x ≠ y → (2 : ℝ) ^ (-(L * n)) ≤ |x - y|) :
    let χ := -Real.log θ
    let φ := Fourier.quinticSmoothingKernel (packingFrequencyWidth (L / ρ))
    ∃ f : ℝ → ℝ, Measurable f ∧ Integrable f ∧ (∀ x, 0 ≤ f x) ∧
      convolution θ = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
      (∫ x, |f x - measureFunctionConvolution (convolution θ) (rescaledKernel χ φ) x|) < χ / 100 := by
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  have hJ := three_le_separation_entropy_ratio hρ hρ1 hL
  have hε := packingFrequencyWidth_pos hJ
  have hε1 : packingFrequencyWidth (L / ρ) ≤ 1 := (packingFrequencyWidth_lt hJ).le.trans (by norm_num)
  have hdetail := bernoulli_integrated_real_detail_lt_gap_div_hundred
    hθ0 hθ1 hgap hρ hρ1 hL hC hsmall hentropy hsep
  obtain ⟨f, hfm, hfi, hf0, he, herr⟩ :=
    Fourier.exists_quintic_smoothing_density (convolution θ) hε hε1 hχ hdetail.1
  exact ⟨f, hfm, hfi, hf0, he, herr.trans_lt hdetail.2⟩

end LpSelfSimilar.Bernoulli
