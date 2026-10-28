module

public import LpSelfSimilar.Bernoulli.IntegratedDetailSmallness
public import LpSelfSimilar.Fourier.QuinticDetailConvolutionNorm
public import LpSelfSimilar.Fourier.QuinticSmoothingLimit

@[expose] public section

/-!
# The actual Bernoulli smoothings converge in L1

The full working criterion supplies the strict integrated-detail estimate for
the actual real quintic kernel. All kernel hypotheses of the general L1 limit
theorem have already been proved. The resulting measurable integrable function
has error strictly below chi/100 from the initial smoothing. Identifying it
with a nonnegative density of the original law remains a separate obligation.
-/

open MeasureTheory Set Filter
open LpSelfSimilar.Analysis LpSelfSimilar.Entropy
open scoped Topology

namespace LpSelfSimilar.Bernoulli

/-- The actual real detail inherits the exact integrability and strict gap/100 bound. -/
theorem bernoulli_integrated_real_detail_lt_gap_div_hundred {θ ρ L : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hgap : -Real.log θ ≤ 1 / 250)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L)
    (hC : Real.log (2 / (1 - θ) + 2) / Real.log 2 ≤ L + 2)
    (hsmall : (-Real.log θ) * (packingLogScale (L / ρ)) ^ 2 ≤ ρ / 2)
    (hentropy : ∀ n : ℕ, 0 < n →
      ρ * n ≤ finiteEntropy (digitPMF θ n) (digitPMF_support_finite θ n) / Real.log 2)
    (hsep : ∀ n : ℕ, 0 < n → ∀ x ∈ (digitPMF θ n).support,
      ∀ y ∈ (digitPMF θ n).support, x ≠ y → (2 : ℝ) ^ (-(L * n)) ≤ |x - y|) :
    let χ := -Real.log θ
    let ψ := Fourier.quinticDetailKernel (packingFrequencyWidth (L / ρ))
    let d := fun r : ℝ => ∫ x, ‖measureFunctionConvolution (convolution θ) (rescaledKernel r ψ) x‖
    IntegrableOn (fun r => d r / r) (Ioc 0 χ) volume ∧
      (∫ r in Ioc 0 χ, d r / r) < χ / 100 := by
  dsimp only
  simp_rw [Fourier.integral_norm_convolution_quinticDetail_eq_complex]
  exact bernoulli_integrated_detail_lt_gap_div_hundred
    hθ0 hθ1 hgap hρ hρ1 hL hC hsmall hentropy hsep

/-- The full working criterion gives an actual measurable L1 limit with strict smoothing error. -/
theorem bernoulli_exists_smoothing_L1_limit {θ ρ L : ℝ}
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
    ∃ f : ℝ → ℝ, Measurable f ∧ Integrable f ∧
      Tendsto (fun n => ∫ x,
        |measureFunctionConvolution (convolution θ)
          (rescaledKernel (reciprocalScaleSequence χ n) φ) x - f x|) atTop (𝓝 0) ∧
      (∫ x, |f x - measureFunctionConvolution (convolution θ) (rescaledKernel χ φ) x|) < χ / 100 := by
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  have hε := packingFrequencyWidth_pos (three_le_separation_entropy_ratio hρ hρ1 hL)
  have hdetail := bernoulli_integrated_real_detail_lt_gap_div_hundred
    hθ0 hθ1 hgap hρ hρ1 hL hC hsmall hentropy hsep
  obtain ⟨f, hfm, hfi, hlim, herr⟩ :=
    Fourier.exists_quintic_smoothing_L1_limit (convolution θ) hε hχ hdetail.1
  exact ⟨f, hfm, hfi, hlim, herr.trans_lt hdetail.2⟩

end LpSelfSimilar.Bernoulli
