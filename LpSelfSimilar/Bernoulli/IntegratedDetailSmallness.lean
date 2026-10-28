module

public import LpSelfSimilar.Bernoulli.IntegratedDetail
public import LpSelfSimilar.Bernoulli.IntegratedEnvelopeComparison
public import LpSelfSimilar.Bernoulli.IntegratedEnvelopeSmallness

@[expose] public section

/-!
# The actual integrated Bernoulli detail is smaller than one hundredth of the gap

All ingredients now concern the actual constructed measure and kernel: the
scale integral, the explicit packing coefficient, the uniform envelope and its
certified endpoint bound. This is the quantitative input for removing smoothing;
existence or regularity of a density is not assumed or concluded here.
-/

open MeasureTheory Set
open LpSelfSimilar.Analysis LpSelfSimilar.Entropy

namespace LpSelfSimilar.Bernoulli

/-- Actual integrability and strict scale-integral smallness under the full working criterion. -/
theorem bernoulli_integrated_detail_lt_gap_div_hundred {θ ρ L : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hgap : -Real.log θ ≤ 1 / 250)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L)
    (hC : Real.log (2 / (1 - θ) + 2) / Real.log 2 ≤ L + 2)
    (hsmall : (-Real.log θ) * (packingLogScale (L / ρ)) ^ 2 ≤ ρ / 2)
    (hentropy : ∀ n : ℕ, 0 < n →
      ρ * n ≤ finiteEntropy (digitPMF θ n) (digitPMF_support_finite θ n) / Real.log 2)
    (hsep : ∀ n : ℕ, 0 < n → ∀ x ∈ (digitPMF θ n).support,
      ∀ y ∈ (digitPMF θ n).support, x ≠ y → (2 : ℝ) ^ (-(L * n)) ≤ |x - y|) :
    let χ := -Real.log θ
    let ψ := Fourier.angularInverseFourier
      (fun ξ ↦ (Fourier.quinticFourierDetail (packingFrequencyWidth (L / ρ)) ξ : ℂ))
    let d := fun r : ℝ => ∫ x, ‖measureFunctionConvolution (convolution θ) (rescaledKernel r ψ) x‖
    IntegrableOn (fun r => d r / r) (Ioc 0 χ) volume ∧
      (∫ r in Ioc 0 χ, d r / r) < χ / 100 := by
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  have hbase := bernoulli_integrated_detail_bound
    hθ0 hθ1 hgap hρ hρ1 hL hC hsmall hentropy hsep
  have hnorm := bernoulli_integrated_detail_div_gap_bound
    hθ0 hθ1 hgap hρ hρ1 hL hC hsmall hentropy hsep
  have hlt := (hnorm.trans (integrated_coefficient_le_envelope hχ hρ hρ1 hL hsmall)).trans_lt
    (integratedDetailEnvelope_lt_one_hundredth hχ hgap)
  refine ⟨hbase.1, ?_⟩
  convert! (div_lt_iff₀ hχ).mp hlt using 1 <;> ring

end LpSelfSimilar.Bernoulli
