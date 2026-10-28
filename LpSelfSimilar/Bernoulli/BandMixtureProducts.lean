module

public import LpSelfSimilar.Bernoulli.DigitBlockMixtures
public import LpSelfSimilar.Probability.IndependentMixtures
public import LpSelfSimilar.Fourier.IndependentProducts

@[expose] public section

/-!
# Original-label products for disjoint Bernoulli digit blocks

The label PMFs retain the original maximizing-column masses. Their actual product
law supplies independent labels for the finite convolution of conditional laws.
Disjoint natural digit intervals give an exact factorization of the complete
Bernoulli convolution, including an actual probability remainder of unused digits.
-/

open MeasureTheory MeasureTheory.Measure
open scoped BigOperators

namespace LpSelfSimilar.Bernoulli

/-- Integration under the actual label PMF is exactly the original weighted Fourier average. -/
theorem integral_norm_charFun_digitBandLabelPMF (θ : ℝ) (n : ℕ) (j : ℝ) (m : ℤ) (s : ℝ) :
    (∫ label, ‖charFun (digitBandShiftedLaw θ n j m label) s‖ ∂(digitBandLabelPMF θ n j).toMeasure) =
      ∑ label, digitBandLabelWeight θ n j label * ‖charFun (digitBandShiftedLaw θ n j m label) s‖ := by
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul, digitBandLabelPMF_toReal]

/-- Disjoint actual digit blocks are a product-label conditional mixture times a probability remainder. -/
theorem convolution_eq_disjoint_band_mixture {θ : ℝ} (hθ : |θ| < 1) {m : ℕ}
    (start len : Fin m → ℕ) (j : Fin m → ℝ)
    (hd : ∀ i l, i ≠ l → Disjoint
      (Finset.Ico (start i) (start i + len i)) (Finset.Ico (start l) (start l + len l))) :
    ∃ η : Measure ℝ, IsProbabilityMeasure η ∧
      convolution θ =
        pmfMixture (productPMF (fun i ↦ digitBandLabelPMF θ (len i) (j i)))
          (fun ω ↦ finiteConvolution
            (fun i ↦ digitBandShiftedLaw θ (len i) (j i) (start i : ℤ) (ω i))) ∗ η := by
  classical
  obtain ⟨η, hη, heq⟩ := convolution_disjoint_blocks Finset.univ start len hθ
    (fun i _ l _ hil ↦ hd i l hil)
  rw [finsetConvolution_univ_fin] at heq
  have he : (fun i ↦ (blockPMF θ (start i) (len i)).toMeasure) =
      (fun i ↦ pmfMixture (digitBandLabelPMF θ (len i) (j i))
        (digitBandShiftedLaw θ (len i) (j i) (start i : ℤ))) :=
    funext (fun i ↦ blockPMF_eq_band_pmfMixture θ (start i) (len i) (j i))
  rw [he, finiteConvolution_pmfMixture] at heq
  exact ⟨η, hη, heq⟩

/-- Original weighted block attenuations imply the exponential bound under the actual product PMF. -/
theorem integral_norm_charFun_band_product_le_exp {m : ℕ} (θ : ℝ)
    (start len : Fin m → ℕ) (j b : Fin m → ℝ) (s : ℝ)
    (hb : ∀ i, (∑ label, digitBandLabelWeight θ (len i) (j i) label *
      ‖charFun (digitBandShiftedLaw θ (len i) (j i) (start i : ℤ) label) s‖) ≤ 1 - b i) :
    (∫ ω, ‖charFun (finiteConvolution
      (fun i ↦ digitBandShiftedLaw θ (len i) (j i) (start i : ℤ) (ω i))) s‖
      ∂(productPMF (fun i ↦ digitBandLabelPMF θ (len i) (j i))).toMeasure) ≤
        Real.exp (-∑ i, b i) := by
  apply Fourier.integral_norm_charFun_independent_product_le_exp
  intro i
  rw [integral_norm_charFun_digitBandLabelPMF]
  exact hb i

end LpSelfSimilar.Bernoulli
