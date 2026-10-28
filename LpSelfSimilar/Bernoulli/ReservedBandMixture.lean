module

public import LpSelfSimilar.Bernoulli.BandMixtureProducts
public import LpSelfSimilar.Bernoulli.ReservedBlockTail

@[expose] public section

/-!
# Keeping the reserved tail in the original conditional mixture

The actual independent block factorization is refined to separate the specified
infinite tail. Replacing each original block by its conditional mixture keeps
the original product label law and leaves an actual unused-prefix probability
measure. No translated mixture is identified with the original law.
-/

open MeasureTheory MeasureTheory.Measure

namespace LpSelfSimilar.Bernoulli

/-- Original-label conditional blocks before a specified tail retain that exact tail as a factor. -/
theorem convolution_eq_disjoint_band_mixture_before {θ : ℝ} (hθ : |θ| < 1) {m : ℕ}
    (start len : Fin m → ℕ) (j : Fin m → ℝ) (tail : ℕ)
    (hend : ∀ i, start i + len i ≤ tail)
    (hd : ∀ i l, i ≠ l → Disjoint
      (Finset.Ico (start i) (start i + len i)) (Finset.Ico (start l) (start l + len l))) :
    ∃ η : Measure ℝ, IsProbabilityMeasure η ∧
      convolution θ =
        (pmfMixture (productPMF (fun i ↦ digitBandLabelPMF θ (len i) (j i)))
          (fun ω ↦ finiteConvolution
            (fun i ↦ digitBandShiftedLaw θ (len i) (j i) (start i : ℤ) (ω i))) ∗ η) ∗
              (convolution θ).map (fun y ↦ θ ^ tail * y) := by
  classical
  obtain ⟨η, hη, heq⟩ := convolution_disjoint_blocks_before Finset.univ start len hθ tail
    (fun i hi ↦ hend i) (fun i hi l hl hil ↦ hd i l hil)
  rw [finsetConvolution_univ_fin] at heq
  have he : (fun i ↦ (blockPMF θ (start i) (len i)).toMeasure) =
      (fun i ↦ pmfMixture (digitBandLabelPMF θ (len i) (j i))
        (digitBandShiftedLaw θ (len i) (j i) (start i : ℤ))) :=
    funext (fun i ↦ blockPMF_eq_band_pmfMixture θ (start i) (len i) (j i))
  rw [he, finiteConvolution_pmfMixture] at heq
  exact ⟨η, hη, heq⟩

end LpSelfSimilar.Bernoulli
