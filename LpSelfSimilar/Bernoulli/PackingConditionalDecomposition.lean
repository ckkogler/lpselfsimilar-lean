module

public import LpSelfSimilar.Bernoulli.PackingMultiscaleBlocks
public import LpSelfSimilar.Bernoulli.PackingAttenuationRange
public import LpSelfSimilar.Bernoulli.BandMixtureProducts
public import LpSelfSimilar.Probability.IntervalRescaling

@[expose] public section

/-!
# The actual independent conditional decomposition from digit packing

The finite multiscale family is enumerated without repetition and each original
block law is replaced by its proved conditional mixture. The complete Bernoulli
convolution is exactly that product-label mixture convolved with a probability
remainder containing all unused digits. The attenuation, count, reserved-index
and normalized support bounds are derived from the numerical and finite-digit
entropy/separation hypotheses of the working criterion.
-/

open MeasureTheory MeasureTheory.Measure Set
open scoped BigOperators
open LpSelfSimilar.Analysis LpSelfSimilar.Entropy

namespace LpSelfSimilar.Bernoulli

/-- Full conditional digit-packing decomposition, with the exact finite length count and constants. -/
theorem exists_packing_conditional_decomposition {θ ρ L R : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hgap : -Real.log θ ≤ 1 / 250) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L)
    (hC : Real.log (2 / (1 - θ) + 2) / Real.log 2 ≤ L + 2)
    (hsmall : (-Real.log θ) * (packingLogScale (L / ρ)) ^ 2 ≤ ρ / 2)
    (hR : packingScaleThreshold (-Real.log θ) ρ L ≤ R)
    (hentropy : ∀ n : ℕ, 0 < n →
      ρ * n ≤ finiteEntropy (digitPMF θ n) (digitPMF_support_finite θ n) / Real.log 2)
    (hsep : ∀ n : ℕ, 0 < n → ∀ x ∈ (digitPMF θ n).support,
      ∀ y ∈ (digitPMF θ n).support, x ≠ y → (2 : ℝ) ^ (-(L * n)) ≤ |x - y|) :
    let T := packingLengthCount (-Real.log θ) ρ L R
    ∃ (m : ℕ) (scale : Fin m → Fin T) (j : Fin m → ℝ) (start : Fin m → ℕ) (η : Measure ℝ),
      let len := fun i ↦ packingBlockLength (-Real.log θ) (L / ρ) (scale i)
      let b := fun i ↦ digitGridAttenuation θ (packingFrequencyWidth (L / ρ)) (len i) (j i)
      (m : ℝ) ≤ L * T / (-Real.log θ) ∧
      (∀ i, 0 < b i ∧ b i ≤ 1 - Real.sqrt (7 / 16)) ∧
      Function.Surjective scale ∧
      (∀ i l, i ≠ l → Disjoint
        (Finset.Ico (start i) (start i + len i)) (Finset.Ico (start l) (start l + len l))) ∧
      (∀ i, ∀ d < len i, 2 < R - (-Real.log θ / Real.log 2) * (start i + d : ℕ)) ∧
      packingAttenuation (-Real.log θ) ρ L * T ≤ ∑ i, b i ∧
      (∀ i, ∀ ξ : ℝ, abs (|ξ| - 1) ≤ packingFrequencyWidth (L / ρ) →
        (∑ label, digitBandLabelWeight θ (len i) (j i) label *
          ‖charFun (digitBandShiftedLaw θ (len i) (j i) (start i : ℤ) label)
            (ξ / (2 : ℝ) ^ (-R))‖) ≤ 1 - b i) ∧
      (∀ i, ∀ label, ∃ c : ℝ,
        ((digitBandShiftedLaw θ (len i) (j i) (start i : ℤ) label).map
          (fun x ↦ (x - c) / (2 : ℝ) ^ (-R))) (Icc 0 52) = 1) ∧
      IsProbabilityMeasure η ∧
      convolution θ =
        pmfMixture (productPMF (fun i ↦ digitBandLabelPMF θ (len i) (j i)))
          (fun ω ↦ finiteConvolution
            (fun i ↦ digitBandShiftedLaw θ (len i) (j i) (start i : ℤ) (ω i))) ∗ η ∧
      (∀ ξ : ℝ, abs (|ξ| - 1) ≤ packingFrequencyWidth (L / ρ) →
        (∫ ω, ‖charFun (finiteConvolution
          (fun i ↦ digitBandShiftedLaw θ (len i) (j i) (start i : ℤ) (ω i)))
          (ξ / (2 : ℝ) ^ (-R))‖
          ∂(productPMF (fun i ↦ digitBandLabelPMF θ (len i) (j i))).toMeasure) ≤
            Real.exp (-(packingAttenuation (-Real.log θ) ρ L * T))) := by
  classical
  let T := packingLengthCount (-Real.log θ) ρ L R
  let len : (Σ _ : Fin T, ℕ) → ℕ := fun i ↦ packingBlockLength (-Real.log θ) (L / ρ) i.1
  obtain ⟨S, j, start, hcard, hpos, hgroups, hd, hc, hbudget, hf, hs⟩ :=
    exists_packing_multiscale_blocks hθ0 hθ1 hgap hρ hρ1 hL hC hsmall hR hentropy hsep
  let m := Fintype.card S
  let e : Fin m ≃ S := (Fintype.equivFin S).symm
  let ix : Fin m → (Σ _ : Fin T, ℕ) := fun i ↦ (e i).val
  let scale : Fin m → Fin T := fun i ↦ (ix i).1
  let j' : Fin m → ℝ := fun i ↦ j (ix i)
  let start' : Fin m → ℕ := fun i ↦ start (ix i)
  let len' : Fin m → ℕ := fun i ↦ len (ix i)
  let b : Fin m → ℝ := fun i ↦
    digitGridAttenuation θ (packingFrequencyWidth (L / ρ)) (len' i) (j' i)
  have hmem (i : Fin m) : ix i ∈ S := (e i).property
  have hinj : Function.Injective ix := by
    intro i l hil
    exact e.injective (Subtype.ext hil)
  have hsum (f : (Σ _ : Fin T, ℕ) → ℝ) : (∑ i : Fin m, f (ix i)) = ∑ i ∈ S, f i := by
    change (∑ i : Fin m, (fun a : S ↦ f a) (e i)) = _
    rw [e.sum_comp (fun a : S ↦ f a)]
    simpa using (Finset.sum_attach S f)
  have hd' (i l : Fin m) (hil : i ≠ l) : Disjoint
      (Finset.Ico (start' i) (start' i + len' i)) (Finset.Ico (start' l) (start' l + len' l)) :=
    hd (ix i) (hmem i) (ix l) (hmem l) (fun he ↦ hil (hinj he))
  obtain ⟨η, hη, heq⟩ := convolution_eq_disjoint_band_mixture
    (show |θ| < 1 by rwa [abs_of_pos hθ0]) start' len' j' hd'
  have hbudget' : packingAttenuation (-Real.log θ) ρ L * T ≤ ∑ i, b i := by
    change _ ≤ ∑ i, (fun a ↦ digitGridAttenuation θ (packingFrequencyWidth (L / ρ)) (len a) (j a)) (ix i)
    rw [hsum (fun a ↦ digitGridAttenuation θ (packingFrequencyWidth (L / ρ)) (len a) (j a))]
    exact hbudget
  have hf' (i : Fin m) (ξ : ℝ) (hξ : abs (|ξ| - 1) ≤ packingFrequencyWidth (L / ρ)) :
      (∑ label, digitBandLabelWeight θ (len' i) (j' i) label *
        ‖charFun (digitBandShiftedLaw θ (len' i) (j' i) (start' i : ℤ) label)
          (ξ / (2 : ℝ) ^ (-R))‖) ≤ 1 - b i := hf (ix i) (hmem i) ξ hξ
  refine ⟨m, scale, j', start', η, ?_, ?_, ?_, hd', ?_, hbudget', hf', ?_, hη, heq, ?_⟩
  · simpa only [m, Fintype.card_coe] using hcard
  · intro i
    exact ⟨hpos (ix i) (hmem i), (digitGridAttenuation_mem_exact_Icc θ
      (packingFrequencyWidth_pos (three_le_separation_entropy_ratio hρ hρ1 hL)).le
      (len' i) (j' i)).2⟩
  · intro k
    obtain ⟨a, ha, hak⟩ := hgroups k
    refine ⟨e.symm ⟨a, ha⟩, ?_⟩
    change (↑(e (e.symm ⟨a, ha⟩)) : (Σ _ : Fin T, ℕ)).1 = k
    simpa only [Equiv.apply_symm_apply] using hak
  · intro i d hdi
    exact hc (ix i) (hmem i) d hdi
  · intro i label
    obtain ⟨c, hc⟩ := hs (ix i) (hmem i) label
    refine ⟨c, ?_⟩
    rw [map_sub_div_Icc _ c 52 (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-R))]
    exact hc
  · intro ξ hξ
    exact (integral_norm_charFun_band_product_le_exp θ start' len' j' b
      (ξ / (2 : ℝ) ^ (-R)) (fun i ↦ hf' i ξ hξ)).trans
        (Real.exp_le_exp.mpr (neg_le_neg hbudget'))

end LpSelfSimilar.Bernoulli
