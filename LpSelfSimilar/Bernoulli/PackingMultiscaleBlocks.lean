module

public import LpSelfSimilar.Bernoulli.PackingLengths
public import LpSelfSimilar.Bernoulli.PackingNaturalBlocks
public import LpSelfSimilar.Bernoulli.PackingAttenuation
public import LpSelfSimilar.Bernoulli.PackingLengthSeparation
public import Mathlib.Data.Finset.Sigma

@[expose] public section

/-!
# The finite multiscale digit packing

At each of the exactly permitted geometric lengths we choose the already proved
natural block family. Their finite dependent union retains each block once.
Coordinate windows prove disjointness between different lengths, while the
single-length construction supplies disjointness within a length. Summing the
actual counts and attenuations gives the quantitative bounds of Lemma 4.2.
-/

open MeasureTheory Set
open scoped BigOperators
open LpSelfSimilar.Analysis LpSelfSimilar.Entropy

namespace LpSelfSimilar.Bernoulli

/-- The complete finite multiscale family has disjoint digits, the stated count and attenuation,
and the actual conditional-law support and Fourier bounds. -/
theorem exists_packing_multiscale_blocks {θ ρ L R : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hgap : -Real.log θ ≤ 1 / 250) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L)
    (hC : Real.log (2 / (1 - θ) + 2) / Real.log 2 ≤ L + 2)
    (hsmall : (-Real.log θ) * (packingLogScale (L / ρ)) ^ 2 ≤ ρ / 2)
    (hR : packingScaleThreshold (-Real.log θ) ρ L ≤ R)
    (hentropy : ∀ n : ℕ, 0 < n →
      ρ * n ≤ finiteEntropy (digitPMF θ n) (digitPMF_support_finite θ n) / Real.log 2)
    (hsep : ∀ n : ℕ, 0 < n → ∀ x ∈ (digitPMF θ n).support,
      ∀ y ∈ (digitPMF θ n).support, x ≠ y → (2 : ℝ) ^ (-(L * n)) ≤ |x - y|) :
    let T := packingLengthCount (-Real.log θ) ρ L R
    let len : (Σ _ : Fin T, ℕ) → ℕ := fun i ↦ packingBlockLength (-Real.log θ) (L / ρ) i.1
    ∃ (S : Finset (Σ _ : Fin T, ℕ)) (j : (Σ _ : Fin T, ℕ) → ℝ)
      (start : (Σ _ : Fin T, ℕ) → ℕ),
      (S.card : ℝ) ≤ L * T / (-Real.log θ) ∧
      (∀ i ∈ S, 0 < digitGridAttenuation θ (packingFrequencyWidth (L / ρ)) (len i) (j i)) ∧
      (∀ k : Fin T, ∃ i ∈ S, i.1 = k) ∧
      (∀ i ∈ S, ∀ l ∈ S, i ≠ l →
        Disjoint (Finset.Ico (start i) (start i + len i))
          (Finset.Ico (start l) (start l + len l))) ∧
      (∀ i ∈ S, ∀ d < len i, 2 < R - (-Real.log θ / Real.log 2) * (start i + d : ℕ)) ∧
      packingAttenuation (-Real.log θ) ρ L * T ≤
        ∑ i ∈ S, digitGridAttenuation θ (packingFrequencyWidth (L / ρ)) (len i) (j i) ∧
      (∀ i ∈ S, ∀ ξ : ℝ, abs (|ξ| - 1) ≤ packingFrequencyWidth (L / ρ) →
        (∑ label, digitBandLabelWeight θ (len i) (j i) label *
          ‖charFun (digitBandShiftedLaw θ (len i) (j i) (start i : ℤ) label)
            (ξ / (2 : ℝ) ^ (-R))‖) ≤
          1 - digitGridAttenuation θ (packingFrequencyWidth (L / ρ)) (len i) (j i)) ∧
      (∀ i ∈ S, ∀ label, ∃ b : ℝ,
        ((digitBandShiftedLaw θ (len i) (j i) (start i : ℤ) label).map (fun x ↦ x - b))
          (Icc 0 (52 * (2 : ℝ) ^ (-R))) = 1) := by
  classical
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  have hJ := three_le_separation_entropy_ratio hρ hρ1 hL
  let T := packingLengthCount (-Real.log θ) ρ L R
  let n : Fin T → ℕ := fun k ↦ packingBlockLength (-Real.log θ) (L / ρ) k
  have hn (k : Fin T) : packingBaseLength (-Real.log θ) (L / ρ) ≤ n k :=
    packingBaseLength_le_blockLength _ hJ k
  have hn0 (k : Fin T) : 0 < n k := packingBlockLength_pos hχ hJ k
  have hfit (k : Fin T) : 4 * (L + 1) * n k ≤ R :=
    (lt_packingLengthCount_iff hχ hρ hρ1 hL hR k).mp k.isLt
  have hex (k : Fin T) := exists_packing_natural_blocks hθ0 hθ1 hgap hρ hρ1 hL hC
    (n k) (hn k) (hfit k) (hentropy (n k) (hn0 k)) (hsep (n k) (hn0 k))
  choose I j start H using hex
  let S : Finset (Σ _ : Fin T, ℕ) := Finset.univ.sigma I
  have ha : 0 < packingAttenuation (-Real.log θ) ρ L := by
    have ht := six_lt_packingLogScale hJ
    have hta := packingLogScale_lt_attenuation hχ hρ hρ1 hL hsmall
    linarith
  have hmem (i : Σ _ : Fin T, ℕ) (hi : i ∈ S) : i.2 ∈ I i.1 := (Finset.mem_sigma.mp hi).2
  have hcross {k l : Fin T} (hkl : k < l) (i q : ℕ) (hi : i ∈ I k) (hq : q ∈ I l) :
      Disjoint (Finset.Ico (start k i) (start k i + n k))
        (Finset.Ico (start l q) (start l q + n l)) := by
    apply Finset.disjoint_left.mpr
    intro d hdi hdq
    have hdi' := Finset.mem_Ico.mp hdi
    have hdq' := Finset.mem_Ico.mp hdq
    have hc := (H k).2.2.2.1 i hi (d - start k i) (by omega)
    have hc' := (H l).2.2.2.1 q hq (d - start l q) (by omega)
    rw [Nat.add_sub_of_le hdi'.1] at hc
    rw [Nat.add_sub_of_le hdq'.1] at hc'
    have hsep' := packing_length_windows_separated hχ hgap hρ hρ1 hL hsmall
      (n k) (n l) (hn k) (packingBlockLength_step_le _ hJ (show k.val < l.val from hkl))
    linarith [hc.2, hc'.1]
  refine ⟨S, (fun i ↦ j i.1 i.2), (fun i ↦ start i.1 i.2), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (S.card : ℝ) ≤ L * T / (-Real.log θ)
    calc
      (S.card : ℝ) = ∑ k, ((I k).card : ℝ) := by simp [S, Finset.card_sigma, Nat.cast_sum]
      _ ≤ ∑ _k : Fin T, L / (-Real.log θ) :=
        Finset.sum_le_sum (fun k _ ↦ (H k).1)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  · intro i hi
    exact ((H i.1).2.1 i.2 (hmem i hi)).2
  · intro k
    have hI : (I k).Nonempty := by
      by_contra he
      have he' : I k = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
      have hb := (H k).2.2.2.2.1
      rw [he', Finset.sum_empty] at hb
      exact (lt_irrefl 0) (ha.trans_le hb)
    obtain ⟨i, hi⟩ := hI
    exact ⟨⟨k, i⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ k, hi⟩, rfl⟩
  · intro a ha b hb hab
    obtain ⟨k, i⟩ := a
    obtain ⟨l, q⟩ := b
    have hi := hmem ⟨k, i⟩ ha
    have hq := hmem ⟨l, q⟩ hb
    by_cases hkl : k = l
    · subst l
      exact (H k).2.2.1 i hi q hq (by intro he; apply hab; cases he; rfl)
    · rcases lt_or_gt_of_ne hkl with h | h
      · exact hcross h i q hi hq
      · exact (hcross h q i hq hi).symm
  · intro i hi d hd
    exact (packing_window_lower_gt_two hχ hgap hρ hρ1 hL hsmall (n i.1) (hn i.1)).trans
      ((H i.1).2.2.2.1 i.2 (hmem i hi) d hd).1
  · change packingAttenuation (-Real.log θ) ρ L * T ≤
      ∑ i ∈ Finset.univ.sigma I,
        digitGridAttenuation θ (packingFrequencyWidth (L / ρ)) (n i.1) (j i.1 i.2)
    rw [Finset.sum_sigma]
    calc
      _ = ∑ _k : Fin T, packingAttenuation (-Real.log θ) ρ L := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      _ ≤ _ := Finset.sum_le_sum (fun k _ ↦ (H k).2.2.2.2.1)
  · intro i hi ξ hξ
    exact (H i.1).2.2.2.2.2.1 i.2 (hmem i hi) ξ hξ
  · intro i hi label
    exact (H i.1).2.2.2.2.2.2 i.2 (hmem i hi) label

end LpSelfSimilar.Bernoulli
