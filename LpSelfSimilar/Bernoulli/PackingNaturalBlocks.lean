module

public import LpSelfSimilar.Bernoulli.PackingGridSelection
public import LpSelfSimilar.Bernoulli.PackingBlockWindows
public import LpSelfSimilar.Bernoulli.DigitBlockMixtures
public import LpSelfSimilar.Fourier.BandGridIndices

@[expose] public section

/-!
# A complete family of natural digit blocks at one length

The retained grid and its common phase shifts are chosen before the conditional
labels. The scale cutoff proves nonnegativity of every integer shift before it
is converted to a natural digit index. Exact grid spacing then proves disjointness
of the actual natural intervals. The Fourier and support conclusions concern the
original shifted conditional probability laws, including zero-weight labels.
-/

open MeasureTheory Set
open scoped BigOperators
open LpSelfSimilar.Analysis LpSelfSimilar.Entropy LpSelfSimilar.Fourier

namespace LpSelfSimilar.Bernoulli

/-- One admissible length supplies disjoint actual digit blocks with its full attenuation budget. -/
theorem exists_packing_natural_blocks {θ ρ L R : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hgap : -Real.log θ ≤ 1 / 250) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L)
    (hC : Real.log (2 / (1 - θ) + 2) / Real.log 2 ≤ L + 2)
    (n : ℕ) (hn : packingBaseLength (-Real.log θ) (L / ρ) ≤ n)
    (hR : 4 * (L + 1) * n ≤ R)
    (hentropy : ρ * n ≤ finiteEntropy (digitPMF θ n) (digitPMF_support_finite θ n) / Real.log 2)
    (hsep : ∀ x ∈ (digitPMF θ n).support, ∀ y ∈ (digitPMF θ n).support, x ≠ y →
      (2 : ℝ) ^ (-(L * n)) ≤ |x - y|) :
    ∃ (I : Finset ℕ) (j : ℕ → ℝ) (start : ℕ → ℕ),
      (I.card : ℝ) ≤ L / (-Real.log θ) ∧
      (∀ i ∈ I, j i ∈ Icc ((4 / 25 : ℝ) * ρ * n) (L * n + 4) ∧
        0 < digitGridAttenuation θ (packingFrequencyWidth (L / ρ)) n (j i)) ∧
      (∀ i ∈ I, ∀ l ∈ I, i ≠ l →
        Disjoint (Finset.Ico (start i) (start i + n)) (Finset.Ico (start l) (start l + n))) ∧
      (∀ i ∈ I, ∀ d < n,
        ((4 / 25 : ℝ) * ρ - (-Real.log θ / Real.log 2)) * n - 30 <
          R - (-Real.log θ / Real.log 2) * (start i + d : ℕ) ∧
        R - (-Real.log θ / Real.log 2) * (start i + d : ℕ) ≤ L * n + 34) ∧
      packingAttenuation (-Real.log θ) ρ L ≤
        ∑ i ∈ I, digitGridAttenuation θ (packingFrequencyWidth (L / ρ)) n (j i) ∧
      (∀ i ∈ I, ∀ ξ : ℝ, abs (|ξ| - 1) ≤ packingFrequencyWidth (L / ρ) →
        (∑ label, digitBandLabelWeight θ n (j i) label *
          ‖charFun (digitBandShiftedLaw θ n (j i) (start i : ℤ) label)
            (ξ / (2 : ℝ) ^ (-R))‖) ≤
          1 - digitGridAttenuation θ (packingFrequencyWidth (L / ρ)) n (j i)) ∧
      (∀ i ∈ I, ∀ label, ∃ b : ℝ,
        ((digitBandShiftedLaw θ n (j i) (start i : ℤ) label).map (fun x ↦ x - b))
          (Icc 0 (52 * (2 : ℝ) ^ (-R))) = 1) := by
  classical
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  have hJ := three_le_separation_entropy_ratio hρ hρ1 hL
  have hn0 := (packingBaseLength_pos hχ hJ).trans_le hn
  obtain ⟨t, I, hcard, hgrid, hbudget⟩ :=
    exists_retained_packing_grid hθ0 hθ1 hgap hρ hρ1 hL hC n hn hentropy hsep
  let j : ℕ → ℝ := fun i ↦
    packingGridSpacing (-Real.log θ) n (geometricPhaseLength θ) * ((i : ℝ) + t)
  have hex (i : ℕ) := exists_digit_band_block hθ0 hθ1
    (by linarith : -Real.log θ ≤ 1 / 70) n (j i)
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-R))
  choose k hk using hex
  let first : ℕ → ℤ := fun i ↦ bandFirstShift θ ((2 : ℝ) ^ (-(j i))) ((2 : ℝ) ^ (-R))
  let m : ℕ → ℤ := fun i ↦ first i + (k i).val
  let start : ℕ → ℕ := fun i ↦ (m i).toNat
  have hkmax (i : ℕ) : (k i).val ≤ geometricPhaseLength θ := Nat.le_of_lt_succ (k i).isLt
  have hcast (i : ℕ) (hi : i ∈ I) : (start i : ℤ) = m i := by
    apply Int.toNat_of_nonneg
    have hf := packing_band_first_shift_nonneg hθ0 hθ1 hgap hL n hn0 (j i) R
      (hgrid i hi).1.2 hR
    dsimp [m, first]
    omega
  have hordered (i l : ℕ) (hi : i ∈ I) (hl : l ∈ I) (hil : i < l) :
      start l + n ≤ start i := by
    have hg := bandFirstShift_grid_gap hθ0 hθ1
      (n + geometricPhaseLength θ + 2) t R hil
    have hg' : first l + (n : ℤ) + geometricPhaseLength θ + 2 ≤ first i := by
      simpa only [first, j, packingGridSpacing, Nat.cast_add, Nat.cast_ofNat, add_assoc] using hg
    have hci := hcast i hi
    have hcl := hcast l hl
    have hkl := hkmax l
    dsimp [m] at hci hcl
    omega
  refine ⟨I, j, start, hcard, hgrid, ?_, ?_, hbudget, ?_, ?_⟩
  · intro i hi l hl hil
    apply Finset.disjoint_left.mpr
    intro d hdi hdl
    have hdi' := Finset.mem_Ico.mp hdi
    have hdl' := Finset.mem_Ico.mp hdl
    rcases lt_or_gt_of_ne hil with h | h
    · have hs := hordered i l hi hl h
      omega
    · have hs := hordered l i hl hi h
      omega
  · intro i hi d hd
    have hw := packing_digit_coordinate_window hθ0 hθ1 hgap n (j i) R
      (hgrid i hi).1 (k i).val d (hkmax i) hd
    change _ < R - (-Real.log θ / Real.log 2) * ((m i + (d : ℤ) : ℤ) : ℝ) ∧
      R - (-Real.log θ / Real.log 2) * ((m i + (d : ℤ) : ℤ) : ℝ) ≤ _ at hw
    rw [← hcast i hi] at hw
    simpa only [Int.cast_add, Int.cast_natCast, Nat.cast_add] using hw
  · intro i hi ξ hξ
    have hf := (hk i).1 ξ (packingFrequencyWidth (L / ρ)) hξ
    change (∑ label, digitBandLabelWeight θ n (j i) label *
      ‖charFun (digitBandShiftedLaw θ n (j i) (m i) label) (ξ / (2 : ℝ) ^ (-R))‖) ≤ _ at hf
    rw [← hcast i hi] at hf
    have hg := (hgrid i hi).2
    change 0 < max (digitBandCancellation θ n (j i) - 52 * packingFrequencyWidth (L / ρ)) 0 at hg
    have hp : 0 < digitBandCancellation θ n (j i) - 52 * packingFrequencyWidth (L / ρ) :=
      (lt_max_iff.mp hg).resolve_right (lt_irrefl 0)
    rw [digitGridAttenuation, max_eq_left hp.le]
    linarith
  · intro i hi label
    obtain ⟨b, hb⟩ := (hk i).2 label
    refine ⟨b, ?_⟩
    change ((digitBandShiftedLaw θ n (j i) (m i) label).map (fun x ↦ x - b)) _ = 1 at hb
    rw [← hcast i hi] at hb
    exact hb

end LpSelfSimilar.Bernoulli
