module

public import LpSelfSimilar.Entropy.Grid
public import Mathlib.Data.Int.Interval

@[expose] public section

/-!
Cardinality and entropy estimates for quantizing a law supported in an interval.
Both the real length bound and the sharp integer-multiple bound are useful:
an interval of length at most four fine-grid cells meets at most five cells.
-/

open MeasureTheory Set Real
open scoped ENNReal

namespace LpSelfSimilar.Entropy

lemma grid_support_subset_interval (p : PMF ℝ) {A B s : ℝ}
    (hAB : p.support ⊆ Icc A B) (hs : 0 < s) (t : ℝ) :
    (p.map (quantize s t)).support ⊆ Icc (quantize s t A) (quantize s t B) := by
  intro z hz
  rw [PMF.support_map] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  obtain ⟨hAx, hxB⟩ := hAB hx
  constructor <;> apply Int.floor_mono
  · linarith [div_le_div_of_nonneg_right hAx hs.le]
  · linarith [div_le_div_of_nonneg_right hxB hs.le]

lemma grid_card_le_length (p : PMF ℝ) (hp : p.support.Finite) {A B s : ℝ}
    (hAB : p.support ⊆ Icc A B) (hs : 0 < s) (t : ℝ) :
    ((show (p.map (quantize s t)).support.Finite from by
      simpa using hp.image (quantize s t)).toFinset.card : ℝ) ≤ (B - A) / s + 2 := by
  let hq : (p.map (quantize s t)).support.Finite := by simpa using hp.image (quantize s t)
  have hsub : hq.toFinset ⊆ Finset.Icc (quantize s t A) (quantize s t B) := by
    intro z hz
    simpa using grid_support_subset_interval p hAB hs t (by simpa using hz)
  obtain ⟨x, hx⟩ := p.support_nonempty
  have hle : quantize s t A ≤ quantize s t B := by
    apply Int.floor_mono
    linarith [div_le_div_of_nonneg_right ((hAB hx).1.trans (hAB hx).2) hs.le]
  have hc : (hq.toFinset.card : ℤ) ≤ (Finset.Icc (quantize s t A) (quantize s t B)).card := by
    exact_mod_cast Finset.card_le_card hsub
  rw [Int.card_Icc_of_le (a := quantize s t A) (b := quantize s t B) (by omega)] at hc
  have hcr : (hq.toFinset.card : ℝ) ≤
      (quantize s t B : ℝ) + 1 - (quantize s t A : ℝ) := by exact_mod_cast hc
  have hL := Int.lt_floor_add_one (A / s + t)
  have hU := Int.floor_le (B / s + t)
  change (hq.toFinset.card : ℝ) ≤ _
  dsimp [quantize] at hcr
  rw [sub_div]
  linarith

lemma gridEntropyAt_le_log_length (p : PMF ℝ) (hp : p.support.Finite) {A B s : ℝ}
    (hAB : p.support ⊆ Icc A B) (hs : 0 < s) (t : ℝ) :
    gridEntropyAt p hp s t ≤ Real.log ((B - A) / s + 2) := by
  apply (finiteEntropy_le_log_card _ _).trans
  apply Real.log_le_log
  · exact_mod_cast Finset.card_pos.mpr (by simpa using (p.map (quantize s t)).support_nonempty)
  · exact grid_card_le_length p hp hAB hs t

lemma gridEntropy_le_log_length (p : PMF ℝ) (hp : p.support.Finite) {A B s : ℝ}
    (hAB : p.support ⊆ Icc A B) (hs : 0 < s) :
    gridEntropy p hp s ≤ Real.log ((B - A) / s + 2) := by
  calc
    gridEntropy p hp s ≤ ∫ _ in Icc (0 : ℝ) 1, Real.log ((B - A) / s + 2) := by
      apply integral_mono (integrable_gridEntropyAt p hp s) (integrable_const _)
      exact fun t ↦ gridEntropyAt_le_log_length p hp hAB hs t
    _ = _ := by simp

lemma grid_card_le_of_length_le_nat (p : PMF ℝ) (hp : p.support.Finite) {A B s : ℝ}
    (hAB : p.support ⊆ Icc A B) (hs : 0 < s) (n : ℕ) (hlen : B - A ≤ n * s) (t : ℝ) :
    (show (p.map (quantize s t)).support.Finite from by
      simpa using hp.image (quantize s t)).toFinset.card ≤ n + 1 := by
  let hq : (p.map (quantize s t)).support.Finite := by simpa using hp.image (quantize s t)
  have hsub : hq.toFinset ⊆ Finset.Icc (quantize s t A) (quantize s t A + n) := by
    intro z hz
    have hz' : z ∈ (p.map (quantize s t)).support := by simpa using hz
    rw [PMF.support_map] at hz'
    obtain ⟨x, hx, rfl⟩ := hz'
    obtain ⟨hAx, hxB⟩ := hAB hx
    simp only [Finset.mem_Icc]
    constructor
    · apply Int.floor_mono
      linarith [div_le_div_of_nonneg_right hAx hs.le]
    · change ⌊x / s + t⌋ ≤ ⌊A / s + t⌋ + n
      rw [← Int.floor_add_natCast]
      apply Int.floor_mono
      have hx' : x ≤ A + n * s := by linarith
      have h := div_le_div_of_nonneg_right hx' hs.le
      rw [add_div, mul_div_cancel_right₀ _ hs.ne'] at h
      linarith
  apply (Finset.card_le_card hsub).trans
  rw [Int.card_Icc]
  omega

end LpSelfSimilar.Entropy
