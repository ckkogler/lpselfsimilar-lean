module

public import LpSelfSimilar.Algebraic.BlockVariance
public import LpSelfSimilar.Analysis.ShiftedGridAverage

@[expose] public section

/-!
A deterministic arithmetic grid carrying the algebraic block variance. Averaging
translates of a grid of spacing length times logarithmic contraction converts
Lemma 3.7 into the one-length input of Proposition 3.8.
-/

open MeasureTheory Set Real
open LpSelfSimilar.Bernoulli LpSelfSimilar.Entropy

namespace LpSelfSimilar.Algebraic

/-- One length supplies variance of order `1/(χ B^7)` on a grid of spacing `nχ`. -/
theorem exists_digit_variance_grid {r : ℝ} (hr : IsAlgebraic ℚ r)
    (hr0 : 0 < r) (hr1 : r < 1) {n : ℕ}
    (hn : 100 * complexity r ^ 2 ≤ n) {χ : ℝ} (hχ : 0 < χ) :
    ∃ (S : Finset ℕ) (t : ℝ),
      (∀ j ∈ S, (n : ℝ) * χ * ((j : ℝ) + t) ∈
        Icc ((n : ℝ) / (32 * complexity r)) (2 * complexity r * n)) ∧
      (1 / (10 : ℝ) ^ 10) / (χ * complexity r ^ 7) ≤
        ∑ j ∈ S, varianceOnLogScale (digitPMF r n)
          (digitPMF_support_finite _ _) ((n : ℝ) * χ * ((j : ℝ) + t)) := by
  classical
  let B := complexity r
  let p := digitPMF r n
  let hp := digitPMF_support_finite r n
  let V := varianceOnLogScale p hp
  let u := (n : ℝ) / (32 * B)
  let v := 2 * B * n
  let h := (n : ℝ) * χ
  have hB : 3 ≤ B := three_le_complexity hr hr0 hr1
  have hB0 : 0 < B := complexity_pos hr hr0 hr1
  have hn0 : 0 < (n : ℝ) := (by positivity : 0 < 100 * B ^ 2).trans_le hn
  have hh : 0 < h := by dsimp [h]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have huv : u ≤ v := by
    apply (div_le_iff₀ (by positivity : 0 < 32 * B)).mpr
    dsimp only [v]
    nlinarith [mul_nonneg hn0.le (show 0 ≤ B ^ 2 - 4 by nlinarith)]
  obtain ⟨N, hN⟩ := exists_nat_ge (v / h)
  have hcover : v ≤ h * (N : ℝ) := by
    have hn' := (div_le_iff₀ hh).mp hN
    nlinarith
  obtain ⟨t, ht⟩ := exists_shifted_grid_sum_ge V (measurable_varianceOnLogScale p hp)
    (fun x ↦ ⟨scaleVariance_nonneg p hp _, scaleVariance_le_one p hp (exp_pos _)⟩)
    hu huv hh N hcover
  let S := (Finset.range N).filter (fun j : ℕ ↦ h * ((j : ℝ) + t) ∈ Icc u v)
  refine ⟨S, t, ?_, ?_⟩
  · intro j hj
    exact (Finset.mem_filter.mp hj).2
  · have hi := digit_integral_variance_lower_bound hr hr0 hr1 hn
    have hmul := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 1 / h)
    have he : (1 / h) * ((n : ℝ) / ((10 : ℝ) ^ 10 * B ^ 7)) =
        (1 / (10 : ℝ) ^ 10) / (χ * B ^ 7) := by
      dsimp [h]
      field_simp
    rw [he] at hmul
    have ht' : (1 / (10 : ℝ) ^ 10) / (χ * B ^ 7) ≤
        ∑ j ∈ Finset.range N, if h * ((j : ℝ) + t) ∈ Icc u v
          then V (h * ((j : ℝ) + t)) else 0 := hmul.trans ht
    change (1 / (10 : ℝ) ^ 10) / (χ * B ^ 7) ≤ ∑ j ∈ S, V (h * ((j : ℝ) + t))
    dsimp only [S]
    rw [Finset.sum_filter]
    exact ht'

end LpSelfSimilar.Algebraic
