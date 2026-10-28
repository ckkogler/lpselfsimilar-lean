module

public import LpSelfSimilar.Bernoulli.WeakSmoothing
public import LpSelfSimilar.Bernoulli.SharpTailDetail

@[expose] public section

/-!
Equation (3.5) with the revised explicit constant forty. A retained Bernoulli tail
has enough Gaussian variance; its centered replacement cost is at most fifteen
rather than thirty, so the proof first gives the stronger coefficient twenty-three.
All tail limits and discarded-factor convolution inequalities are proved upstream.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real

namespace LpSelfSimilar.Bernoulli

lemma detail_le_of_cube_eq_gap_explicit {l ε r : ℝ} (hl0 : 1 / 2 ≤ l) (hl1 : l < 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1)
    (hcube : ε ^ 3 = 1 - l) :
    Gaussian.detail (convolution l) r ≤ 23 * ε := by
  have hl : 0 < l := by linarith
  have htarget : ε * r ≤ 1 := (mul_le_mul hε1 hr1 hr.le (by norm_num)).trans (by norm_num)
  obtain ⟨n, hn, hprev⟩ := exists_nat_pow_near_of_lt_one (mul_pos hε hr) htarget hl hl1
  have ha : l * (ε * r) ≤ l ^ (n + 1) := by
    rw [pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left hprev hl.le]
  have htail := detail_scaled_convolution_le_fifteen hl.le hl1 (pow_nonneg hl.le _)
    hε.le hε1 hr hn.le
  have hfrac := gaussian_tail_fraction_le hl0 hl1 hε hr hcube ha
  have hdisc := detail_le_scaled_tail (l := l) (by simpa only [abs_of_pos hl] using hl1) hr (n + 1)
  linarith

/-- Equation (3.5), first in the stronger gap form. -/
theorem weak_smoothing_gap_explicit {l r : ℝ} (hl0 : 1 / 2 ≤ l) (hl1 : l < 1)
    (hr : 0 < r) (hr1 : r ≤ 1) :
    Gaussian.detail (convolution l) r ≤
      23 * (1 - l) ^ (1 / 3 : ℝ) := by
  have hg : 0 < 1 - l := by linarith
  have he : 0 < (1 - l) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hg _
  have he1 : (1 - l) ^ (1 / 3 : ℝ) ≤ 1 :=
    Real.rpow_le_one hg.le (by linarith) (by norm_num)
  have hcube : ((1 - l) ^ (1 / 3 : ℝ)) ^ 3 = 1 - l := by
    rw [← Real.rpow_mul_natCast hg.le]
    norm_num
  exact detail_le_of_cube_eq_gap_explicit hl0 hl1 he he1 hr hr1 hcube

/-- The paper's logarithmic parameter `χ = -log l`, with one absolute constant. -/
theorem weak_smoothing_twenty_three {l r : ℝ} (hl0 : 1 / 2 ≤ l) (hl1 : l < 1)
    (hr : 0 < r) (hr1 : r ≤ 1) :
    Gaussian.detail (convolution l) r ≤
      23 * (-Real.log l) ^ (1 / 3 : ℝ) := by
  have hl : 0 < l := by linarith
  have hg : 0 ≤ 1 - l := by linarith
  have hgap : 1 - l ≤ -Real.log l := by linarith [Real.log_le_sub_one_of_pos hl]
  exact (weak_smoothing_gap_explicit hl0 hl1 hr hr1).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hg hgap (by norm_num)) (by norm_num : (0 : ℝ) ≤ 23))

/-- Equation (3.5) of revised paper, with its exact advertised constant. -/
theorem weak_smoothing_explicit {l r : ℝ} (hl0 : 1 / 2 < l) (hl1 : l < 1)
    (hr : 0 < r) (hr1 : r ≤ 1) :
    Gaussian.detail (convolution l) r ≤ 40 * (-Real.log l) ^ (1 / 3 : ℝ) := by
  have hn : 0 ≤ -Real.log l := neg_nonneg.mpr (Real.log_nonpos (by linarith) hl1.le)
  have hp : 0 ≤ (-Real.log l) ^ (1 / 3 : ℝ) := Real.rpow_nonneg hn _
  exact (weak_smoothing_twenty_three hl0.le hl1 hr hr1).trans (by nlinarith)

end LpSelfSimilar.Bernoulli
