module

public import LpSelfSimilar.Bernoulli.TailDetail
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
Weak smoothing from the smallest Bernoulli digits, equation (3.5). The tail index
is chosen between consecutive geometric powers. Its exact variance balances
the Gaussian term and the Lindeberg error at the cube root of the gap.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real

namespace LpSelfSimilar.Bernoulli

noncomputable def weakSmoothingConstant : ℝ := 8 + Gaussian.smallSummandConstant

lemma weakSmoothingConstant_pos : 0 < weakSmoothingConstant := by
  unfold weakSmoothingConstant
  linarith [Gaussian.smallSummandConstant_nonneg]

lemma gaussian_tail_fraction_le {l ε r a : ℝ} (hl0 : 1 / 2 ≤ l) (hl1 : l < 1)
    (hε : 0 < ε) (hr : 0 < r) (hcube : ε ^ 3 = 1 - l) (ha : l * (ε * r) ≤ a) :
    r ^ 2 / (r ^ 2 + a ^ 2 / (1 - l ^ 2)) ≤ 8 * ε := by
  have hl : 0 < l := by linarith
  have hg : 0 < 1 - l ^ 2 := by nlinarith
  have hhalf : ε * r / 2 ≤ a := by nlinarith [mul_nonneg (by linarith : 0 ≤ l - 1 / 2) (mul_nonneg hε.le hr.le)]
  have ha0 : 0 < a := by linarith [mul_pos hε hr]
  have ha2 : (ε * r / 2) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (by positivity) hhalf 2
  have hg2 : 1 - l ^ 2 ≤ 2 * ε ^ 3 := by nlinarith [sq_nonneg (1 - l)]
  have hh : r ^ 2 * (1 - l ^ 2) ≤ 8 * ε * a ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hg2 (sq_nonneg r)
    have h2 := mul_le_mul_of_nonneg_left ha2 (by positivity : 0 ≤ 8 * ε)
    nlinarith
  have hv : r ^ 2 ≤ 8 * ε * (a ^ 2 / (1 - l ^ 2)) := by
    rw [← mul_div_assoc]
    exact (le_div_iff₀ hg).2 hh
  apply (div_le_iff₀ (by positivity : 0 < r ^ 2 + a ^ 2 / (1 - l ^ 2))).2
  nlinarith [mul_nonneg hε.le (sq_nonneg r)]

lemma detail_le_of_cube_eq_gap {l ε r : ℝ} (hl0 : 1 / 2 ≤ l) (hl1 : l < 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1)
    (hcube : ε ^ 3 = 1 - l) :
    Gaussian.detail (convolution l) r ≤ weakSmoothingConstant * ε := by
  have hl : 0 < l := by linarith
  have htarget : ε * r ≤ 1 := (mul_le_mul hε1 hr1 hr.le (by norm_num)).trans (by norm_num)
  obtain ⟨n, hn, hprev⟩ := exists_nat_pow_near_of_lt_one (mul_pos hε hr) htarget hl hl1
  have ha : l * (ε * r) ≤ l ^ (n + 1) := by
    rw [pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left hprev hl.le]
  have htail := detail_scaled_convolution_le hl.le hl1 (pow_nonneg hl.le _)
    hε.le hε1 hr hn.le
  have hfrac := gaussian_tail_fraction_le hl0 hl1 hε hr hcube ha
  have hdisc := detail_le_scaled_tail (l := l) (by simpa only [abs_of_pos hl] using hl1) hr (n + 1)
  unfold weakSmoothingConstant
  linarith

/-- Equation (3.5), first in the stronger gap form. -/
theorem weak_smoothing_gap {l r : ℝ} (hl0 : 1 / 2 ≤ l) (hl1 : l < 1)
    (hr : 0 < r) (hr1 : r ≤ 1) :
    Gaussian.detail (convolution l) r ≤
      weakSmoothingConstant * (1 - l) ^ (1 / 3 : ℝ) := by
  have hg : 0 < 1 - l := by linarith
  have he : 0 < (1 - l) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hg _
  have he1 : (1 - l) ^ (1 / 3 : ℝ) ≤ 1 :=
    Real.rpow_le_one hg.le (by linarith) (by norm_num)
  have hcube : ((1 - l) ^ (1 / 3 : ℝ)) ^ 3 = 1 - l := by
    rw [← Real.rpow_mul_natCast hg.le]
    norm_num
  exact detail_le_of_cube_eq_gap hl0 hl1 he he1 hr hr1 hcube

/-- The paper's logarithmic parameter `χ = -log l`, with one absolute constant. -/
theorem weak_smoothing {l r : ℝ} (hl0 : 1 / 2 ≤ l) (hl1 : l < 1)
    (hr : 0 < r) (hr1 : r ≤ 1) :
    Gaussian.detail (convolution l) r ≤
      weakSmoothingConstant * (-Real.log l) ^ (1 / 3 : ℝ) := by
  have hl : 0 < l := by linarith
  have hg : 0 ≤ 1 - l := by linarith
  have hgap : 1 - l ≤ -Real.log l := by linarith [Real.log_le_sub_one_of_pos hl]
  exact (weak_smoothing_gap hl0 hl1 hr hr1).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hg hgap (by norm_num)) weakSmoothingConstant_pos.le)

end LpSelfSimilar.Bernoulli
