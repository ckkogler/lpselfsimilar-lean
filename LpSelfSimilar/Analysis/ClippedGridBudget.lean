module

public import LpSelfSimilar.Analysis.ShiftedGridAverage

@[expose] public section

/-!
# Finite translated grids after a uniform attenuation loss

Subtracting a fixed nonnegative frequency error and taking the positive part
loses at most the error times the interval length from the integral budget.
The existing finite grid averaging theorem then selects a deterministic grid.
This avoids an infinite periodization sum and requires only measurability.
-/

open MeasureTheory Set
open scoped BigOperators

namespace LpSelfSimilar.Analysis

/-- A bounded measurable attenuation remains interval-integrable after clipping. -/
theorem intervalIntegrable_clipped_attenuation (f : ℝ → ℝ) (hm : Measurable f)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) {c : ℝ} (hc : 0 ≤ c) (a b : ℝ) :
    IntervalIntegrable (fun x ↦ max (f x - c) 0) volume a b := by
  have hi : IntegrableOn (fun x ↦ max (f x - c) 0) (Icc (min a b) (max a b)) := by
    apply (integrable_const (1 : ℝ)).mono'
      ((hm.sub measurable_const).max measurable_const).aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    change max (f x - c) 0 ≤ 1
    exact max_le (by linarith [(hf x).2]) zero_le_one
  exact hi.intervalIntegrable.mono_set (by simp only [uIcc]; rfl)

/-- The positive part loses at most the uniform error times the interval length. -/
theorem integral_clipped_attenuation_lower_bound (f : ℝ → ℝ) (hm : Measurable f)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) {a b c A : ℝ} (hab : a ≤ b) (hc : 0 ≤ c)
    (hfi : IntervalIntegrable f volume a b) (hA : A ≤ ∫ x in a..b, f x) :
    A - c * (b - a) ≤ ∫ x in a..b, max (f x - c) 0 := by
  have hi := intervalIntegral.integral_mono hab (hfi.sub intervalIntegrable_const)
    (intervalIntegrable_clipped_attenuation f hm hf hc a b)
    (fun x ↦ le_max_left (f x - c) 0)
  rw [intervalIntegral.integral_sub hfi intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul] at hi
  linarith

/-- Some finite translated grid retains the integral budget after the frequency loss. -/
theorem exists_shifted_grid_clipped_budget (f : ℝ → ℝ) (hm : Measurable f)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) {a b h c A : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hh : 0 < h) (hc : 0 ≤ c)
    (N : ℕ) (hb : b ≤ h * N) (hfi : IntervalIntegrable f volume a b)
    (hA : A ≤ ∫ x in a..b, f x) :
    ∃ t : ℝ, (A - c * (b - a)) / h ≤
      ∑ j ∈ Finset.range N, if h * ((j : ℝ) + t) ∈ Icc a b then
        max (f (h * ((j : ℝ) + t)) - c) 0 else 0 := by
  classical
  have hg : ∀ x, 0 ≤ max (f x - c) 0 ∧ max (f x - c) 0 ≤ 1 := by
    intro x
    exact ⟨le_max_right _ _, max_le (by linarith [(hf x).2]) zero_le_one⟩
  obtain ⟨t, ht⟩ := exists_shifted_grid_sum_ge (fun x ↦ max (f x - c) 0)
    ((hm.sub measurable_const).max measurable_const) hg ha hab hh N hb
  refine ⟨t, le_trans ?_ ht⟩
  simpa only [div_eq_mul_inv, one_div, mul_one, one_mul, mul_comm] using
    (div_le_div_of_nonneg_right
      (integral_clipped_attenuation_lower_bound f hm hf hab hc hfi hA) hh.le)

end LpSelfSimilar.Analysis
