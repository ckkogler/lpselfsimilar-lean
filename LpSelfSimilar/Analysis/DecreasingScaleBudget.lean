module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-!
# Telescoping an integrable scale increment

For a decreasing function vanishing beyond `b`, integrating its backward
increment over `[a,b+w]` leaves precisely its integral over `[a-w,a]`.
That interval contributes at least `w*f(a)`. The statement includes a measurable
integrable majorant for the increment, as used for conditional entropy budgets.
-/

open MeasureTheory Set

namespace LpSelfSimilar.Analysis

/-- A backward increment telescopes to the initial interval when the final tail vanishes. -/
theorem integral_backward_difference_of_vanishing
    (f : ℝ → ℝ) (hf : Antitone f) (a b w : ℝ) (hw : 0 ≤ w)
    (hzero : ∀ x, b ≤ x → f x = 0) :
    (∫ x in a..b + w, (f (x - w) - f x)) = ∫ x in a - w..a, f x := by
  have hshift : Antitone (fun x ↦ f (x - w)) := fun x y hxy ↦ hf (sub_le_sub_right hxy w)
  rw [intervalIntegral.integral_sub hshift.intervalIntegrable hf.intervalIntegrable,
    intervalIntegral.integral_comp_sub_right, add_sub_cancel_right]
  rw [intervalIntegral.integral_interval_sub_interval_comm hf.intervalIntegrable
    hf.intervalIntegrable hf.intervalIntegrable]
  have ht : (∫ x in b..b + w, f x) = 0 := by
    have he : (∫ x in b..b + w, f x) = ∫ x in b..b + w, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le (le_add_of_nonneg_right hw)]
      intro x hx
      exact hzero x hx.1
    simpa using he
  rw [ht, sub_zero]

/-- Any integrable upper bound for the backward increment has the exact initial-value budget. -/
theorem initial_value_le_integral_of_backward_difference
    (f g : ℝ → ℝ) (hf : Antitone f) (a b w : ℝ) (hab : a ≤ b) (hw : 0 ≤ w)
    (hzero : ∀ x, b ≤ x → f x = 0)
    (hg : IntervalIntegrable g volume a (b + w))
    (hbound : ∀ x ∈ Icc a (b + w), f (x - w) - f x ≤ g x) :
    w * f a ≤ ∫ x in a..b + w, g x := by
  have hshift : Antitone (fun x ↦ f (x - w)) := fun x y hxy ↦ hf (sub_le_sub_right hxy w)
  have hi := intervalIntegral.integral_mono_on (show a - w ≤ a by linarith)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ f a) volume (a - w) a)
    hf.intervalIntegrable (fun x hx ↦ hf hx.2)
  have hib : w * f a ≤ ∫ x in a - w..a, f x := by
    simpa only [intervalIntegral.integral_const, sub_sub_cancel, smul_eq_mul] using hi
  have hm := intervalIntegral.integral_mono_on (show a ≤ b + w by linarith)
    (hshift.intervalIntegrable.sub hf.intervalIntegrable) hg hbound
  rw [integral_backward_difference_of_vanishing f hf a b w hw hzero] at hm
  exact hib.trans hm

end LpSelfSimilar.Analysis
