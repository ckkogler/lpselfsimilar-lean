module

public import LpSelfSimilar.Analysis.FourthRootIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-!
An integrated increment inequality. Translating an interval integral leaves
only two boundary intervals. A fourth-root bound on the increment then gives
a quantitative lower bound on the integral of the nonnegative input.
-/

open MeasureTheory Set Real

namespace LpSelfSimilar

lemma integral_shift_sub_eq_boundary (H : ℝ → ℝ)
    (hH : ∀ a b, IntervalIntegrable H volume a b) (a b h : ℝ) :
    (∫ x in a..b, H (x + h) - H x) =
      (∫ x in b..b + h, H x) - ∫ x in a..a + h, H x := by
  have hi : IntervalIntegrable (fun x ↦ H (x + h)) volume a b := by
    exact (IntervalIntegrable.comp_add_right_iff).mpr (hH (a + h) (b + h))
  rw [intervalIntegral.integral_sub hi (hH a b), intervalIntegral.integral_comp_add_right]
  have h1 := intervalIntegral.integral_add_adjacent_intervals (hH a b) (hH b (b + h))
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (hH a (a + h)) (hH (a + h) (b + h))
  linarith

/-- Entropy boundary separation forces positive integrated variance. -/
lemma boundary_gap_pow_four_le_integral {H V : ℝ → ℝ}
    (hH : ∀ a b, IntervalIntegrable H volume a b)
    (hV : ∀ a b, IntervalIntegrable V volume a b)
    (hn : ∀ x, 0 ≤ V x) {a b h C E₀ E₁ : ℝ}
    (hab : a ≤ b) (hh : 0 ≤ h) (hC : 0 ≤ C) (hE : E₀ ≤ E₁)
    (hinc : ∀ x, H (x + h) - H x ≤ C * Real.sqrt (Real.sqrt (V x)))
    (hlo : ∀ x ∈ Icc a (a + h), H x ≤ E₀)
    (hhi : ∀ x ∈ Icc b (b + h), E₁ ≤ H x) :
    (h * (E₁ - E₀)) ^ 4 ≤ C ^ 4 * (b - a) ^ 3 * ∫ x in a..b, V x := by
  have hi : IntervalIntegrable (fun x ↦ H (x + h)) volume a b :=
    (IntervalIntegrable.comp_add_right_iff).mpr (hH (a + h) (b + h))
  have hv := (hV a b).1
  have hr := integrable_sqrt_of_nonneg hv (ae_of_all _ hn)
  have hr2 := integrable_sqrt_of_nonneg hr (ae_of_all _ (fun _ ↦ Real.sqrt_nonneg _))
  have hri : IntervalIntegrable (fun x ↦ Real.sqrt (Real.sqrt (V x))) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hr2
  have hupper := intervalIntegral.integral_mono_on hab (hi.sub (hH a b)) (hri.const_mul C)
    (fun x _ ↦ hinc x)
  rw [integral_shift_sub_eq_boundary H hH, intervalIntegral.integral_const_mul] at hupper
  have hlower := intervalIntegral.integral_mono_on (by linarith : b ≤ b + h)
    (intervalIntegrable_const (c := E₁)) (hH b (b + h)) hhi
  have hsmall := intervalIntegral.integral_mono_on (by linarith : a ≤ a + h)
    (hH a (a + h)) (intervalIntegrable_const (c := E₀)) hlo
  simp only [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left] at hlower hsmall
  have hgap : h * (E₁ - E₀) ≤ C * ∫ x in a..b, Real.sqrt (Real.sqrt (V x)) := by
    nlinarith
  have hp := pow_le_pow_left₀ (mul_nonneg hh (sub_nonneg.mpr hE)) hgap 4
  rw [mul_pow] at hp
  have hroot := integral_fourthRoot_pow_four_le
    ((hV a b).1) (ae_of_all _ hn)
  rw [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab)] at hroot
  rw [intervalIntegral.integral_of_le hab] at hp ⊢
  rw [mul_pow] at hp
  simpa only [mul_pow, mul_assoc] using hp.trans
    (mul_le_mul_of_nonneg_left hroot (pow_nonneg hC 4))

end LpSelfSimilar
