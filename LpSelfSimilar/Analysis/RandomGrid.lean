module

public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Tactic

@[expose] public section

/-!
Uniformly shifted unit grids. The expected integer distance of two quantized
points equals their real distance. Consequently the probability that the two
points fall in different cells is at most their distance. Periodicity of the
fractional part proves this without choosing boundary conventions implicitly.
-/

open MeasureTheory Set Real

namespace LpSelfSimilar

lemma intervalIntegrable_fract_add (x a b : ℝ) :
    IntervalIntegrable (fun t ↦ Int.fract (x + t)) volume a b := by
  apply intervalIntegrable_iff.mpr
  apply (intervalIntegrable_const (c := (1 : ℝ)) (a := a) (b := b) (μ := volume)).def'.mono'
    (((measurable_const.add measurable_id).fract).aestronglyMeasurable)
  exact ae_of_all _ (fun t ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
    exact (Int.fract_lt_one _).le)

lemma intervalIntegrable_floor_add (x a b : ℝ) :
    IntervalIntegrable (fun t ↦ (⌊x + t⌋ : ℝ)) volume a b := by
  have he : (fun t ↦ (⌊x + t⌋ : ℝ)) =
      (fun t ↦ x + t) - (fun t ↦ Int.fract (x + t)) := by
    funext t
    simp only [Int.fract, Pi.sub_apply]
    ring
  rw [he]
  exact ((continuous_const.add continuous_id).intervalIntegrable a b).sub
    (intervalIntegrable_fract_add x a b)

lemma integral_floor_sub_floor (x y : ℝ) :
    (∫ t in (0 : ℝ)..1, ((⌊x + t⌋ : ℝ) - ⌊y + t⌋)) = x - y := by
  have hf : Function.Periodic (Int.fract : ℝ → ℝ) 1 := Int.fract_add_one
  have hperiod : (∫ t in (0 : ℝ)..1, Int.fract (x + t)) =
      ∫ t in (0 : ℝ)..1, Int.fract (y + t) := by
    rw [intervalIntegral.integral_comp_add_left, intervalIntegral.integral_comp_add_left]
    simpa only [add_zero, add_comm 1] using hf.intervalIntegral_add_eq x y
  have he (t : ℝ) : (⌊x + t⌋ : ℝ) - ⌊y + t⌋ =
      (x - y) - (Int.fract (x + t) - Int.fract (y + t)) := by
    simp only [Int.fract]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_sub intervalIntegrable_const
      ((intervalIntegrable_fract_add x 0 1).sub (intervalIntegrable_fract_add y 0 1)),
    intervalIntegral.integral_sub (intervalIntegrable_fract_add x 0 1)
      (intervalIntegrable_fract_add y 0 1), hperiod]
  simp

lemma integral_abs_floor_sub_floor (x y : ℝ) :
    (∫ t in (0 : ℝ)..1, |(⌊x + t⌋ : ℝ) - ⌊y + t⌋|) = |x - y| := by
  rcases le_total y x with hxy | hxy
  · have hnonneg (t : ℝ) : 0 ≤ (⌊x + t⌋ : ℝ) - ⌊y + t⌋ := by
      apply sub_nonneg.mpr
      exact_mod_cast Int.floor_mono (show y + t ≤ x + t by linarith)
    simp_rw [abs_of_nonneg (hnonneg _)]
    rw [integral_floor_sub_floor, abs_of_nonneg (sub_nonneg.mpr hxy)]
  · have hnonpos (t : ℝ) : (⌊x + t⌋ : ℝ) - ⌊y + t⌋ ≤ 0 := by
      apply sub_nonpos.mpr
      exact_mod_cast Int.floor_mono (show x + t ≤ y + t by linarith)
    simp_rw [abs_of_nonpos (hnonpos _)]
    rw [intervalIntegral.integral_neg, integral_floor_sub_floor,
      abs_of_nonpos (sub_nonpos.mpr hxy)]

lemma indicator_floor_ne_le_abs (x y t : ℝ) :
    (if ⌊x + t⌋ ≠ ⌊y + t⌋ then (1 : ℝ) else 0) ≤ |(⌊x + t⌋ : ℝ) - ⌊y + t⌋| := by
  split_ifs with h
  · have hi : (1 : ℤ) ≤ |⌊x + t⌋ - ⌊y + t⌋| := by
      have hz : ⌊x + t⌋ - ⌊y + t⌋ ≠ 0 := sub_ne_zero.mpr h
      exact Int.one_le_abs hz
    exact_mod_cast hi
  · exact abs_nonneg _

lemma integral_indicator_floor_ne_le (x y : ℝ) :
    (∫ t in (0 : ℝ)..1, if ⌊x + t⌋ ≠ ⌊y + t⌋ then (1 : ℝ) else 0) ≤ |x - y| := by
  have hi : IntervalIntegrable
      (fun t ↦ if ⌊x + t⌋ ≠ ⌊y + t⌋ then (1 : ℝ) else 0) volume 0 1 := by
    apply intervalIntegrable_iff.mpr
    have hm : Measurable (fun t : ℝ ↦ if ⌊x + t⌋ ≠ ⌊y + t⌋ then (1 : ℝ) else 0) := by
      apply Measurable.ite
      · exact (measurableSet_eq_fun (by fun_prop) (by fun_prop)).compl
      · exact measurable_const
      · exact measurable_const
    apply (intervalIntegrable_const (c := (1 : ℝ)) (a := 0) (b := 1) (μ := volume)).def'.mono'
      hm.aestronglyMeasurable
    exact ae_of_all _ (fun _ ↦ by split_ifs <;> norm_num)
  apply (intervalIntegral.integral_mono (by norm_num) hi
    ((intervalIntegrable_floor_add x 0 1).sub (intervalIntegrable_floor_add y 0 1)).abs
    (fun t ↦ indicator_floor_ne_le_abs x y t)).trans_eq
  exact integral_abs_floor_sub_floor x y

end LpSelfSimilar
