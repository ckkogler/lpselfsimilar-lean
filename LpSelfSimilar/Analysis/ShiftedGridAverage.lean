module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.Tactic

@[expose] public section

/-!
Averaging a finite translated arithmetic grid samples an interval integral.
The samples outside the target interval vanish. Consequently one translate has
at least the average sum; no continuity of the sampled function is assumed.
This supplies the deterministic grids in the effective block argument.
-/

open MeasureTheory Set

namespace LpSelfSimilar

/-- A measurable function bounded by one has a translated grid whose sum is at
least its interval integral divided by the grid spacing. -/
theorem exists_shifted_grid_sum_ge (f : ℝ → ℝ) (hm : Measurable f)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) {a b h : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hh : 0 < h) (N : ℕ) (hb : b ≤ h * N) :
    ∃ t : ℝ, (1 / h) * (∫ x in a..b, f x) ≤
      ∑ j ∈ Finset.range N, if h * ((j : ℝ) + t) ∈ Icc a b
        then f (h * ((j : ℝ) + t)) else 0 := by
  classical
  let U : ℝ → ℝ := (Icc a b).indicator f
  have hUm : Measurable U := hm.indicator measurableSet_Icc
  have hU (x : ℝ) : |U x| ≤ 1 := by
    dsimp [U]
    by_cases hx : x ∈ Icc a b
    · rw [indicator_of_mem hx, abs_of_nonneg (hf x).1]
      exact (hf x).2
    · rw [indicator_of_notMem hx]
      norm_num
  have hUi (u v : ℝ) : IntegrableOn U (Icc u v) volume := by
    apply (integrable_const (1 : ℝ)).mono' hUm.aestronglyMeasurable
    exact ae_of_all _ (fun x ↦ by simpa only [Real.norm_eq_abs] using hU x)
  have hcell (j : ℕ) : IntervalIntegrable U volume (h * j) (h * (j + 1)) :=
    (hUi _ _).intervalIntegrable
  have hsample (j : ℕ) : IntegrableOn (fun t : ℝ ↦ U (h * ((j : ℝ) + t)))
      (Icc (0 : ℝ) 1) volume := by
    apply (integrable_const (1 : ℝ)).mono' (hUm.comp (by fun_prop)).aestronglyMeasurable
    exact ae_of_all _ (fun t ↦ by
      simpa only [Real.norm_eq_abs, Function.comp_apply] using hU (h * (j + t)))
  have hcellint (j : ℕ) :
      (∫ t in Icc (0 : ℝ) 1, U (h * ((j : ℝ) + t))) =
        (1 / h) * ∫ x in (h * j)..(h * (j + 1)), U x := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    rw [intervalIntegral.integral_comp_add_left (fun t : ℝ ↦ U (h * t)) (j : ℝ)]
    rw [intervalIntegral.integral_comp_mul_left U hh.ne']
    simp only [add_zero, one_div, smul_eq_mul]
  have hfull : (∫ x in (0 : ℝ)..(h * N), U x) = ∫ x in a..b, f x := by
    have hNh : 0 ≤ h * (N : ℝ) := by positivity
    rw [intervalIntegral.integral_of_le hNh, intervalIntegral.integral_of_le hab,
      ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
    dsimp [U]
    rw [integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
    have hs : Icc a b ⊆ Icc (0 : ℝ) (h * N) := Icc_subset_Icc ha hb
    rw [inter_eq_left.mpr hs]
  have hsum : (∫ t in Icc (0 : ℝ) 1,
      ∑ j ∈ Finset.range N, U (h * ((j : ℝ) + t))) = (1 / h) * ∫ x in a..b, f x := by
    rw [integral_finsetSum _ (fun j _ ↦ hsample j)]
    simp_rw [hcellint]
    rw [← Finset.mul_sum]
    have hs := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun j : ℕ ↦ h * (j : ℝ)) (n := N)
      (fun j _ ↦ by simpa only [Nat.cast_add, Nat.cast_one] using hcell j)
    simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one, mul_zero] at hs
    rw [hs, hfull]
  letI : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩
  obtain ⟨t, ht⟩ := exists_integral_le
    (integrable_finsetSum (Finset.range N) (fun j _ ↦ hsample j))
  rw [hsum] at ht
  refine ⟨t, ?_⟩
  simpa only [U, Set.indicator_apply] using ht

end LpSelfSimilar
