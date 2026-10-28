module

public import LpSelfSimilar.Analysis.WeightedTranslations
public import Mathlib.Analysis.Calculus.TaylorIntegral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-!
Taylor's theorem for translations, with its integral remainder. This formulation
keeps the third derivative inside an average of translates so that its L1 norm
can be estimated by Fubini, without a nonintegrable constant spatial bound.
-/

open MeasureTheory Real

namespace LpSelfSimilar

/-- Quadratic Taylor remainder for translation by `u`. -/
noncomputable def translationRemainder (f : ℝ → ℝ) (u x : ℝ) : ℝ :=
  f (x + u) - f x - u * deriv f x - u ^ 2 / 2 * iteratedDeriv 2 f x

lemma translationRemainder_eq_integral {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) (u x : ℝ) :
    translationRemainder f u x =
      u ^ 3 / 2 * ∫ t in (0 : ℝ)..1, (1 - t) ^ 2 * iteratedDeriv 3 f (x + t * u) := by
  have h := map_add_eq_sum_add_integral_iteratedFDeriv (f := f) (x := x) (y := u) (n := 2)
    (fun _ _ ↦ hf.contDiffAt)
  simp only [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.factorial_zero, Nat.factorial_succ, Nat.cast_ofNat, Nat.cast_one, Nat.cast_mul,
    inv_one, one_mul, pow_zero, pow_one, iteratedDeriv_zero, iteratedDeriv_one] at h
  have he (t : ℝ) : (1 - t) ^ 2 * (u ^ 3 * iteratedDeriv 3 f (x + t * u)) =
      u ^ 3 * ((1 - t) ^ 2 * iteratedDeriv 3 f (x + t * u)) := by ring
  simp_rw [he] at h
  rw [intervalIntegral.integral_const_mul] at h
  unfold translationRemainder
  linarith

/-- The quadratic translation remainder has the sharp integral-Taylor L1 bound. -/
lemma integral_abs_translationRemainder_le {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (hD : Integrable (iteratedDeriv 3 f) volume) (u : ℝ) :
    (∫ x, |translationRemainder f u x|) ≤
      |u| ^ 3 / 6 * ∫ x, |iteratedDeriv 3 f x| := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have hwm : Measurable (fun t : ℝ ↦ (1 - t) ^ 2) := by fun_prop
  have hw : Integrable (fun t : ℝ ↦ (1 - t) ^ 2) μ :=
    ((show Continuous (fun t : ℝ ↦ (1 - t) ^ 2) by fun_prop).intervalIntegrable 0 1).1
  have he (x : ℝ) : translationRemainder f u x =
      u ^ 3 / 2 * ∫ t, (1 - t) ^ 2 * iteratedDeriv 3 f (x - (-t * u)) ∂μ := by
    rw [translationRemainder_eq_integral hf u x, intervalIntegral.integral_of_le zero_le_one]
    simp only [neg_mul, sub_neg_eq_add, μ]
  have hbound := integral_abs_weighted_average_le hwm hw
    (show Measurable (fun t : ℝ ↦ -t * u) by fun_prop)
    (hf.continuous_iteratedDeriv' 3) hD
  have hweight : (∫ t, |(1 - t) ^ 2| ∂μ) = 1 / 3 := by
    have hsq (t : ℝ) : |(1 - t) ^ 2| = (1 - t) ^ 2 := abs_of_nonneg (sq_nonneg _)
    simp_rw [hsq]
    change (∫ t in Set.Ioc (0 : ℝ) 1, (1 - t) ^ 2) = _
    rw [← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_comp_sub_left (fun t : ℝ ↦ t ^ 2) 1]
    norm_num [integral_pow]
  rw [hweight] at hbound
  simp_rw [he, abs_mul]
  rw [integral_const_mul]
  have hc : |u ^ 3 / 2| = |u| ^ 3 / 2 := by rw [abs_div, abs_pow]; norm_num
  rw [hc]
  calc
    |u| ^ 3 / 2 * (∫ x, |∫ t, (1 - t) ^ 2 * iteratedDeriv 3 f (x - (-t * u)) ∂μ|) ≤
      |u| ^ 3 / 2 * (1 / 3 * ∫ x, |iteratedDeriv 3 f x|) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by ring

end LpSelfSimilar
