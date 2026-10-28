module

public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Tactic

@[expose] public section

/-!
Evaluation bounds from the genuine polynomial Mahler measure.

Mignotte's coefficient bound and the binomial identity first bound evaluation at
one by 2^degree times the Mahler measure. Factoring out a specified root in the
closed unit disk retains its exact distance from one and saves one degree. This
is the geometric estimate behind the logarithmic gap bound in Section 3.
-/

open Polynomial

namespace LpSelfSimilar

lemma polynomial_norm_eval_one_le (p : ℂ[X]) :
    ‖p.eval 1‖ ≤ 2 ^ p.natDegree * p.mahlerMeasure := by
  rw [eval_eq_sum_range]
  simp only [one_pow, mul_one]
  calc
    ‖∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j‖ ≤
        ∑ j ∈ Finset.range (p.natDegree + 1), ‖p.coeff j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (p.natDegree + 1),
        (p.natDegree.choose j : ℝ) * p.mahlerMeasure :=
      Finset.sum_le_sum (fun j _ ↦ p.norm_coeff_le_choose_mul_mahlerMeasure j)
    _ = 2 ^ p.natDegree * p.mahlerMeasure := by
      rw [← Finset.sum_mul]
      congr 1
      exact_mod_cast Nat.sum_range_choose p.natDegree

/-- A specified root in the unit disk contributes its actual distance from one;
its contribution to the Mahler measure itself is one. -/
lemma polynomial_norm_eval_one_le_of_root {p : ℂ[X]} (hp : p ≠ 0)
    {z : ℂ} (hz : p.IsRoot z) (hz1 : ‖z‖ ≤ 1) :
    ‖p.eval 1‖ ≤ ‖1 - z‖ * 2 ^ (p.natDegree - 1) * p.mahlerMeasure := by
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hz
  have hq0 : q ≠ 0 := by
    intro h
    exact hp (by simpa only [h, mul_zero] using hq)
  have hdeg : q.natDegree = p.natDegree - 1 := by
    rw [hq, natDegree_mul (X_sub_C_ne_zero z) hq0, natDegree_X_sub_C]
    omega
  have hM : p.mahlerMeasure = q.mahlerMeasure := by
    rw [hq, mahlerMeasure_mul, mahlerMeasure_X_sub_C, max_eq_left hz1, one_mul]
  calc
    ‖p.eval 1‖ = ‖1 - z‖ * ‖q.eval 1‖ := by simp [hq]
    _ ≤ ‖1 - z‖ * (2 ^ q.natDegree * q.mahlerMeasure) :=
      mul_le_mul_of_nonneg_left (polynomial_norm_eval_one_le q) (norm_nonneg _)
    _ = ‖1 - z‖ * 2 ^ (p.natDegree - 1) * p.mahlerMeasure := by rw [hdeg, hM]; ring

end LpSelfSimilar
