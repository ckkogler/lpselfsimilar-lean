module

public import LpSelfSimilar.Analysis.PolynomialCoefficientBounds
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Multiset

@[expose] public section

/-!
A quantitative resultant bound using the genuine polynomial Mahler measure.

The product formula for the resultant combines a uniform coefficient bound for
one polynomial with the Mahler measure of the other. Factoring out a specified
root in the unit disk then isolates one evaluation with the exact degree loss.
No arithmetic separation or entropy assumption is used in these analytic bounds.
-/

open Polynomial

namespace LpSelfSimilar.Algebraic

lemma norm_resultant_le_coeff_bound (p q : ℂ[X]) {H : ℝ}
    (hH : 0 ≤ H) (hp : ∀ j, ‖p.coeff j‖ ≤ H) :
    ‖q.resultant p‖ ≤ (((p.natDegree : ℝ) + 1) * H) ^ q.natDegree *
      q.mahlerMeasure ^ p.natDegree := by
  have hprod := Multiset.prod_map_le_prod_map₀
    (fun z : ℂ ↦ ‖p.eval z‖)
    (fun z : ℂ ↦ (((p.natDegree : ℝ) + 1) * H) * max 1 ‖z‖ ^ p.natDegree)
    (s := q.roots) (fun z _ ↦ norm_nonneg _) (fun z _ ↦
      polynomial_norm_eval_le_coeff_bound p hH hp z)
  have hnorm : ‖(q.roots.map p.eval).prod‖ = (q.roots.map (fun z ↦ ‖p.eval z‖)).prod := by
    induction q.roots using Multiset.induction_on with
    | empty => simp
    | cons z s ih => simp [ih]
  rw [resultant_eq_prod_eval q p p.natDegree le_rfl (IsAlgClosed.splits q), norm_mul,
    norm_pow, hnorm]
  calc
    ‖q.leadingCoeff‖ ^ p.natDegree * (q.roots.map (fun z ↦ ‖p.eval z‖)).prod ≤
        ‖q.leadingCoeff‖ ^ p.natDegree *
          (q.roots.map (fun z ↦ (((p.natDegree : ℝ) + 1) * H) *
            max 1 ‖z‖ ^ p.natDegree)).prod :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = (((p.natDegree : ℝ) + 1) * H) ^ q.natDegree * q.mahlerMeasure ^ p.natDegree := by
      rw [Multiset.prod_map_mul, Multiset.prod_map_pow,
        Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots, mul_pow]
      simp only [Multiset.map_const', Multiset.prod_replicate,
        (IsAlgClosed.splits q).natDegree_eq_card_roots, mul_pow]
      ring

/-- Remove a distinguished root in the unit disk before bounding the remaining
resultant. Its Mahler factor is one, while its actual evaluation is retained. -/
lemma norm_resultant_le_of_root (p q : ℂ[X]) (hq : q ≠ 0) {H : ℝ}
    (hH : 0 ≤ H) (hp : ∀ j, ‖p.coeff j‖ ≤ H) {z : ℂ}
    (hz : q.IsRoot z) (hz1 : ‖z‖ ≤ 1) :
    ‖q.resultant p‖ ≤ ‖p.eval z‖ * (((p.natDegree : ℝ) + 1) * H) ^ (q.natDegree - 1) *
      q.mahlerMeasure ^ p.natDegree := by
  obtain ⟨r, hr⟩ := dvd_iff_isRoot.mpr hz
  have hr0 : r ≠ 0 := by
    intro h
    exact hq (by simpa only [h, mul_zero] using hr)
  have hdeg : r.natDegree = q.natDegree - 1 := by
    rw [hr, natDegree_mul (X_sub_C_ne_zero z) hr0, natDegree_X_sub_C]
    omega
  have hM : q.mahlerMeasure = r.mahlerMeasure := by
    rw [hr, mahlerMeasure_mul, mahlerMeasure_X_sub_C, max_eq_left hz1, one_mul]
  have hres : q.resultant p = p.eval z * r.resultant p := by
    rw [hr, natDegree_mul (X_sub_C_ne_zero z) hr0,
      resultant_mul_left _ _ _ _ le_rfl, natDegree_X_sub_C,
      resultant_X_sub_C_left _ _ _ le_rfl]
  calc
    ‖q.resultant p‖ = ‖p.eval z‖ * ‖r.resultant p‖ := by rw [hres, norm_mul]
    _ ≤ ‖p.eval z‖ * ((((p.natDegree : ℝ) + 1) * H) ^ r.natDegree *
        r.mahlerMeasure ^ p.natDegree) :=
      mul_le_mul_of_nonneg_left (norm_resultant_le_coeff_bound p r hH hp) (norm_nonneg _)
    _ = ‖p.eval z‖ * (((p.natDegree : ℝ) + 1) * H) ^ (q.natDegree - 1) *
        q.mahlerMeasure ^ p.natDegree := by rw [hdeg, hM]; ring

end LpSelfSimilar.Algebraic
