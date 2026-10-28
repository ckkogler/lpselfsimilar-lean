module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Tactic

@[expose] public section

/-!
# Finite probability averages

Weighted Cauchy--Schwarz bounds a first moment by its second moment without
introducing square roots of the weights. A minimum of a finite family is no
larger than its probability average; this selects a single index before any
subsequent conditional label is sampled. Zero weights are allowed throughout.
-/

open scoped BigOperators

namespace LpSelfSimilar.Analysis

/-- The square of a probability average is bounded by the second moment. -/
theorem sq_weighted_sum_le {ι : Type*} [Fintype ι]
    (w f : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    (∑ i, w i * f i) ^ 2 ≤ ∑ i, w i * (f i) ^ 2 := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun i ↦ w i * f i) (f := w) (g := fun i ↦ w i * (f i) ^ 2)
    (fun i _ ↦ hw i) (fun i _ ↦ mul_nonneg (hw i) (sq_nonneg _))
    (fun i _ ↦ by nlinarith [sq_nonneg (w i * f i)])
  simpa only [hsum, one_mul] using h

/-- A bound on the second moment gives a square-root bound on the first moment. -/
theorem weighted_sum_le_sqrt {ι : Type*} [Fintype ι]
    (w f : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    {B : ℝ} (hB : ∑ i, w i * (f i) ^ 2 ≤ B) :
    ∑ i, w i * f i ≤ Real.sqrt B :=
  Real.le_sqrt_of_sq_le ((sq_weighted_sum_le w f hw hsum).trans hB)

/-- Some index has value at most a prescribed upper bound for the probability average. -/
theorem exists_le_of_weighted_sum_le {ι : Type*} [Fintype ι]
    (w f : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    {B : ℝ} (hB : ∑ i, w i * f i ≤ B) : ∃ i, f i ≤ B := by
  classical
  have hne : (Finset.univ : Finset ι).Nonempty := by
    by_contra h
    have hz := Finset.not_nonempty_iff_eq_empty.mp h
    simp [hz] at hsum
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image Finset.univ f hne
  refine ⟨i, le_trans ?_ hB⟩
  calc
    f i = ∑ j, w j * f i := by rw [← Finset.sum_mul, hsum, one_mul]
    _ ≤ ∑ j, w j * f j := Finset.sum_le_sum fun j hj ↦
      mul_le_mul_of_nonneg_left (hmin j hj) (hw j)

end LpSelfSimilar.Analysis
