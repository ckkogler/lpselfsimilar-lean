module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic

@[expose] public section

/-!
# Positive minimizers of weighted logarithmic cost

On a compact set of nonnegative vectors containing a vector positive on the
weight support, the logarithmic minimum is attained with the same positivity.
We maximize a continuous weighted product first. A zero coordinate carrying
positive weight has product zero and cannot occur at the maximizer. Coordinates
of weight zero contribute zero to the logarithmic cost and require no convention
beyond the ordinary continuous definition of `0 log 0`.
-/

open Set
open scoped BigOperators

namespace LpSelfSimilar

/-- Weighted logarithmic minimization, allowing zero coordinate weights. -/
theorem exists_weighted_log_minimizer_on_support {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (K : Set (ι → ℝ)) (hK : IsCompact K)
    (hK0 : ∀ x ∈ K, ∀ i, 0 ≤ x i)
    (hu : ∃ u ∈ K, ∀ i, p i ≠ 0 → 0 < u i) :
    ∃ x ∈ K, (∀ i, p i ≠ 0 → 0 < x i) ∧
      ∀ y ∈ K, (∀ i, p i ≠ 0 → 0 < y i) →
        (∑ i, p i * (-Real.log (x i))) ≤ ∑ i, p i * (-Real.log (y i)) := by
  classical
  obtain ⟨u, huK, hu0⟩ := hu
  let P : (ι → ℝ) → ℝ := fun x ↦ ∏ i, (x i) ^ (p i)
  have hP : Continuous P := by
    apply continuous_finsetProd
    intro i _
    exact (Real.continuous_rpow_const (hp i)).comp (continuous_apply i)
  obtain ⟨x, hxK, hxmax⟩ := hK.exists_isMaxOn ⟨u, huK⟩ hP.continuousOn
  have hprod (z : ι → ℝ) (hz : ∀ i, p i ≠ 0 → 0 < z i) : 0 < P z := by
    apply Finset.prod_pos
    intro i _
    by_cases hpi : p i = 0
    · simp [hpi]
    · exact Real.rpow_pos_of_pos (hz i hpi) _
  have hxP : 0 < P x := (hprod u hu0).trans_le (hxmax huK)
  have hx0 : ∀ i, p i ≠ 0 → 0 < x i := by
    intro i hpi
    have hxi : x i ≠ 0 := by
      intro hi
      have hz : P x = 0 := Finset.prod_eq_zero (Finset.mem_univ i)
        (by rw [hi, Real.zero_rpow hpi])
      exact hxP.ne' hz
    exact lt_of_le_of_ne (hK0 x hxK i) hxi.symm
  refine ⟨x, hxK, hx0, ?_⟩
  intro y hyK hy0
  have hlog := Real.log_le_log (hprod y hy0) (hxmax hyK)
  have hlogP (z : ι → ℝ) (hz : ∀ i, p i ≠ 0 → 0 < z i) :
      Real.log (P z) = ∑ i, p i * Real.log (z i) := by
    change Real.log (∏ i, (z i) ^ (p i)) = _
    rw [Real.log_prod (fun i _ ↦ by
      by_cases hpi : p i = 0
      · simp [hpi]
      · exact (Real.rpow_pos_of_pos (hz i hpi) (p i)).ne')]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hpi : p i = 0
    · simp [hpi]
    · exact Real.log_rpow (hz i hpi) (p i)
  rw [hlogP y hy0, hlogP x hx0] at hlog
  simpa only [mul_neg, Finset.sum_neg_distrib] using neg_le_neg hlog

/-- Strictly positive weights give a minimizer with every coordinate positive. -/
theorem exists_positive_weighted_log_minimizer {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 < p i) (K : Set (ι → ℝ)) (hK : IsCompact K)
    (hK0 : ∀ x ∈ K, ∀ i, 0 ≤ x i)
    (hu : ∃ u ∈ K, ∀ i, 0 < u i) :
    ∃ x ∈ K, (∀ i, 0 < x i) ∧
      ∀ y ∈ K, (∀ i, 0 < y i) →
        (∑ i, p i * (-Real.log (x i))) ≤ ∑ i, p i * (-Real.log (y i)) := by
  obtain ⟨x, hxK, hx0, hx⟩ := exists_weighted_log_minimizer_on_support p
    (fun i ↦ (hp i).le) K hK hK0 (by
      obtain ⟨u, huK, hu0⟩ := hu
      exact ⟨u, huK, fun i _ ↦ hu0 i⟩)
  exact ⟨x, hxK, fun i ↦ hx0 i (hp i).ne', fun y hy hy0 ↦ hx y hy (fun i _ ↦ hy0 i)⟩

end LpSelfSimilar
