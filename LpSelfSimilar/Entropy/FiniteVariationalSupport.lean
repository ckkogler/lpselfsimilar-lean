module

public import LpSelfSimilar.Entropy.FiniteVariational

@[expose] public section

/-!
# Gibbs' inequality with zero comparison weights

The comparison vector need only be positive on the support of the probability
vector. Restricting both entropy sums to that support removes the null terms;
nonnegativity ensures that restriction does not increase the comparison mass.
-/

open scoped BigOperators

namespace LpSelfSimilar.Entropy

/-- Gibbs' inequality for a nonnegative comparison vector positive on the law's support. -/
theorem finite_entropy_le_cross_entropy_on_support {ι : Type*} (s : Finset ι)
    (p q : ι → ℝ) (hp : ∀ i ∈ s, 0 ≤ p i) (hsum : ∑ i ∈ s, p i = 1)
    (hq : ∀ i ∈ s, 0 ≤ q i) (hqs : ∀ i ∈ s, p i ≠ 0 → 0 < q i)
    (hqsum : ∑ i ∈ s, q i ≤ 1) :
    (∑ i ∈ s, Real.negMulLog (p i)) ≤ ∑ i ∈ s, p i * (-Real.log (q i)) := by
  classical
  let t := s.filter (fun i ↦ p i ≠ 0)
  have hrestrict (f : ι → ℝ) (hf : ∀ i ∈ s, p i = 0 → f i = 0) :
      (∑ i ∈ t, f i) = ∑ i ∈ s, f i := by
    simp only [t, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hpi : p i = 0
    · simp [hpi, hf i hi hpi]
    · simp [hpi]
  have hpt : ∑ i ∈ t, p i = 1 := (hrestrict p (fun _ _ hi ↦ hi)).trans hsum
  have hqt : (∑ i ∈ t, q i) ≤ 1 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i hi _ ↦ hq i hi)).trans hqsum
  have h := finite_entropy_le_cross_entropy t p q
    (fun i hi ↦ hp i (Finset.mem_filter.mp hi).1) hpt
    (fun i hi ↦ hqs i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2) hqt
  rw [hrestrict (fun i ↦ Real.negMulLog (p i)) (by intros; simp_all),
    hrestrict (fun i ↦ p i * (-Real.log (q i))) (by intros; simp_all)] at h
  exact h

end LpSelfSimilar.Entropy
