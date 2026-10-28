module

public import LpSelfSimilar.Entropy.GraphCoverRepresentation
public import LpSelfSimilar.Entropy.GraphConditionalMaximum

@[expose] public section

/-!
# Canonical labels for every independent-set coverage

A finite convex presentation may repeat its independent sets. Summing the weights
of equal labels puts it on the single fixed label type of all finite vertex sets.
The coverage vector is unchanged. Invalid labels automatically receive zero
weight, since each contributing original label is independent.
-/

open scoped BigOperators

namespace LpSelfSimilar.Entropy

/-- Every polytope point has a cover presentation on the fixed family of all finite sets. -/
theorem exists_canonical_cover_of_mem_independentSetPolytope {ι : Type*} [Fintype ι]
    (G : SimpleGraph ι) {x : ι → ℝ} (hx : x ∈ independentSetPolytope G) :
    ∃ W : Finset ι → ℝ, (∀ s, 0 ≤ W s) ∧ (∑ s, W s = 1) ∧
      finiteCoverWeight Finset.univ W (graphIndependentCover G) = x := by
  classical
  obtain ⟨κ, hκ, w, cover, hw, hsum, hcover, he⟩ :=
    exists_finite_cover_of_mem_independentSetPolytope G hx
  let W : Finset ι → ℝ := fun s ↦ ∑ j, if cover j = s then w j else 0
  have hW (s : Finset ι) : 0 ≤ W s := by
    apply Finset.sum_nonneg
    intro j _
    split_ifs
    · exact hw j
    · exact le_rfl
  have hWsum : ∑ s, W s = 1 := by
    simp only [W]
    rw [Finset.sum_comm]
    simpa using hsum
  refine ⟨W, hW, hWsum, ?_⟩
  rw [← he]
  ext i
  calc
    finiteCoverWeight Finset.univ W (graphIndependentCover G) i =
        ∑ s, W s * vertexSetIndicator (graphIndependentCover G s) i := by
      simp [finiteCoverWeight, vertexSetIndicator, mul_ite]
    _ = ∑ j, ∑ s, (if cover j = s then w j else 0) *
        vertexSetIndicator (graphIndependentCover G s) i := by
      simp only [W, Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = ∑ j, w j * vertexSetIndicator (cover j) i := by
      apply Finset.sum_congr rfl
      intro j _
      simp [ite_mul, graphIndependentCover, hcover j]
    _ = finiteCoverWeight Finset.univ w cover i := by
      simp [finiteCoverWeight, vertexSetIndicator, mul_ite]

end LpSelfSimilar.Entropy
