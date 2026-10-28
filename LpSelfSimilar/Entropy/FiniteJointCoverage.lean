module

public import LpSelfSimilar.Entropy.GraphCoverRepresentation
public import LpSelfSimilar.Entropy.FiniteSupportedJoint

@[expose] public section

/-!
# Coverages supplied by the label marginal of a joint law

Sampling the actual label marginal yields an independent-set coverage. Each
point's coverage is at least its point probability, because a joint entry is
bounded by its column mass and can occur only on an allowed support. This gives
the positive-on-support comparison vector used in the reverse entropy bound.
-/

open scoped BigOperators

namespace LpSelfSimilar.Entropy

/-- A finite probability weighting of independent supports gives a polytope point. -/
theorem finiteCoverWeight_mem_independentSetPolytope {ι κ : Type*} [Fintype κ]
    (G : SimpleGraph ι) (w : κ → ℝ) (cover : κ → Finset ι)
    (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j, w j = 1)
    (hcover : ∀ j, G.IsIndepSet (cover j : Set ι)) :
    finiteCoverWeight Finset.univ w cover ∈ independentSetPolytope G := by
  classical
  refine mem_convexHull_of_exists_fintype w (fun j ↦ vertexSetIndicator (cover j)) hw hsum ?_ ?_
  · intro j
    exact ⟨⟨cover j, hcover j⟩, rfl⟩
  · ext i
    simp [finiteCoverWeight, vertexSetIndicator, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, mul_ite]

/-- A row entry is bounded by its prescribed marginal. -/
lemma supportedJoint_entry_le_row {ι κ : Type*} [Fintype κ]
    (p : ι → ℝ) (cover : κ → Finset ι) {u : ι → κ → ℝ}
    (hu : u ∈ supportedJointSpace p cover) (i : ι) (j : κ) : u i j ≤ p i := by
  rw [← hu.2.1 i]
  exact Finset.single_le_sum (fun k _ ↦ hu.1 i k) (Finset.mem_univ j)

/-- The actual label cover includes each point with at least its point probability. -/
theorem supportedJoint_row_le_label_coverage {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → ℝ) (cover : κ → Finset ι) {u : ι → κ → ℝ}
    (hu : u ∈ supportedJointSpace p cover) (i : ι) :
    p i ≤ finiteCoverWeight Finset.univ (fun j ↦ ∑ k, u k j) cover i := by
  classical
  rw [← hu.2.1 i]
  apply Finset.sum_le_sum
  intro j _
  by_cases hi : i ∈ cover j
  · simp only [hi, ite_true]
    exact Finset.single_le_sum (fun k _ ↦ hu.1 k j) (Finset.mem_univ i)
  · simp only [hi, ite_false, hu.2.2 i j hi]
    exact le_rfl

end LpSelfSimilar.Entropy
