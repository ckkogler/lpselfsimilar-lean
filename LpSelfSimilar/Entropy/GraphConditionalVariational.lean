module

public import LpSelfSimilar.Entropy.JointCoverageEntropyUpperBound
public import LpSelfSimilar.Entropy.GraphConditionalLowerBound

@[expose] public section

/-!
# Full variational meaning of graph conditional entropy

The canonical maximum equals point entropy minus graph entropy. Every finite
joint law with independent conditional supports is bounded by this same value,
even if it uses another label type or repeats its supports. Since the canonical
maximum is attained, this proves that the fixed finite-set label family computes
the full greatest conditional entropy of finite mixtures.
-/

open scoped BigOperators

namespace LpSelfSimilar.Entropy

/-- Every finite independent-support joint law is bounded by entropy minus graph entropy. -/
theorem jointConditionalEntropy_le_entropy_sub_graphEntropy {ι κ : Type*}
    [Fintype ι] [Fintype κ] (G : SimpleGraph ι) (p : ι → ℝ) (cover : κ → Finset ι)
    (hcover : ∀ j, G.IsIndepSet (cover j : Set ι))
    {u : ι → κ → ℝ} (hu : u ∈ supportedJointSpace p cover) (hsum : ∑ i, p i = 1) :
    jointConditionalEntropy u ≤ (∑ i, Real.negMulLog (p i)) - graphEntropy G p := by
  let q : κ → ℝ := fun j ↦ ∑ i, u i j
  let x := finiteCoverWeight Finset.univ q cover
  have hp : ∀ i, 0 ≤ p i := by
    intro i
    rw [← hu.2.1 i]
    exact Finset.sum_nonneg (fun j _ ↦ hu.1 i j)
  have hq : ∀ j, 0 ≤ q j := fun j ↦ Finset.sum_nonneg (fun i _ ↦ hu.1 i j)
  have hqsum : ∑ j, q j = 1 := by
    simp only [q]
    rw [Finset.sum_comm]
    simpa only [hu.2.1] using hsum
  have hx : x ∈ independentSetPolytope G :=
    finiteCoverWeight_mem_independentSetPolytope G q cover hq hqsum hcover
  have hx0 : ∀ i, p i ≠ 0 → 0 < x i := fun i hi ↦
    (lt_of_le_of_ne (hp i) hi.symm).trans_le (supportedJoint_row_le_label_coverage p cover hu i)
  obtain ⟨v, hv, hv0, hve, hmin⟩ := exists_graphEntropy_minimizer G p hp
  have hcost : graphEntropy G p ≤ graphCoverageCost p x := by
    rw [← hve]
    exact hmin x hx hx0
  exact (jointConditionalEntropy_le_entropy_sub_coverageCost p cover hu hsum).trans
    (sub_le_sub_left hcost _)

/-- The canonical attained maximum is exactly entropy minus graph entropy. -/
theorem graphConditionalEntropy_eq_entropy_sub_graphEntropy {ι : Type*} [Fintype ι]
    (G : SimpleGraph ι) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    graphConditionalEntropy G p = (∑ i, Real.negMulLog (p i)) - graphEntropy G p := by
  apply le_antisymm
  · obtain ⟨u, hu, he, _⟩ := exists_graphConditionalEntropy_maximizer G p hp
    have h := jointConditionalEntropy_le_entropy_sub_graphEntropy G p (graphIndependentCover G)
      (graphIndependentCover_isIndepSet G) hu hsum
    rwa [he] at h
  · exact entropy_sub_graphEntropy_le_graphConditionalEntropy G p hp hsum

/-- Arbitrary finite label families are bounded by the attained canonical maximum. -/
theorem jointConditionalEntropy_le_canonical_maximum {ι κ : Type*}
    [Fintype ι] [Fintype κ] (G : SimpleGraph ι) (p : ι → ℝ) (cover : κ → Finset ι)
    (hcover : ∀ j, G.IsIndepSet (cover j : Set ι))
    {u : ι → κ → ℝ} (hu : u ∈ supportedJointSpace p cover) (hsum : ∑ i, p i = 1) :
    jointConditionalEntropy u ≤ graphConditionalEntropy G p := by
  have hp : ∀ i, 0 ≤ p i := by
    intro i
    rw [← hu.2.1 i]
    exact Finset.sum_nonneg (fun j _ ↦ hu.1 i j)
  rw [graphConditionalEntropy_eq_entropy_sub_graphEntropy G p hp hsum]
  exact jointConditionalEntropy_le_entropy_sub_graphEntropy G p cover hcover hu hsum

end LpSelfSimilar.Entropy
