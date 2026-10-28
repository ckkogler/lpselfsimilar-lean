module

public import LpSelfSimilar.Entropy.FiniteSupportedJoint
public import LpSelfSimilar.Entropy.GraphPolytope

@[expose] public section

/-!
# An attained maximum over all independent-set conditional supports

All finite vertex sets are used as labels. An independent label allows its own
vertices; any other label allows the empty set and is therefore forced to carry
zero mass. This gives one fixed finite-dimensional space of joint laws and avoids
restricting the maximum to a particular convex-combination representation.
The objective is the actual continuous joint-minus-label conditional entropy.
-/

open scoped BigOperators

namespace LpSelfSimilar.Entropy

/-- Canonical allowed support for a finite-set label; invalid labels have zero mass. -/
noncomputable def graphIndependentCover {ι : Type*} (G : SimpleGraph ι)
    (s : Finset ι) : Finset ι := by
  classical
  exact if G.IsIndepSet (s : Set ι) then s else ∅

/-- Greatest conditional entropy on the canonical family of independent supports. -/
noncomputable def graphConditionalEntropy {ι : Type*} [Fintype ι]
    (G : SimpleGraph ι) (p : ι → ℝ) : ℝ :=
  sSup (jointConditionalEntropy '' supportedJointSpace p (graphIndependentCover G))

theorem graphIndependentCover_isIndepSet {ι : Type*} (G : SimpleGraph ι) (s : Finset ι) :
    G.IsIndepSet (graphIndependentCover G s : Set ι) := by
  classical
  by_cases hs : G.IsIndepSet (s : Set ι)
  · simp [graphIndependentCover, hs]
  · simp [graphIndependentCover, hs, SimpleGraph.isIndepSet_iff]

@[simp] theorem graphIndependentCover_singleton {ι : Type*} (G : SimpleGraph ι) (i : ι) :
    graphIndependentCover G {i} = {i} := by
  simp [graphIndependentCover, SimpleGraph.isIndepSet_iff]

/-- The maximum uses all independent supports and is attained by an actual joint law. -/
theorem exists_graphConditionalEntropy_maximizer {ι : Type*} [Fintype ι]
    (G : SimpleGraph ι) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) :
    ∃ u ∈ supportedJointSpace p (graphIndependentCover G),
      jointConditionalEntropy u = graphConditionalEntropy G p ∧
      ∀ v ∈ supportedJointSpace p (graphIndependentCover G),
        jointConditionalEntropy v ≤ jointConditionalEntropy u := by
  classical
  obtain ⟨u, hu, hmax⟩ := exists_jointConditionalEntropy_maximizer p hp
    (graphIndependentCover G) (fun i ↦ ⟨{i}, by simp⟩)
  refine ⟨u, hu, ?_, hmax⟩
  symm
  apply IsGreatest.csSup_eq
  refine ⟨⟨u, hu, rfl⟩, ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  exact hmax v hv

/-- Every feasible joint law is bounded by the attained graph-conditional maximum. -/
theorem jointConditionalEntropy_le_graphConditionalEntropy {ι : Type*} [Fintype ι]
    (G : SimpleGraph ι) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    {u : ι → Finset ι → ℝ} (hu : u ∈ supportedJointSpace p (graphIndependentCover G)) :
    jointConditionalEntropy u ≤ graphConditionalEntropy G p := by
  obtain ⟨v, hv, he, hmax⟩ := exists_graphConditionalEntropy_maximizer G p hp
  rw [← he]
  exact hmax u hu

end LpSelfSimilar.Entropy
