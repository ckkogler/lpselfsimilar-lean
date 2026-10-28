module

public import LpSelfSimilar.Entropy.ChainCoverPolytope
public import LpSelfSimilar.Entropy.GraphComplement

@[expose] public section

/-!
# Entropy duality for an incomparability graph

At an optimal independent-set coverage `x`, the reciprocal vector `p / x`
satisfies every chain inequality. The weighted interval construction realizes
it as a coverage for the complementary graph. Its logarithmic cost is exactly
the entropy of `p` minus the cost of `x`, proving complementary entropy duality.
All coordinates of zero probability remain in the finite graph.
-/

open Set
open scoped BigOperators

namespace LpSelfSimilar.Entropy

/-- Vertices are adjacent precisely when neither precedes the other. -/
def incomparabilityGraph {ι : Type*} [PartialOrder ι] : SimpleGraph ι where
  Adj i j := ¬i ≤ j ∧ ¬j ≤ i
  symm := ⟨fun _ _ h ↦ h.symm⟩
  loopless := ⟨fun _ h ↦ h.1 le_rfl⟩

/-- Independent sets of the incomparability graph are exactly chains. -/
theorem isIndepSet_incomparabilityGraph_iff {ι : Type*} [PartialOrder ι] (s : Set ι) :
    (incomparabilityGraph : SimpleGraph ι).IsIndepSet s ↔ IsChain (· ≤ ·) s := by
  constructor
  · intro h i hi j hj hij
    have hn := h hi hj hij
    change ¬(¬i ≤ j ∧ ¬j ≤ i) at hn
    change i ≤ j ∨ j ≤ i
    tauto
  · intro h i hi j hj hij hn
    have hc := h hi hj hij
    change ¬i ≤ j ∧ ¬j ≤ i at hn
    rcases hc with hc | hc
    · exact hn.1 hc
    · exact hn.2 hc

/-- Reciprocal logarithmic coverage costs give the exact entropy remainder. -/
theorem graphCoverageCost_div_eq_entropy_sub {ι : Type*} [Fintype ι]
    (p x : ι → ℝ) (hx0 : ∀ i, p i ≠ 0 → 0 < x i) :
    graphCoverageCost p (fun i ↦ p i / x i) =
      (∑ i, Real.negMulLog (p i)) - graphCoverageCost p x := by
  unfold graphCoverageCost
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hpi : p i = 0
  · simp [hpi]
  · rw [Real.log_div hpi (hx0 i hpi).ne', Real.negMulLog]
    ring

/-- Exact complementary entropy duality for a finite partially ordered set. -/
theorem graphEntropy_incomparability_add_compl {ι : Type*} [Fintype ι] [PartialOrder ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    graphEntropy incomparabilityGraph p + graphEntropy incomparabilityGraphᶜ p =
      ∑ i, Real.negMulLog (p i) := by
  classical
  let G : SimpleGraph ι := incomparabilityGraph
  obtain ⟨x, hx, hx0, hxe, hmin⟩ := exists_graphEntropy_minimizer G p hp
  let r : ι → ℝ := fun i ↦ p i / x i
  have hr0 : ∀ i, 0 ≤ r i := fun i ↦ div_nonneg (hp i)
    (independentSetPolytope_coordinate_bounds G hx i).1
  have hrpos : ∀ i, p i ≠ 0 → 0 < r i := fun i hpi ↦
    div_pos (lt_of_le_of_ne (hp i) hpi.symm) (hx0 i hpi)
  have hr : r ∈ independentSetPolytope Gᶜ := by
    refine chain_bound_mem_independentSetPolytope Gᶜ ?_ r hr0 ?_
    · intro i j hij
      change i ≠ j ∧ ¬(¬i ≤ j ∧ ¬j ≤ i) at hij
      have hc : i ≤ j ∨ j ≤ i := by tauto
      rcases hc with hc | hc
      · exact Or.inl (lt_of_le_of_ne hc hij.1)
      · exact Or.inr (lt_of_le_of_ne hc hij.1.symm)
    · intro s hs
      have h := graphEntropy_minimizer_independent_set_bound G p x hx hx0 hmin s
        ((isIndepSet_incomparabilityGraph_iff (s : Set ι)).mpr hs)
      simpa only [hsum] using h
  obtain ⟨y, hy, hy0, hye, hymin⟩ := exists_graphEntropy_minimizer Gᶜ p hp
  have hcost : graphEntropy Gᶜ p ≤ graphCoverageCost p r := by
    rw [← hye]
    exact hymin r hr hrpos
  have he := graphCoverageCost_div_eq_entropy_sub p x hx0
  change graphCoverageCost p r = _ at he
  have hlower := entropy_le_graphEntropy_add_compl G p hp hsum
  change graphEntropy G p + graphEntropy Gᶜ p = _
  linarith

end LpSelfSimilar.Entropy
