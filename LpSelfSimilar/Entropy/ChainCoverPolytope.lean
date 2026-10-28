module

public import LpSelfSimilar.Entropy.MeasurableCoverPolytope
public import LpSelfSimilar.Combinatorics.WeightedChains

@[expose] public section

/-!
# Weighted chain bounds yield antichain coverages

The maximum-predecessor-chain construction supplies actual half-open intervals
in the unit interval. Intervals for comparable vertices are disjoint. Uniform
sampling therefore realizes the desired inclusion probabilities, proving
polytope membership from the chain inequalities without a linear-programming
or graph-duality assumption.
-/

open Set
open scoped BigOperators

namespace LpSelfSimilar.Entropy

/-- A nonnegative vector satisfying all unit chain bounds is an antichain coverage. -/
theorem chain_bound_mem_independentSetPolytope {ι : Type*} [Finite ι] [PartialOrder ι]
    (G : SimpleGraph ι) (hG : ∀ i j, G.Adj i j → i < j ∨ j < i)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hchain : ∀ s : Finset ι, IsChain (· ≤ ·) (s : Set ι) → (∑ j ∈ s, w j) ≤ 1) :
    w ∈ independentSetPolytope G := by
  classical
  let := Fintype.ofFinite ι
  apply interval_cover_mem_independentSetPolytope G
    (Combinatorics.predecessorChainWeight w) w
    (Combinatorics.predecessorChainWeight_nonneg w) hw
    (Combinatorics.predecessorChainWeight_add_le_one w hchain)
  intro i j hij
  apply Set.disjoint_left.mpr
  intro t hti htj
  rcases hG i j hij with hij | hji
  · have h := Combinatorics.predecessorChainWeight_add_le w hij
    linarith [hti.2, htj.1]
  · have h := Combinatorics.predecessorChainWeight_add_le w hji
    linarith [htj.2, hti.1]

end LpSelfSimilar.Entropy
