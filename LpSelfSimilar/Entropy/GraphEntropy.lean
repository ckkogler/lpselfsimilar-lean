module

public import LpSelfSimilar.Entropy.GraphPolytope
public import LpSelfSimilar.Analysis.WeightedLogSupporting

@[expose] public section

/-!
# Finite graph entropy and an attained optimum

Graph entropy here uses natural logarithms. It minimizes the logarithmic
coverage cost over the independent-set polytope, requiring positive coverage
exactly on the support of the input weights. Thus zero probabilities cause no
extra hypothesis, and a positively weighted uncovered vertex is never assigned
the library's totalized value of `log 0`. The infimum is attained, and its
first-order inequality bounds the reciprocal-weight sum on each independent set.
-/

open Set
open scoped BigOperators

namespace LpSelfSimilar.Entropy

/-- Natural-logarithm cost of a coverage vector for a finite weight vector. -/
noncomputable def graphCoverageCost {ι : Type*} [Fintype ι] (p x : ι → ℝ) : ℝ :=
  ∑ i, p i * (-Real.log (x i))

/-- Graph entropy in nats, with positive coverage on the probability support. -/
noncomputable def graphEntropy {ι : Type*} [Fintype ι] (G : SimpleGraph ι)
    (p : ι → ℝ) : ℝ :=
  sInf (graphCoverageCost p '' {x | x ∈ independentSetPolytope G ∧
    ∀ i, p i ≠ 0 → 0 < x i})

/-- Logarithmic coverage cost is nonnegative on its meaningful domain. -/
theorem graphCoverageCost_nonneg {ι : Type*} [Fintype ι] (G : SimpleGraph ι)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) {x : ι → ℝ}
    (hx : x ∈ independentSetPolytope G) (hx0 : ∀ i, p i ≠ 0 → 0 < x i) :
    0 ≤ graphCoverageCost p x := by
  apply Finset.sum_nonneg
  intro i _
  by_cases hpi : p i = 0
  · simp [hpi]
  · exact mul_nonneg (hp i) (neg_nonneg.mpr
      (Real.log_nonpos (hx0 i hpi).le (independentSetPolytope_coordinate_bounds G hx i).2))

/-- Every finite graph has an attained entropy optimum, including zero weights. -/
theorem exists_graphEntropy_minimizer {ι : Type*} [Fintype ι] (G : SimpleGraph ι)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) :
    ∃ x ∈ independentSetPolytope G, (∀ i, p i ≠ 0 → 0 < x i) ∧
      graphCoverageCost p x = graphEntropy G p ∧
      ∀ y ∈ independentSetPolytope G, (∀ i, p i ≠ 0 → 0 < y i) →
        graphCoverageCost p x ≤ graphCoverageCost p y := by
  classical
  have hu : ∃ u ∈ independentSetPolytope G, ∀ i, p i ≠ 0 → 0 < u i := by
    cases isEmpty_or_nonempty ι
    · refine ⟨vertexSetIndicator ∅, vertexSetIndicator_mem_polytope G ∅ ?_, ?_⟩
      · simp [SimpleGraph.isIndepSet_iff]
      · intro i
        exact isEmptyElim i
    · refine ⟨_, uniform_mem_independentSetPolytope G, fun i _ ↦ ?_⟩
      exact inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
  obtain ⟨x, hxK, hx0, hmin⟩ := exists_weighted_log_minimizer_on_support p hp
    (independentSetPolytope G) (isCompact_independentSetPolytope G)
    (fun z hz i ↦ (independentSetPolytope_coordinate_bounds G hz i).1) hu
  refine ⟨x, hxK, hx0, ?_, hmin⟩
  symm
  apply IsLeast.csInf_eq
  refine ⟨⟨x, ⟨hxK, hx0⟩, rfl⟩, ?_⟩
  rintro _ ⟨y, ⟨hyK, hy0⟩, rfl⟩
  exact hmin y hyK hy0

/-- The actual infimum is nonnegative; its feasible domain is never empty. -/
theorem graphEntropy_nonneg {ι : Type*} [Fintype ι] (G : SimpleGraph ι)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) : 0 ≤ graphEntropy G p := by
  obtain ⟨x, hx, hx0, he, _⟩ := exists_graphEntropy_minimizer G p hp
  rw [← he]
  exact graphCoverageCost_nonneg G p hp hx hx0

/-- The reciprocal weights at an optimum obey every independent-set constraint. -/
theorem graphEntropy_minimizer_independent_set_bound {ι : Type*} [Fintype ι]
    (G : SimpleGraph ι) (p x : ι → ℝ)
    (hxK : x ∈ independentSetPolytope G) (hx0 : ∀ i, p i ≠ 0 → 0 < x i)
    (hmin : ∀ y ∈ independentSetPolytope G, (∀ i, p i ≠ 0 → 0 < y i) →
      graphCoverageCost p x ≤ graphCoverageCost p y)
    (s : Finset ι) (hs : G.IsIndepSet (s : Set ι)) :
    (∑ i ∈ s, p i / x i) ≤ ∑ i, p i := by
  classical
  have h := weighted_log_minimizer_support_bound p x (independentSetPolytope G)
    (convex_independentSetPolytope G)
    (fun z hz i ↦ (independentSetPolytope_coordinate_bounds G hz i).1) hxK hx0 hmin
    (vertexSetIndicator_mem_polytope G s hs)
  simpa [vertexSetIndicator, mul_ite, ite_div] using h

end LpSelfSimilar.Entropy
