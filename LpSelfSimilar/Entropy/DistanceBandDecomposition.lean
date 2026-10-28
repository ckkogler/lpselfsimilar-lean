module

public import LpSelfSimilar.Entropy.DistanceBandGraph
public import LpSelfSimilar.Entropy.GraphConditionalDecomposition

@[expose] public section

/-!
# Actual finite probability mixtures in a sixteen-scale distance band

The decomposition below is constructed from an optimal cover of the band
complement. Its positive-mass conditional laws are supported on at most sixteen
points with pairwise distances in `[a,16a)`. Their average is the original law,
and their expected entropy dominates the difference of the near-graph entropies.
This is the constructive single-scale content behind the integrated band budget.
-/

open scoped BigOperators

namespace LpSelfSimilar.Entropy

/-- A finite distance-band mixture with exact near-entropy gain and sixteen-point supports. -/
theorem exists_distanceBand_decomposition {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (a : ℝ) (ha : 0 < a) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    ∃ (κ : Type) (_ : Fintype κ) (q : κ → ℝ) (r : κ → ι → ℝ) (cover : κ → Finset ι),
      (∀ j, 0 ≤ q j) ∧ (∑ j, q j = 1) ∧ (∀ j i, 0 ≤ r j i) ∧
      (∀ j, 0 < q j → ∑ i, r j i = 1) ∧
      (∀ j i, i ∉ cover j → r j i = 0) ∧ (∀ j, (cover j).card ≤ 16) ∧
      (∀ j, ∀ i ∈ cover j, ∀ k ∈ cover j, i ≠ k →
        a ≤ |z i - z k| ∧ |z i - z k| < 16 * a) ∧
      (∀ i, ∑ j, q j * r j i = p i) ∧
      graphEntropy (nearDistanceGraph z (16 * a)) p - graphEntropy (nearDistanceGraph z a) p ≤
        ∑ j, q j * ∑ i, Real.negMulLog (r j i) := by
  obtain ⟨κ, hκ, q, r, cover, hq, hqsum, hr, hrnorm, hrsupp, hcover, hmix, hent⟩ :=
    exists_graph_conditional_decomposition (distanceBandGraph z a (16 * a))ᶜ p hp hsum
  have hclique (j : κ) : (distanceBandGraph z a (16 * a)).IsClique (cover j : Set ι) := by
    simpa using hcover j
  refine ⟨κ, hκ, q, r, cover, hq, hqsum, hr, hrnorm, hrsupp, ?_, ?_, hmix, ?_⟩
  · intro j
    exact distanceBandGraph_clique_card_le_sixteen z a ha (cover j) (hclique j)
  · intro j i hi k hk hik
    exact (hclique j hi hk hik).2
  · exact (entropy_sub_band_compl_ge_near_difference z a (16 * a)
      (by positivity) p hp hsum).trans hent

end LpSelfSimilar.Entropy
