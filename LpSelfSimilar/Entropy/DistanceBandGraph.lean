module

public import LpSelfSimilar.Entropy.DistanceGraphDuality
public import LpSelfSimilar.Entropy.GraphUnion
public import LpSelfSimilar.Geometry.FiniteSeparatedCardinality

@[expose] public section

/-!
# Distance-band graphs and the entropy budget at one scale

The complement of the graph for distances in `[a,b)` is the union of the near
`a` graph and the far `b` graph. Graph-union subadditivity and exact near/far
duality give the difference of the two near-graph entropies. For `[a,16a)`, every
clique has at most sixteen vertices; the strict upper endpoint is retained.
-/

open scoped BigOperators

namespace LpSelfSimilar.Entropy

/-- Distinct vertices whose distances lie in a half-open band. -/
def distanceBandGraph {ι : Type*} (z : ι → ℝ) (a b : ℝ) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ a ≤ |z i - z j| ∧ |z i - z j| < b
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, by simpa [abs_sub_comm] using h.2⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

/-- The band complement consists of distances below the lower or at least the upper scale. -/
theorem distanceBandGraph_compl_eq_sup {ι : Type*} (z : ι → ℝ) (a b : ℝ) :
    (distanceBandGraph z a b)ᶜ = nearDistanceGraph z a ⊔ (nearDistanceGraph z b)ᶜ := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · suffices hs : (a ≤ |z i - z j| → b ≤ |z i - z j|) ↔
        (|z i - z j| < a ∨ b ≤ |z i - z j|) by
      simpa [SimpleGraph.compl_adj, SimpleGraph.sup_adj, distanceBandGraph,
        nearDistanceGraph, hij, not_lt] using hs
    constructor
    · intro h
      by_cases hd : a ≤ |z i - z j|
      · exact Or.inr (h hd)
      · exact Or.inl (lt_of_not_ge hd)
    · rintro (hl | hu) hd
      · exact False.elim (not_lt_of_ge hd hl)
      · exact hu

/-- The band complement's coverage cost leaves the exact near-entropy increment. -/
theorem entropy_sub_band_compl_ge_near_difference {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (a b : ℝ) (hb : 0 < b) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    graphEntropy (nearDistanceGraph z b) p - graphEntropy (nearDistanceGraph z a) p ≤
      (∑ i, Real.negMulLog (p i)) - graphEntropy (distanceBandGraph z a b)ᶜ p := by
  have hu := graphEntropy_sup_le_add (nearDistanceGraph z a) (nearDistanceGraph z b)ᶜ p hp
  have hd := graphEntropy_nearDistance_add_compl z b hb p hp hsum
  rw [distanceBandGraph_compl_eq_sup]
  linarith

/-- A clique in the half-open sixteen-scale band has at most sixteen vertices. -/
theorem distanceBandGraph_clique_card_le_sixteen {ι : Type*}
    (z : ι → ℝ) (a : ℝ) (ha : 0 < a) (s : Finset ι)
    (hs : (distanceBandGraph z a (16 * a)).IsClique (s : Set ι)) : s.card ≤ 16 := by
  apply Geometry.card_le_of_separated_strict_diameter s z a ha 16
  · intro i hi j hj hij
    exact (hs hi hj hij).2.1
  · intro i hi j hj
    by_cases hij : i = j
    · subst j
      simp only [sub_self, abs_zero, Nat.cast_ofNat]
      positivity
    · exact (hs hi hj hij).2.2

end LpSelfSimilar.Entropy
