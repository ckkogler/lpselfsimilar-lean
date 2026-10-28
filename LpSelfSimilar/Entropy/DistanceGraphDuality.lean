module

public import LpSelfSimilar.Entropy.PosetGraphDuality

@[expose] public section

/-!
# Entropy duality for near and far distance graphs

Two distinct vertices are near when their real positions have distance strictly
less than a positive scale. Ordering one vertex before another when their
positions differ by at least that scale makes the near graph an incomparability
graph. The previously proved poset construction therefore gives exact near/far
entropy duality, including the distance-equality endpoint and zero probabilities.
Positions need not be distinct for this graph-theoretic statement.
-/

open scoped BigOperators

namespace LpSelfSimilar.Entropy

/-- The graph of distinct vertices at distance strictly below the given scale. -/
def nearDistanceGraph {ι : Type*} (z : ι → ℝ) (a : ℝ) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ |z i - z j| < a
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, by simpa [abs_sub_comm] using h.2⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

/-- A vertex precedes another if they agree or are separated to the right by the scale. -/
@[instance_reducible]
def distancePartialOrder {ι : Type*} (z : ι → ℝ) (a : ℝ) (ha : 0 < a) : PartialOrder ι where
  le i j := i = j ∨ z i + a ≤ z j
  le_refl i := Or.inl rfl
  le_trans i j k hij hjk := by
    rcases hij with rfl | hij
    · exact hjk
    rcases hjk with rfl | hjk
    · exact Or.inr hij
    · exact Or.inr (by linarith)
  le_antisymm i j hij hji := by
    rcases hij with hij | hij
    · exact hij
    rcases hji with hji | hji
    · exact hji.symm
    · exfalso
      linarith

/-- Nearness is exactly incomparability for the positive distance order. -/
theorem nearDistanceGraph_eq_incomparabilityGraph {ι : Type*}
    (z : ι → ℝ) (a : ℝ) (ha : 0 < a) :
    letI := distancePartialOrder z a ha
    nearDistanceGraph z a = (incomparabilityGraph : SimpleGraph ι) := by
  let := distancePartialOrder z a ha
  ext i j
  change (i ≠ j ∧ |z i - z j| < a) ↔
    (¬(i = j ∨ z i + a ≤ z j) ∧ ¬(j = i ∨ z j + a ≤ z i))
  constructor
  · rintro ⟨hne, habs⟩
    obtain ⟨hl, hu⟩ := abs_lt.mp habs
    constructor
    · rintro (he | hle)
      · exact hne he
      · linarith
    · rintro (he | hle)
      · exact hne he.symm
      · linarith
  · rintro ⟨hl, hu⟩
    refine ⟨fun h ↦ hl (Or.inl h), abs_lt.mpr ⟨?_, ?_⟩⟩
    · have h : z j < z i + a := lt_of_not_ge (fun h ↦ hl (Or.inr h))
      linarith
    · have h : z i < z j + a := lt_of_not_ge (fun h ↦ hu (Or.inr h))
      linarith

/-- The near and far graph entropies add to the entropy of the finite law. -/
theorem graphEntropy_nearDistance_add_compl {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (a : ℝ) (ha : 0 < a) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    graphEntropy (nearDistanceGraph z a) p + graphEntropy (nearDistanceGraph z a)ᶜ p =
      ∑ i, Real.negMulLog (p i) := by
  let := distancePartialOrder z a ha
  rw [nearDistanceGraph_eq_incomparabilityGraph z a ha]
  exact graphEntropy_incomparability_add_compl p hp hsum

end LpSelfSimilar.Entropy
