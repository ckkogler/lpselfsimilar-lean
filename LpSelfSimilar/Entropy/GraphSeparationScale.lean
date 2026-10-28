module

public import LpSelfSimilar.Entropy.GraphMonotonicity

@[expose] public section

/-!
# Vanishing near entropy at a separation scale

Distinct atoms separated by at least `a` have no near-graph edges at threshold
`a`. The strict inequality in near adjacency includes the boundary correctly.
This gives exact vanishing beyond the dyadic separation exponent.
-/

namespace LpSelfSimilar.Entropy

/-- At or below the minimum distinct-point separation, the near graph is edgeless. -/
theorem nearDistanceGraph_eq_bot_of_separated {ι : Type*} (z : ι → ℝ) (a : ℝ)
    (hsep : ∀ i j, i ≠ j → a ≤ |z i - z j|) : nearDistanceGraph z a = ⊥ := by
  ext i j
  simp only [nearDistanceGraph, SimpleGraph.bot_adj, iff_false, not_and]
  intro hij
  exact not_lt_of_ge (hsep i j hij)

/-- The dyadic near entropy is exactly zero at and beyond a separation exponent. -/
theorem dyadic_near_graphEntropyBits_eq_zero_of_separated {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (s : ℝ)
    (hsep : ∀ i j, i ≠ j → (2 : ℝ) ^ (-s) ≤ |z i - z j|)
    {j : ℝ} (hj : s ≤ j) :
    graphEntropyBits (nearDistanceGraph z ((2 : ℝ) ^ (-j))) p = 0 := by
  have hscale : (2 : ℝ) ^ (-j) ≤ (2 : ℝ) ^ (-s) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_neg hj)
  rw [nearDistanceGraph_eq_bot_of_separated z _ (fun i k hik ↦
    hscale.trans (hsep i k hik))]
  simp [graphEntropyBits, graphEntropy_bot p hp]

end LpSelfSimilar.Entropy
