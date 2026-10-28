module

public import LpSelfSimilar.Entropy.GraphConditionalVariational

@[expose] public section

/-!
# Graph and conditional entropies in bits

The variational library uses natural logarithms. Dividing by the strictly
positive constant `log 2` gives the base-two entropies used in dyadic scale
budgets, preserving the exact near/far identity and sixteen-scale band bound.
-/

open scoped BigOperators

namespace LpSelfSimilar.Entropy

/-- Graph entropy in bits. -/
noncomputable def graphEntropyBits {ι : Type*} [Fintype ι]
    (G : SimpleGraph ι) (p : ι → ℝ) : ℝ := graphEntropy G p / Real.log 2

/-- The attained greatest independent-support conditional entropy in bits. -/
noncomputable def graphConditionalEntropyBits {ι : Type*} [Fintype ι]
    (G : SimpleGraph ι) (p : ι → ℝ) : ℝ := graphConditionalEntropy G p / Real.log 2

/-- The greatest conditional entropy for the half-open sixteen-scale distance band, in bits. -/
noncomputable def distanceBandConditionalEntropyBits {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (a : ℝ) (p : ι → ℝ) : ℝ :=
  graphConditionalEntropyBits (distanceBandGraph z a (16 * a))ᶜ p

theorem graphConditionalEntropyBits_eq_entropy_sub_graphEntropyBits {ι : Type*} [Fintype ι]
    (G : SimpleGraph ι) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    graphConditionalEntropyBits G p =
      (∑ i, Real.negMulLog (p i)) / Real.log 2 - graphEntropyBits G p := by
  simp only [graphConditionalEntropyBits, graphEntropyBits,
    graphConditionalEntropy_eq_entropy_sub_graphEntropy G p hp hsum, sub_div]

/-- Exact complementary identity with base-two entropy. -/
theorem graphEntropyBits_near_add_compl {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (a : ℝ) (ha : 0 < a) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    graphEntropyBits (nearDistanceGraph z a) p + graphEntropyBits (nearDistanceGraph z a)ᶜ p =
      (∑ i, Real.negMulLog (p i)) / Real.log 2 := by
  simp only [graphEntropyBits, ← add_div, graphEntropy_nearDistance_add_compl z a ha p hp hsum]

/-- The exact base-two band inequality for the attained greatest conditional entropy. -/
theorem near_difference_le_distanceBandConditionalEntropyBits {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (a : ℝ) (ha : 0 < a) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    graphEntropyBits (nearDistanceGraph z (16 * a)) p -
      graphEntropyBits (nearDistanceGraph z a) p ≤
      distanceBandConditionalEntropyBits z a p := by
  unfold graphEntropyBits distanceBandConditionalEntropyBits graphConditionalEntropyBits
  rw [← sub_div]
  exact div_le_div_of_nonneg_right (near_difference_le_band_graphConditionalEntropy z a ha p hp hsum)
    (Real.log_nonneg (by norm_num))

end LpSelfSimilar.Entropy
