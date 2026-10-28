module

public import LpSelfSimilar.Entropy.DistanceBandScaleBudget
public import LpSelfSimilar.Entropy.QuantizedNearEntropy

@[expose] public section

/-!
# The quantitative integrated distance-band entropy bound

Combining the actual finite-cell quantization with the four-step telescoping
identity proves the finite-law budget used for Bernoulli digit blocks. The
constant is `log(2/(1-theta)+2)/log 2`, with the additive two inside the logarithm.
No measurable-choice or integrability hypothesis is left to the caller.
-/

open MeasureTheory
open scoped BigOperators

namespace LpSelfSimilar.Entropy

/-- The scale budget for any bounded finite law with the stated dyadic separation. -/
theorem distanceBand_integral_ge_quantized_entropy {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (lo hi a b : ℝ) (hlohi : lo ≤ hi) (ha : 0 ≤ a) (hab : a ≤ b)
    (hz : ∀ i, z i ∈ Set.Icc lo hi)
    (hsep : ∀ i k, i ≠ k → (2 : ℝ) ^ (-b) ≤ |z i - z k|) :
    4 * ((∑ i, Real.negMulLog (p i)) / Real.log 2 - a -
      Real.log (hi - lo + 2) / Real.log 2) ≤
      ∫ j in a..b + 4, distanceBandConditionalEntropyBits z ((2 : ℝ) ^ (-j)) p := by
  exact (mul_le_mul_of_nonneg_left
    (dyadic_near_graphEntropyBits_ge_of_interval z p hp hsum lo hi a hlohi ha hz)
    (by norm_num : (0 : ℝ) ≤ 4)).trans
    (four_mul_near_entropy_le_distanceBand_integral z p hp hsum a b hab hsep)

/-- The finite-law form of the integrated entropy budget, retaining its exact constant. -/
theorem distanceBand_integrated_entropy_budget {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (θ ρ c L : ℝ) (n : ℕ) (hθ : θ < 1) (hρ : ρ ∈ Set.Icc 0 1)
    (hc : c ∈ Set.Icc 0 1) (hL : 1 ≤ L)
    (hz : ∀ i, |z i| ≤ 1 / (1 - θ))
    (hentropy : ρ * n ≤ (∑ i, Real.negMulLog (p i)) / Real.log 2)
    (hsep : ∀ i k, i ≠ k → (2 : ℝ) ^ (-(L * n)) ≤ |z i - z k|) :
    4 * (1 - c) * ρ * n - 4 * (Real.log (2 / (1 - θ) + 2) / Real.log 2) ≤
      ∫ j in c * ρ * n..L * n + 4,
        distanceBandConditionalEntropyBits z ((2 : ℝ) ^ (-j)) p := by
  have hr : 0 < 1 / (1 - θ) := one_div_pos.mpr (sub_pos.mpr hθ)
  have hcr : c * ρ ≤ 1 := (mul_le_mul_of_nonneg_right hc.2 hρ.1).trans
    (by simpa using hρ.2)
  have hab : c * ρ * n ≤ L * n :=
    mul_le_mul_of_nonneg_right (hcr.trans hL) (Nat.cast_nonneg n)
  have h := distanceBand_integral_ge_quantized_entropy z p hp hsum
    (-(1 / (1 - θ))) (1 / (1 - θ)) (c * ρ * n) (L * n)
    (by linarith) (mul_nonneg (mul_nonneg hc.1 hρ.1) (Nat.cast_nonneg n)) hab (fun i ↦ abs_le.mp (hz i)) hsep
  have he : 1 / (1 - θ) - -(1 / (1 - θ)) + 2 = 2 / (1 - θ) + 2 := by ring
  rw [he] at h
  nlinarith

end LpSelfSimilar.Entropy
