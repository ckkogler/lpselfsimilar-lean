module

public import LpSelfSimilar.Entropy.DyadicBandFamily
public import LpSelfSimilar.Entropy.CancellationParameters
public import LpSelfSimilar.Entropy.DistanceBandEntropyBudget

@[expose] public section

/-!
# Integrating the cancellation of actual maximizing conditional laws

The same measurable joint family supplies both entropy and cancellation.
Its cancellation is bounded and hence integrable. Integrating the specialized
sixteen-atom bound and subtracting the exact interval-length remainder gives
the finite-block lower bound, including the four-unit endpoint error.
-/

open MeasureTheory Set
open scoped BigOperators

namespace LpSelfSimilar.Entropy

/-- Feasibility of a band family already implies that its point weights are nonnegative. -/
theorem MaximizingBandFamily.pointWeight_nonneg {ι : Type*} [Fintype ι]
    {z p : ι → ℝ} (F : MaximizingBandFamily z p) (i : ι) : 0 ≤ p i := by
  rw [← (F.supported 0).2.1 i]
  exact Finset.sum_nonneg (fun j _ ↦ (F.supported 0).1 i j)

/-- The exact logarithmic slope and remainder apply to the chosen family. -/
theorem MaximizingBandFamily.entropy_le_cancellation_log_parameter {ι : Type*} [Fintype ι]
    {z p : ι → ℝ} (F : MaximizingBandFamily z p) (hsum : ∑ i, p i = 1)
    {J : ℝ} (hJ : 3 ≤ J) (j : ℝ) :
    distanceBandConditionalEntropyBits z ((2 : ℝ) ^ (-j)) p ≤
      cancellationSlope J * F.cancellation j + cancellationRemainder J := by
  have h := F.entropy_le_cancellation hsum (cancellationSlope_pos hJ) j
  rwa [cancellation_remainder_at_slope hJ] at h

/-- Integrating retains the actual interval length multiplying the remainder. -/
theorem MaximizingBandFamily.integral_entropy_le_cancellation {ι : Type*} [Fintype ι]
    {z p : ι → ℝ} (F : MaximizingBandFamily z p) (hsum : ∑ i, p i = 1)
    {J : ℝ} (hJ : 3 ≤ J) (a b : ℝ) (hab : a ≤ b) :
    (∫ j in a..b, distanceBandConditionalEntropyBits z ((2 : ℝ) ^ (-j)) p) ≤
      cancellationSlope J * (∫ j in a..b, F.cancellation j) +
        (b - a) * cancellationRemainder J := by
  have hi := F.intervalIntegrable_cancellation hsum a b
  have h := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_dyadic_distanceBandConditionalEntropyBits z p a b)
    ((hi.const_mul (cancellationSlope J)).add intervalIntegrable_const)
    (fun j _ ↦ F.entropy_le_cancellation_log_parameter hsum hJ j)
  rw [intervalIntegral.integral_add (hi.const_mul (cancellationSlope J)) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at h
  exact h

/-- Exact finite-n cancellation budget before fixing the lower cutoff fraction. -/
theorem MaximizingBandFamily.cancellation_integral_lower_bound {ι : Type*} [Fintype ι]
    {z p : ι → ℝ} (F : MaximizingBandFamily z p) (hsum : ∑ i, p i = 1)
    (θ ρ c L J : ℝ) (n : ℕ) (hθ : θ < 1) (hρ : ρ ∈ Icc 0 1)
    (hc : c ∈ Icc 0 1) (hL : 1 ≤ L) (hJ : 3 ≤ J)
    (hz : ∀ i, |z i| ≤ 1 / (1 - θ))
    (hentropy : ρ * n ≤ (∑ i, Real.negMulLog (p i)) / Real.log 2)
    (hsep : ∀ i k, i ≠ k → (2 : ℝ) ^ (-(L * n)) ≤ |z i - z k|) :
    (n * (4 * (1 - c) * ρ - (L - c * ρ) * cancellationRemainder J) -
        (4 * (Real.log (2 / (1 - θ) + 2) / Real.log 2) + 4 * cancellationRemainder J)) /
        cancellationSlope J ≤ ∫ j in c * ρ * n..L * n + 4, F.cancellation j := by
  have hcr : c * ρ ≤ 1 := (mul_le_mul_of_nonneg_right hc.2 hρ.1).trans
    (by simpa using hρ.2)
  have hab : c * ρ * n ≤ L * n + 4 := by
    have := mul_le_mul_of_nonneg_right (hcr.trans hL) (Nat.cast_nonneg n)
    linarith
  have hlower := distanceBand_integrated_entropy_budget z p F.pointWeight_nonneg hsum
    θ ρ c L n hθ hρ hc hL hz hentropy hsep
  have hupper := F.integral_entropy_le_cancellation hsum hJ (c * ρ * n) (L * n + 4) hab
  apply (div_le_iff₀ (cancellationSlope_pos hJ)).mpr
  nlinarith

end LpSelfSimilar.Entropy
