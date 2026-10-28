module

public import LpSelfSimilar.Entropy.CancellationIntegral
public import LpSelfSimilar.Entropy.CancellationRate

@[expose] public section

/-!
# The exact finite-block cancellation budget

Fixing `c=4/25` and `J=L/rho` yields the rate `W` and the endpoint error
`(4*Ctheta+4*beta)/alpha`. This is an exact finite-n inequality, so no limiting
or asymptotic argument is required at this stage.
-/

open MeasureTheory Set
open scoped BigOperators

namespace LpSelfSimilar.Entropy

/-- Exact cancellation integral with the rate and finite-n error kept separate. -/
theorem MaximizingBandFamily.cancellation_integral_lower_bound_explicit {ι : Type*} [Fintype ι]
    {z p : ι → ℝ} (F : MaximizingBandFamily z p) (hsum : ∑ i, p i = 1)
    (θ ρ L : ℝ) (n : ℕ) (hθ : θ < 1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L)
    (hz : ∀ i, |z i| ≤ 1 / (1 - θ))
    (hentropy : ρ * n ≤ (∑ i, Real.negMulLog (p i)) / Real.log 2)
    (hsep : ∀ i k, i ≠ k → (2 : ℝ) ^ (-(L * n)) ≤ |z i - z k|) :
    n * bandCancellationRate ρ L -
        (4 * (Real.log (2 / (1 - θ) + 2) / Real.log 2) +
          4 * cancellationRemainder (L / ρ)) / cancellationSlope (L / ρ) ≤
      ∫ j in (4 / 25 : ℝ) * ρ * n..L * n + 4, F.cancellation j := by
  have h := F.cancellation_integral_lower_bound hsum θ ρ (4 / 25) L (L / ρ) n hθ
    ⟨hρ.le, hρ1⟩ (by norm_num) (by linarith)
    (three_le_separation_entropy_ratio hρ hρ1 hL) hz hentropy hsep
  have he : n * bandCancellationRate ρ L -
      (4 * (Real.log (2 / (1 - θ) + 2) / Real.log 2) +
        4 * cancellationRemainder (L / ρ)) / cancellationSlope (L / ρ) =
      (n * (4 * (1 - (4 / 25 : ℝ)) * ρ -
        (L - (4 / 25 : ℝ) * ρ) * cancellationRemainder (L / ρ)) -
        (4 * (Real.log (2 / (1 - θ) + 2) / Real.log 2) +
          4 * cancellationRemainder (L / ρ))) / cancellationSlope (L / ρ) := by
    unfold bandCancellationRate
    ring
  rw [he]
  exact h

end LpSelfSimilar.Entropy
