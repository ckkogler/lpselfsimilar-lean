module

public import LpSelfSimilar.Entropy.CancellationParameters

@[expose] public section

/-!
# The uniform integrated cancellation rate

The rate retains the exact remainder at `J=L/rho`. Bounding that remainder by
`rho/(10 L log 2)` gives the explicit lower bound with coefficients `13/40` and
`84/25`. No parameter-dependent replacement for a fixed numerical coefficient
is introduced.
-/

namespace LpSelfSimilar.Entropy

/-- Exact cancellation rate after integrating from `(4/25)*rho*n` to `L*n+4`. -/
noncomputable def bandCancellationRate (ρ L : ℝ) : ℝ :=
  ((84 / 25 : ℝ) * ρ - (L - (4 / 25 : ℝ) * ρ) * cancellationRemainder (L / ρ)) /
    cancellationSlope (L / ρ)

/-- The entropy-normalized separation parameter lies in the required range. -/
theorem three_le_separation_entropy_ratio {ρ L : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L) : 3 ≤ L / ρ := by
  apply (le_div_iff₀ hρ).mpr
  nlinarith

/-- Exact uniform lower bound for the cancellation rate. -/
theorem bandCancellationRate_lower_bound {ρ L : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L) :
    ((13 / 40 : ℝ) * ρ * Real.log 2 / Real.log (150 * (L / ρ))) *
      (84 / 25 - 1 / (10 * Real.log 2)) ≤ bandCancellationRate ρ L := by
  have hL0 : 0 < L := by linarith
  have hJ := three_le_separation_entropy_ratio hρ hρ1 hL
  have hJ0 : 0 < L / ρ := div_pos hL0 hρ
  have hα := cancellationSlope_pos hJ
  have hβ0 := cancellationRemainder_nonneg hJ0
  have hβ : cancellationRemainder (L / ρ) ≤ ρ / (10 * L * Real.log 2) := by
    have he : 1 / (10 * (L / ρ) * Real.log 2) = ρ / (10 * L * Real.log 2) := by
      field_simp
    simpa only [he] using cancellationRemainder_le hJ0
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hproduct : (L - (4 / 25 : ℝ) * ρ) * cancellationRemainder (L / ρ) ≤
      ρ / (10 * Real.log 2) := by
    calc
      _ ≤ L * cancellationRemainder (L / ρ) :=
        mul_le_mul_of_nonneg_right (by linarith) hβ0
      _ ≤ L * (ρ / (10 * L * Real.log 2)) := mul_le_mul_of_nonneg_left hβ hL0.le
      _ = ρ / (10 * Real.log 2) := by field_simp
  have hn : ρ * (84 / 25 - 1 / (10 * Real.log 2)) ≤
      (84 / 25 : ℝ) * ρ - (L - (4 / 25 : ℝ) * ρ) * cancellationRemainder (L / ρ) := by
    calc
      ρ * (84 / 25 - 1 / (10 * Real.log 2)) =
          (84 / 25 : ℝ) * ρ - ρ / (10 * Real.log 2) := by ring
      _ ≤ _ := sub_le_sub_left hproduct _
  have he : ((13 / 40 : ℝ) * ρ * Real.log 2 / Real.log (150 * (L / ρ))) *
      (84 / 25 - 1 / (10 * Real.log 2)) =
      (ρ * (84 / 25 - 1 / (10 * Real.log 2))) / cancellationSlope (L / ρ) := by
    unfold cancellationSlope
    field_simp
    <;> ring
  rw [he]
  exact div_le_div_of_nonneg_right hn hα.le

end LpSelfSimilar.Entropy
