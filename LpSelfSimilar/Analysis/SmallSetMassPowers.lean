module

public import LpSelfSimilar.Analysis.SmallSetMassIteration
public import LpSelfSimilar.Analysis.MassDecayExponent

@[expose] public section

/-!
# Power bounds from geometric small-set masses

Choose the integer whose consecutive geometric volumes bracket a positive
budget. Monotonicity interpolates the geometric estimate with exactly
alpha = log(1/beta)/log D. The explicit constant also covers budgets above
the starting scale, using only that the measured mass is a probability.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LpSelfSimilar.Analysis

/-- Geometric small-set estimates imply the exact real-power bound at all positive budgets. -/
theorem smallSetMass_le_rpow_of_geometric {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] {R D β : ℝ}
    (hR : 0 < R) (hD : 1 < D) (hβ : 0 < β) (hβ1 : β < 1)
    (hmass : ∀ n : ℕ, smallSetMass μ ν (ENNReal.ofReal (R / D ^ n)) ≤ ENNReal.ofReal β ^ n)
    {t : ℝ} (ht : 0 < t) :
    smallSetMass μ ν (ENNReal.ofReal t) ≤
      ENNReal.ofReal ((1 / (β * R ^ massDecayExponent β D)) * t ^ massDecayExponent β D) := by
  let α := massDecayExponent β D
  let C := 1 / (β * R ^ α)
  have hα : 0 < α := massDecayExponent_pos hβ hβ1 hD
  have hD0 : 0 < D := zero_lt_one.trans hD
  have hRp : 0 < R ^ α := Real.rpow_pos_of_pos hR _
  have hC : 0 < C := by dsimp only [C]; positivity
  change smallSetMass μ ν (ENNReal.ofReal t) ≤ ENNReal.ofReal (C * t ^ α)
  by_cases htR : t ≤ R
  · obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near
      ((le_div_iff₀ ht).mpr (by simpa using htR)) hD
    have hupper : t ≤ R / D ^ n := by
      apply (le_div_iff₀ (pow_pos hD0 n)).mpr
      have h := (le_div_iff₀ ht).mp hn
      nlinarith
    have hlower : R / D ^ (n + 1) < t := by
      apply (div_lt_iff₀ (pow_pos hD0 (n + 1))).mpr
      have h := (div_lt_iff₀ ht).mp hn'
      nlinarith
    have hpow := Real.rpow_le_rpow (div_nonneg hR.le (pow_nonneg hD0.le _))
      hlower.le hα.le
    rw [geometric_volume_rpow_massDecayExponent hR.le hβ hD] at hpow
    have heq : C * (R ^ α * β ^ (n + 1)) = β ^ n := by
      dsimp only [C]
      rw [pow_succ]
      field_simp [hβ.ne', hRp.ne']
    have hbound : β ^ n ≤ C * t ^ α := by
      rw [← heq]
      exact mul_le_mul_of_nonneg_left hpow hC.le
    calc
      _ ≤ smallSetMass μ ν (ENNReal.ofReal (R / D ^ n)) :=
        smallSetMass_mono μ ν (ENNReal.ofReal_le_ofReal hupper)
      _ ≤ ENNReal.ofReal β ^ n := hmass n
      _ = ENNReal.ofReal (β ^ n) := (ENNReal.ofReal_pow hβ.le n).symm
      _ ≤ ENNReal.ofReal (C * t ^ α) := ENNReal.ofReal_le_ofReal hbound
  · have hpow : R ^ α ≤ t ^ α := Real.rpow_le_rpow hR.le (le_of_not_ge htR) hα.le
    have heq : C * R ^ α = 1 / β := by
      dsimp only [C]
      field_simp [hβ.ne', hRp.ne']
    have hone : 1 ≤ C * t ^ α := by
      calc
        1 ≤ 1 / β := (le_div_iff₀ hβ).mpr (by simpa using hβ1.le)
        _ = C * R ^ α := heq.symm
        _ ≤ C * t ^ α := mul_le_mul_of_nonneg_left hpow hC.le
    apply (smallSetMass_le μ ν (b := 1) fun E _ _ =>
      (measure_mono (subset_univ E)).trans_eq measure_univ).trans
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hone

/-- A small-set recurrence supplies a global power bound with an explicit positive constant. -/
theorem smallSetMass_le_rpow_of_recurrence {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] {r D β : ℝ}
    (hr : 0 < r) (hD : 1 < D) (hβ : 0 < β) (hβ1 : β < 1)
    (hrec : ∀ t : ℝ, 0 < t → t < r →
      smallSetMass μ ν (ENNReal.ofReal t) ≤
        ENNReal.ofReal β * smallSetMass μ ν (ENNReal.ofReal (D * t))) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
      smallSetMass μ ν (ENNReal.ofReal t) ≤ ENNReal.ofReal (C * t ^ massDecayExponent β D) := by
  have hR : 0 < r / 2 := half_pos hr
  refine ⟨1 / (β * (r / 2) ^ massDecayExponent β D), by positivity, ?_⟩
  intro t ht
  exact smallSetMass_le_rpow_of_geometric μ ν hR hD hβ hβ1
    (smallSetMass_le_geometric_of_recurrence μ ν hR (half_lt_self hr) hD _ hrec) ht

end LpSelfSimilar.Analysis
