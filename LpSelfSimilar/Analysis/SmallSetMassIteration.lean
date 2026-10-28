module

public import LpSelfSimilar.Analysis.SmallSetMass
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Tactic

@[expose] public section

/-!
# Geometric iteration of a small-set mass recurrence

Starting strictly below the recurrence's volume cutoff avoids an endpoint
issue. At the geometric volumes R/D^n, iteration gives a mass bound beta^n.
This form interfaces directly with geometric tail-to-moment estimates.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LpSelfSimilar.Analysis

/-- A contracting small-set recurrence gives its exact geometric mass bounds. -/
theorem smallSetMass_le_geometric_of_recurrence {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] {r R D : ℝ} (hR : 0 < R)
    (hRr : R < r) (hD : 1 < D) (β : ℝ≥0∞)
    (hrec : ∀ t : ℝ, 0 < t → t < r →
      smallSetMass μ ν (ENNReal.ofReal t) ≤
        β * smallSetMass μ ν (ENNReal.ofReal (D * t))) (n : ℕ) :
    smallSetMass μ ν (ENNReal.ofReal (R / D ^ n)) ≤ β ^ n := by
  have hD0 : 0 < D := zero_lt_one.trans hD
  induction n with
  | zero =>
    simp only [pow_zero, div_one]
    apply smallSetMass_le μ ν
    intro E hE hv
    exact (measure_mono (subset_univ E)).trans_eq measure_univ
  | succ n ih =>
    have ht : 0 < R / D ^ (n + 1) := div_pos hR (pow_pos hD0 _)
    have htr : R / D ^ (n + 1) < r :=
      (div_le_self hR.le (one_le_pow₀ hD.le)).trans_lt hRr
    have heq : D * (R / D ^ (n + 1)) = R / D ^ n := by
      rw [pow_succ]
      field_simp [hD0.ne']
    calc
      _ ≤ β * smallSetMass μ ν (ENNReal.ofReal (D * (R / D ^ (n + 1)))) := hrec _ ht htr
      _ = β * smallSetMass μ ν (ENNReal.ofReal (R / D ^ n)) := by rw [heq]
      _ ≤ β * β ^ n := mul_le_mul' le_rfl ih
      _ = β ^ (n + 1) := by rw [pow_succ]; ac_rfl

end LpSelfSimilar.Analysis
