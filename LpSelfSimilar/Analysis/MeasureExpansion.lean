module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Tactic

@[expose] public section

/-! Iteration of an abstract measure-expansion inequality; independent of Euclidean geometry. -/

open MeasureTheory Metric Set
open scoped ENNReal

namespace LpSelfSimilar

/-- Iterating a proved expansion step gives geometric decay of the mass of
sets whose volume is geometrically small. -/
lemma measure_le_pow_mul_of_expansion {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) {A β T : ℝ≥0∞} (hA : 1 ≤ A)
    (hstep : ∀ E, MeasurableSet E → A * μ E ≤ T →
      ∃ Ω, MeasurableSet Ω ∧ μ Ω ≤ A * μ E ∧ ν E ≤ β * ν Ω)
    (n : ℕ) {E : Set X} (hE : MeasurableSet E) (hvol : A ^ n * μ E ≤ T) :
    ν E ≤ β ^ n * ν univ := by
  induction n generalizing E with
  | zero => simpa using measure_mono (subset_univ E)
  | succ n ih =>
    have hstepvol : A * μ E ≤ T := by
      calc
        A * μ E = 1 * (A * μ E) := by rw [one_mul]
        _ ≤ A ^ n * (A * μ E) := by gcongr; exact one_le_pow₀ hA
        _ = A ^ (n + 1) * μ E := by rw [pow_succ, mul_assoc]
        _ ≤ T := hvol
    obtain ⟨Ω, hΩ, hv, hm⟩ := hstep E hE hstepvol
    have hΩvol : A ^ n * μ Ω ≤ T := by
      calc
        A ^ n * μ Ω ≤ A ^ n * (A * μ E) := by gcongr
        _ = A ^ (n + 1) * μ E := by rw [pow_succ, mul_assoc]
        _ ≤ T := hvol
    calc
      ν E ≤ β * ν Ω := hm
      _ ≤ β * (β ^ n * ν univ) := by gcongr; exact ih hΩ hΩvol
      _ = β ^ (n + 1) * ν univ := by rw [pow_succ]; ac_rfl

end LpSelfSimilar
