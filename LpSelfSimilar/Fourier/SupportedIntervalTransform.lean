module

public import LpSelfSimilar.Fourier.IntervalIntegrationByParts
public import LpSelfSimilar.Fourier.AngularInverseL1
public import LpSelfSimilar.Analysis.CompactIntervalExtension

@[expose] public section

/-!
# Fourier identities for a compact interval amplitude

The amplitude and its first derivative may be merely piecewise smooth globally.
Continuity on the closed active interval, derivative formulas in its interior,
and vanishing endpoint data suffice for the exact whole-line transform identity.
-/

open Set MeasureTheory
open LpSelfSimilar.Analysis

namespace LpSelfSimilar.Fourier

/-- A zero-extended amplitude has exactly its interval oscillatory integral. -/
theorem integral_angularFourierPhase_eq_interval {f : ℝ → ℂ} {a b : ℝ}
    (hz : ∀ ξ, ξ ≤ a ∨ b ≤ ξ → f ξ = 0) (x : ℝ) :
    (∫ ξ, angularFourierPhase x ξ * f ξ) = ∫ ξ in a..b, angularFourierPhase x ξ * f ξ := by
  apply integral_eq_interval_of_zero_off_Ioo
  intro ξ hξ
  rw [hz ξ hξ, mul_zero]

/-- The whole-line second-derivative identity follows from the actual interval derivative data. -/
theorem angularFourier_secondDerivative_identity_of_interval {a b : ℝ} (hab : a ≤ b)
    {g g' g'' : ℝ → ℂ} (hg : ContinuousOn g (Icc a b)) (hg' : ContinuousOn g' (Icc a b))
    (hd : ∀ ξ ∈ Ioo a b, HasDerivAt g (g' ξ) ξ)
    (hd' : ∀ ξ ∈ Ioo a b, HasDerivAt g' (g'' ξ) ξ)
    (hi : IntervalIntegrable g'' volume a b)
    (hz : ∀ ξ, ξ ≤ a ∨ b ≤ ξ → g ξ = 0)
    (hz'' : ∀ ξ, ξ ≤ a ∨ b ≤ ξ → g'' ξ = 0)
    (ha' : g' a = 0) (hb' : g' b = 0) (x : ℝ) :
    (∫ ξ, angularFourierPhase x ξ * g'' ξ) =
      -(x : ℂ) ^ 2 * ∫ ξ, angularFourierPhase x ξ * g ξ := by
  rw [integral_angularFourierPhase_eq_interval hz'', integral_angularFourierPhase_eq_interval hz]
  exact integral_angularFourierPhase_mul_secondDerivative hab hg hg' hd hd' hi
    (hz a (Or.inl le_rfl)) (hz b (Or.inr le_rfl)) ha' hb' x

/-- Exact inverse-transform integrability and L1 bound for an actual interval amplitude. -/
theorem angularInverseFourier_interval_L1_bound {a b : ℝ} (hab : a ≤ b)
    {g g' g'' : ℝ → ℂ} (hg : ContinuousOn g (Icc a b)) (hg' : ContinuousOn g' (Icc a b))
    (hd : ∀ ξ ∈ Ioo a b, HasDerivAt g (g' ξ) ξ)
    (hd' : ∀ ξ ∈ Ioo a b, HasDerivAt g' (g'' ξ) ξ)
    (hi : IntervalIntegrable g'' volume a b)
    (hz : ∀ ξ, ξ ≤ a ∨ b ≤ ξ → g ξ = 0)
    (hz'' : ∀ ξ, ξ ≤ a ∨ b ≤ ξ → g'' ξ = 0)
    (ha' : g' a = 0) (hb' : g' b = 0) :
    Integrable (angularInverseFourier g) ∧
      (∫ x, ‖angularInverseFourier g x‖) ≤ (1 / 2) * ((∫ ξ, ‖g ξ‖) + ∫ ξ, ‖g'' ξ‖) := by
  have hgI := integrable_of_intervalIntegrable_zero_off_Ioo
    (hg.intervalIntegrable_of_Icc hab) hz
  have hg₂I := integrable_of_intervalIntegrable_zero_off_Ioo hi hz''
  have hid := angularFourier_secondDerivative_identity_of_interval hab hg hg' hd hd' hi hz hz'' ha' hb'
  exact ⟨integrable_angularInverseFourier_of_secondDerivative_identity hgI hg₂I hid,
    integral_norm_angularInverseFourier_le_of_secondDerivative_identity hgI hg₂I hid⟩

end LpSelfSimilar.Fourier
