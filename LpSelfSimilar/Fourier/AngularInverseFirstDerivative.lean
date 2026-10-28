module

public import LpSelfSimilar.Fourier.SupportedIntervalTransform
public import LpSelfSimilar.Fourier.AngularInverseTransform

@[expose] public section

/-!
# Inverse transforms of compactly supported first derivatives

One integration by parts removes the boundary term when the amplitude vanishes
at the endpoints. Multiplication by constants commutes with the actual inverse
integral, including its real normalization coefficient.
-/

open MeasureTheory Set

namespace LpSelfSimilar.Fourier

/-- Constant complex factors commute with the actual angular inverse integral. -/
theorem angularInverseFourier_const_mul (c : ℂ) (f : ℝ → ℂ) (x : ℝ) :
    angularInverseFourier (fun ξ => c * f ξ) x = c * angularInverseFourier f x := by
  unfold angularInverseFourier
  simp_rw [mul_left_comm (angularFourierPhase x _) c]
  rw [integral_const_mul]
  simp only [Complex.real_smul]
  ring

/-- The inverse transform of a compactly supported derivative has exact multiplier -i*x. -/
theorem angularInverseFourier_firstDerivative_of_interval {a b : ℝ} (hab : a ≤ b)
    {g g' : ℝ → ℂ} (hg : ContinuousOn g (Icc a b))
    (hd : ∀ ξ ∈ Ioo a b, HasDerivAt g (g' ξ) ξ)
    (hi : IntervalIntegrable g' volume a b)
    (hz : ∀ ξ, ξ ≤ a ∨ b ≤ ξ → g ξ = 0)
    (hz' : ∀ ξ, ξ ≤ a ∨ b ≤ ξ → g' ξ = 0) (x : ℝ) :
    angularInverseFourier g' x = -((x : ℂ) * Complex.I) * angularInverseFourier g x := by
  unfold angularInverseFourier
  rw [integral_angularFourierPhase_eq_interval hz', integral_angularFourierPhase_eq_interval hz,
    integral_angularFourierPhase_mul_derivative hab hg hd hi
      (hz a (Or.inl le_rfl)) (hz b (Or.inr le_rfl))]
  simp only [Complex.real_smul]
  ring

end LpSelfSimilar.Fourier
