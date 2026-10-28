module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.Tactic

@[expose] public section

/-!
# First and second moments under an affine transformation

These elementary identities use actual Bochner integrals under a probability
measure. The assumptions are precisely integrability of the first and second
moments. They are useful independently of self-similar measures.
-/

open MeasureTheory

namespace LpSelfSimilar.Probability

/-- An affine function is integrable when the identity is integrable. -/
theorem integrable_affine_of_integrable_id (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hi : Integrable (fun x : ℝ => x) μ) (a b : ℝ) :
    Integrable (fun x : ℝ => a * x + b) μ :=
  (hi.const_mul a).add (integrable_const b)

/-- The first moment of an affine function under a probability measure. -/
theorem integral_affine_of_integrable_id (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hi : Integrable (fun x : ℝ => x) μ) (a b : ℝ) :
    (∫ x : ℝ, a * x + b ∂μ) = a * (∫ x : ℝ, x ∂μ) + b := by
  rw [integral_add (hi.const_mul a) (integrable_const b), integral_const_mul]
  simp

/-- An affine square is integrable when the first two moments are integrable. -/
theorem integrable_sq_affine_of_moments (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hi : Integrable (fun x : ℝ => x) μ) (hi2 : Integrable (fun x : ℝ => x ^ 2) μ)
    (a b : ℝ) : Integrable (fun x : ℝ => (a * x + b) ^ 2) μ := by
  convert! ((hi2.const_mul (a ^ 2)).add (hi.const_mul (2 * a * b))).add
    (integrable_const (b ^ 2)) using 1
  funext x
  simp only [Pi.add_apply]
  ring

/-- The exact affine second-moment identity under a probability measure. -/
theorem integral_sq_affine_of_moments (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hi : Integrable (fun x : ℝ => x) μ) (hi2 : Integrable (fun x : ℝ => x ^ 2) μ)
    (a b : ℝ) :
    (∫ x : ℝ, (a * x + b) ^ 2 ∂μ) =
      a ^ 2 * (∫ x : ℝ, x ^ 2 ∂μ) + 2 * a * b * (∫ x : ℝ, x ∂μ) + b ^ 2 := by
  have he : (fun x : ℝ => (a * x + b) ^ 2) =
      fun x : ℝ => (a ^ 2 * x ^ 2 + (2 * a * b) * x) + b ^ 2 := by
    funext x
    ring
  have hsum : Integrable (fun x : ℝ => a ^ 2 * x ^ 2 + (2 * a * b) * x) μ :=
    (hi2.const_mul _).add (hi.const_mul _)
  rw [he, integral_add hsum (integrable_const _),
    integral_add (hi2.const_mul _) (hi.const_mul _), integral_const_mul, integral_const_mul]
  simp

end LpSelfSimilar.Probability
