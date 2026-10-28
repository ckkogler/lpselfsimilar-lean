module

public import LpSelfSimilar.Fourier.AngularInverseTransform
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

/-!
# Differentiation of the actual angular inverse integral

An integrable first frequency moment dominates the spatial derivative uniformly
in the spatial parameter. Differentiation under the integral therefore applies
to the actual phase integral, with the precise multiplier i*xi and coefficient
1/(2*pi). No differentiability of the amplitude is required.
-/

open MeasureTheory Set

namespace LpSelfSimilar.Fourier

/-- The spatial derivative of the angular phase has multiplier i*xi. -/
theorem hasDerivAt_angularFourierPhase_space (x ξ : ℝ) :
    HasDerivAt (fun y => angularFourierPhase y ξ)
      ((ξ : ℂ) * Complex.I * angularFourierPhase x ξ) x := by
  have he : (fun y => angularFourierPhase y ξ) = angularFourierPhase ξ := by
    funext y
    simp only [angularFourierPhase, mul_comm y ξ]
  have hp : angularFourierPhase x ξ = angularFourierPhase ξ x := by
    simp only [angularFourierPhase, mul_comm x ξ]
  rw [he, hp]
  exact hasDerivAt_angularFourierPhase ξ x

/-- An integrable frequency moment justifies differentiation under the phase integral. -/
theorem hasDerivAt_integral_angularFourierPhase_mul {f : ℝ → ℂ}
    (hf : Integrable f) (hm : Integrable (fun ξ : ℝ => (ξ : ℂ) * f ξ)) (x : ℝ) :
    HasDerivAt (fun y => ∫ ξ, angularFourierPhase y ξ * f ξ)
      (∫ ξ, angularFourierPhase x ξ * (Complex.I * ((ξ : ℂ) * f ξ))) x := by
  have hi := hm.const_mul Complex.I
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun y ξ => angularFourierPhase y ξ * f ξ)
    (F' := fun y ξ => angularFourierPhase y ξ * (Complex.I * ((ξ : ℂ) * f ξ)))
    (bound := fun ξ : ℝ => ‖(ξ : ℂ) * f ξ‖) (s := Set.univ) (by simp)
    (Filter.Eventually.of_forall (fun y =>
      (integrable_angularFourierPhase_mul hf y).aestronglyMeasurable))
    (integrable_angularFourierPhase_mul hf x)
    (integrable_angularFourierPhase_mul hi x).aestronglyMeasurable
    (ae_of_all _ (fun ξ y _ => by
      simp only [norm_mul, norm_angularFourierPhase, Complex.norm_I, one_mul, le_refl]))
    hm.norm
    (ae_of_all _ (fun ξ y _ => by
      convert! (hasDerivAt_angularFourierPhase_space y ξ).mul_const (f ξ) using 1 <;> ring))).2

/-- Differentiation of the inverse integral retains its exact angular normalization. -/
theorem hasDerivAt_angularInverseFourier {f : ℝ → ℂ}
    (hf : Integrable f) (hm : Integrable (fun ξ : ℝ => (ξ : ℂ) * f ξ)) (x : ℝ) :
    HasDerivAt (angularInverseFourier f)
      (angularInverseFourier (fun ξ => Complex.I * ((ξ : ℂ) * f ξ)) x) x := by
  exact (hasDerivAt_integral_angularFourierPhase_mul hf hm x).const_smul (2 * Real.pi)⁻¹

end LpSelfSimilar.Fourier
