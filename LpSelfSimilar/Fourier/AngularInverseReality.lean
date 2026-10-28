module

public import LpSelfSimilar.Fourier.AngularTransformReflection
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-!
# Reality of angular inverse kernels

Conjugation reverses the angular phase, and Lebesgue reflection transfers that
reversal to the amplitude. Thus a conjugate-reflection symmetric amplitude has
an actually real inverse integral. No convergence assumption is hidden here:
these identities hold for the total Bochner integral itself.
-/

open MeasureTheory
open scoped ComplexConjugate

namespace LpSelfSimilar.Fourier

/-- Complex conjugation reverses the angular phase. -/
theorem conj_angularFourierPhase (x ξ : ℝ) :
    conj (angularFourierPhase x ξ) = angularFourierPhase (-x) ξ := by
  unfold angularFourierPhase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_mul, Complex.ofReal_neg]
  ring

/-- Conjugating the inverse integral conjugates its amplitude and reflects the spatial coordinate. -/
theorem conj_angularInverseFourier (f : ℝ → ℂ) (x : ℝ) :
    conj (angularInverseFourier f x) = angularInverseFourier (fun ξ => conj (f ξ)) (-x) := by
  unfold angularInverseFourier
  rw [RCLike.conj_smul, ← integral_conj]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun ξ => by
    change conj (angularFourierPhase x ξ * f ξ) = angularFourierPhase (-x) ξ * conj (f ξ)
    rw [map_mul, conj_angularFourierPhase])

/-- Conjugate reflection of the amplitude exactly conjugates the inverse kernel. -/
theorem angularInverseFourier_conj_reflect (f : ℝ → ℂ) (x : ℝ) :
    angularInverseFourier (fun ξ => conj (f (-ξ))) x = conj (angularInverseFourier f x) := by
  rw [conj_angularInverseFourier]
  exact angularInverseFourier_reflect (fun ξ => conj (f ξ)) x

/-- A conjugate-reflection symmetric amplitude has an inverse equal to its real part. -/
theorem ofReal_re_angularInverseFourier_of_conj_reflect (f : ℝ → ℂ)
    (hf : ∀ ξ, conj (f (-ξ)) = f ξ) (x : ℝ) :
    ((angularInverseFourier f x).re : ℂ) = angularInverseFourier f x := by
  apply Complex.conj_eq_iff_re.mp
  rw [← angularInverseFourier_conj_reflect]
  congr 1
  funext ξ
  exact hf ξ

/-- In particular, every even real amplitude has a real angular inverse kernel. -/
theorem ofReal_re_angularInverseFourier_of_even (f : ℝ → ℝ)
    (hf : ∀ ξ, f (-ξ) = f ξ) (x : ℝ) :
    ((angularInverseFourier (fun ξ => (f ξ : ℂ)) x).re : ℂ) =
      angularInverseFourier (fun ξ => (f ξ : ℂ)) x := by
  apply ofReal_re_angularInverseFourier_of_conj_reflect
  intro ξ
  simp only [Complex.conj_ofReal, hf ξ]

end LpSelfSimilar.Fourier
