module

public import LpSelfSimilar.Fourier.QuinticSpatialKernels
public import LpSelfSimilar.Fourier.AngularFourierInversion
public import LpSelfSimilar.Fourier.QuinticCutoffSupport

@[expose] public section

/-!
# Exact Fourier transforms and masses of the real quintic kernels

Fourier inversion applies to the actual compact frequency multipliers using
their already proved inverse integrability. The real smoothing kernel therefore
has mass one, while the detail kernel has mass zero. No positivity or density
hypothesis is used for these kernel identities.
-/

open MeasureTheory

namespace LpSelfSimilar.Fourier

/-- The real smoothing kernel has exactly the prescribed cutoff as its Fourier transform. -/
theorem angularFourier_quinticSmoothingKernel {ε : ℝ} (hε : 0 < ε) (ξ : ℝ) :
    angularFourier (fun x => (quinticSmoothingKernel ε x : ℂ)) ξ =
      (quinticFourierCutoff ε ξ : ℂ) := by
  have he : (fun x => (quinticSmoothingKernel ε x : ℂ)) =
      angularInverseFourier (fun ξ => (quinticFourierCutoff ε ξ : ℂ)) :=
    funext (ofReal_quinticSmoothingKernel ε)
  rw [he]
  apply angularFourier_angularInverseFourier
  · exact Complex.continuous_ofReal.comp (continuous_iff_continuousAt.mpr
      (fun x => (hasDerivAt_quinticFourierCutoff ε x).continuousAt))
  · exact (integrable_quinticFourierCutoff_and_curvature hε).1
  · exact (integrable_continuous_angularInverseFourier_quinticCutoff hε).1

/-- The real detail kernel has exactly the actual derivative multiplier as its Fourier transform. -/
theorem angularFourier_quinticDetailKernel {ε : ℝ} (hε : 0 < ε) (ξ : ℝ) :
    angularFourier (fun x => (quinticDetailKernel ε x : ℂ)) ξ =
      (quinticFourierDetail ε ξ : ℂ) := by
  have he : (fun x => (quinticDetailKernel ε x : ℂ)) =
      angularInverseFourier (fun ξ => (quinticFourierDetail ε ξ : ℂ)) :=
    funext (ofReal_quinticDetailKernel ε)
  rw [he]
  apply angularFourier_angularInverseFourier
  · exact Complex.continuous_ofReal.comp (continuous_iff_continuousAt.mpr
      (fun x => (hasDerivAt_quinticFourierDetail hε.ne' x).continuousAt))
  · exact (integrable_quinticFourierDetail hε).ofReal
  · exact (integrable_continuous_angularInverseFourier_quinticDetail hε).1

/-- The actual real smoothing kernel has mass one throughout the allowed cutoff-width range. -/
theorem integral_quinticSmoothingKernel {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ x, quinticSmoothingKernel ε x) = 1 := by
  apply Complex.ofReal_injective
  calc
    _ = ∫ x, (quinticSmoothingKernel ε x : ℂ) := integral_ofReal.symm
    _ = (1 : ℂ) := by
      rw [← angularFourier_zero, angularFourier_quinticSmoothingKernel hε]
      rw [quinticFourierCutoff_eq_one hε (by simp; linarith)]
      norm_num

/-- The actual real detail kernel has mass zero. -/
theorem integral_quinticDetailKernel {ε : ℝ} (hε : 0 < ε) :
    (∫ x, quinticDetailKernel ε x) = 0 := by
  apply Complex.ofReal_injective
  calc
    _ = ∫ x, (quinticDetailKernel ε x : ℂ) := integral_ofReal.symm
    _ = (0 : ℂ) := by
      rw [← angularFourier_zero, angularFourier_quinticDetailKernel hε]
      simp [quinticFourierDetail]

end LpSelfSimilar.Fourier
