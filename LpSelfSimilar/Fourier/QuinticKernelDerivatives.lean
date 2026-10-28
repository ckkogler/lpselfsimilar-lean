module

public import LpSelfSimilar.Fourier.QuinticSpatialKernels
public import LpSelfSimilar.Fourier.QuinticCutoffMoments
public import LpSelfSimilar.Fourier.AngularInverseDerivative
public import LpSelfSimilar.Fourier.AngularInverseFirstDerivative

@[expose] public section

/-!
# The spatial derivative and exact detail identity for the quintic kernel

Compact frequency support provides the first moment needed to differentiate the
inverse integral. Integration by parts applied to xi times the cutoff proves
psi = phi + x*phi'. The proof uses the actual derivative of the real smoothing
kernel and accounts for all endpoint terms; no smoothness of the second
derivative of the detail multiplier is required.
-/

open MeasureTheory Set

namespace LpSelfSimilar.Fourier

/-- The actual real smoothing kernel has the derivative given by the first Fourier moment. -/
theorem hasDerivAt_quinticSmoothingKernel {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    HasDerivAt (quinticSmoothingKernel ε)
      (angularInverseFourier (fun ξ : ℝ =>
        Complex.I * ((ξ : ℂ) * (quinticFourierCutoff ε ξ : ℂ))) x).re x := by
  have hm := (integrable_continuous_mul_quinticFourierCutoff_and_slope hε
    Complex.continuous_ofReal).1
  have hd := hasDerivAt_angularInverseFourier
    (integrable_quinticFourierCutoff_and_curvature hε).1 hm x
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hd

/-- Frequency integration by parts gives the exact complex detail identity. -/
theorem angularInverseFourier_quinticDetail_identity {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    angularInverseFourier (fun ξ => (quinticFourierDetail ε ξ : ℂ)) x =
      angularInverseFourier (fun ξ => (quinticFourierCutoff ε ξ : ℂ)) x +
        (x : ℂ) * angularInverseFourier (fun ξ : ℝ =>
          Complex.I * ((ξ : ℂ) * (quinticFourierCutoff ε ξ : ℂ))) x := by
  let c : ℝ → ℂ := fun ξ => (quinticFourierCutoff ε ξ : ℂ)
  let s : ℝ → ℂ := fun ξ => (quinticFourierCutoffSlope ε ξ : ℂ)
  have hc : Continuous c := Complex.continuous_ofReal.comp
    (continuous_iff_continuousAt.mpr (fun ξ =>
      (hasDerivAt_quinticFourierCutoff ε ξ).continuousAt))
  have hs : Continuous s := Complex.continuous_ofReal.comp
    (continuous_quinticFourierCutoffSlope hε.ne')
  have hzero (ξ : ℝ) (hξ : ξ ≤ -(1 + ε) ∨ 1 + ε ≤ ξ) : c ξ = 0 ∧ s ξ = 0 := by
    have ha : 1 + ε ≤ |ξ| := by
      rcases hξ with hξ | hξ
      · exact le_abs.mpr (Or.inr (by linarith))
      · exact le_abs.mpr (Or.inl hξ)
    simp only [c, s, quinticFourierCutoff_eq_zero hε ha,
      (quinticFourierCutoff_derivatives_zero_off hε ha).1, Complex.ofReal_zero, and_self]
  have hG : angularInverseFourier (fun ξ : ℝ => c ξ + (ξ : ℂ) * s ξ) x =
      -((x : ℂ) * Complex.I) * angularInverseFourier (fun ξ : ℝ => (ξ : ℂ) * c ξ) x := by
    apply angularInverseFourier_firstDerivative_of_interval (a := -(1 + ε)) (b := 1 + ε)
      (by linarith) (Complex.continuous_ofReal.mul hc).continuousOn
    · intro ξ _
      convert! (hasDerivAt_id ξ).ofReal_comp.mul
        (hasDerivAt_quinticFourierCutoff ε ξ).ofReal_comp using 1 <;>
        simp only [c, s, Complex.ofReal_one, one_mul, id_eq]
    · exact (hc.add (Complex.continuous_ofReal.mul hs)).intervalIntegrable _ _
    · intro ξ hξ
      change (ξ : ℂ) * c ξ = 0
      rw [(hzero ξ hξ).1, mul_zero]
    · intro ξ hξ
      rw [(hzero ξ hξ).1, (hzero ξ hξ).2, mul_zero, add_zero]
  have hi : Integrable c := (integrable_quinticFourierCutoff_and_curvature hε).1
  have hm : Integrable (fun ξ : ℝ => (ξ : ℂ) * s ξ) :=
    (integrable_continuous_mul_quinticFourierCutoff_and_slope hε Complex.continuous_ofReal).2
  have he : (fun ξ => (quinticFourierDetail ε ξ : ℂ)) =
      (fun ξ : ℝ => c ξ - (c ξ + (ξ : ℂ) * s ξ)) := by
    funext ξ
    simp only [quinticFourierDetail, (hasDerivAt_quinticFourierCutoff ε ξ).deriv,
      c, s, Complex.ofReal_mul, Complex.ofReal_neg]
    ring
  have hiSum : Integrable (fun ξ : ℝ => c ξ + (ξ : ℂ) * s ξ) := hi.add hm
  rw [he, angularInverseFourier_sub hi hiSum, hG, angularInverseFourier_const_mul]
  ring

/-- The actual real detail kernel is phi + x times the actual spatial derivative of phi. -/
theorem quinticDetailKernel_eq_add_mul_deriv {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    quinticDetailKernel ε x = quinticSmoothingKernel ε x +
      x * deriv (quinticSmoothingKernel ε) x := by
  rw [(hasDerivAt_quinticSmoothingKernel hε x).deriv]
  simpa only [quinticDetailKernel, quinticSmoothingKernel, Complex.add_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
    congrArg Complex.re (angularInverseFourier_quinticDetail_identity hε x)

end LpSelfSimilar.Fourier
