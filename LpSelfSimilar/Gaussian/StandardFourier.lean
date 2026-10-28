module

public import LpSelfSimilar.Gaussian.Kernel
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import LpSelfSimilar.Fourier.AngularFourierInversion
public import LpSelfSimilar.Fourier.AngularMeasureConvolution

@[expose] public section

/-!
# The exact standard Gaussian Fourier pair in angular frequency

The amplitude exp(-u^2/2) is the characteristic function of the standard
Gaussian probability measure. Its actual inverse is the previously defined
variance-one Gaussian density, with the normalization 1/sqrt(2*pi). All
integrability and inversion inputs are supplied explicitly.
-/

open MeasureTheory ProbabilityTheory
open LpSelfSimilar.Fourier
open scoped ContDiff NNReal

namespace LpSelfSimilar.Gaussian

/-- The standard Gaussian Fourier amplitude, as an actual complex-valued function. -/
noncomputable def standardGaussianAmplitude (u : ℝ) : ℂ :=
  (Real.exp (-(u ^ 2) / 2) : ℂ)

/-- Exact relation of the amplitude to the variance-one spatial Gaussian kernel. -/
theorem standardGaussianAmplitude_eq_mul_kernel (u : ℝ) :
    standardGaussianAmplitude u = (Real.sqrt (2 * Real.pi) : ℂ) * (kernel 1 u : ℂ) := by
  have hs : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  unfold standardGaussianAmplitude kernel
  simp only [mul_one, Complex.ofReal_mul, Complex.ofReal_inv]
  rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hs), one_mul]

/-- The standard Gaussian amplitude is integrable. -/
theorem integrable_standardGaussianAmplitude : Integrable standardGaussianAmplitude := by
  have he : standardGaussianAmplitude =
      (fun u => (Real.sqrt (2 * Real.pi) : ℂ) * (kernel 1 u : ℂ)) :=
    funext standardGaussianAmplitude_eq_mul_kernel
  rw [he]
  exact ((integrable_kernel (by norm_num : (0 : ℝ) ≤ 1)).ofReal).const_mul _

/-- The standard Gaussian amplitude is smooth of every finite order. -/
theorem contDiff_standardGaussianAmplitude : ContDiff ℝ ∞ standardGaussianAmplitude := by
  have hreal : ContDiff ℝ ∞ (fun u : ℝ => Real.exp (-(u ^ 2) / 2)) :=
    Real.contDiff_exp.comp (by fun_prop)
  exact Complex.ofRealCLM.contDiff.comp hreal

/-- The actual forward angular transform of the variance-one density is exp(-u^2/2). -/
theorem angularFourier_kernel_one (u : ℝ) :
    angularFourier (fun x => (kernel 1 x : ℂ)) u = standardGaussianAmplitude u := by
  have hk (x : ℝ) : kernel 1 x = gaussianPDFReal 0 1 x := by
    simpa using kernel_eq_gaussianPDFReal (by norm_num : (0 : ℝ) ≤ 1) x
  have he : angularFourier (fun x => (kernel 1 x : ℂ)) u =
      charFun (gaussianReal 0 1) (-u) := by
    rw [charFun_neg_eq_integral_angularFourierPhase,
      integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
    unfold angularFourier
    apply integral_congr_ae
    apply ae_of_all
    intro x
    dsimp only
    rw [hk, Complex.real_smul]
    have hp : angularFourierPhase (-u) x = angularFourierPhase (-x) u := by
      unfold angularFourierPhase
      congr 2
      ring
    rw [hp, mul_comm]
  rw [he, charFun_gaussianReal]
  unfold standardGaussianAmplitude
  convert! (Complex.ofReal_exp (-(u ^ 2) / 2)).symm using 1 <;>
    congr 1 <;> push_cast <;> ring

/-- The actual inverse amplitude is the standard Gaussian density, with its exact normalization. -/
theorem angularInverseFourier_standardGaussianAmplitude (x : ℝ) :
    angularInverseFourier standardGaussianAmplitude x = (kernel 1 x : ℂ) := by
  have he : angularFourier (fun y => (kernel 1 y : ℂ)) = standardGaussianAmplitude :=
    funext angularFourier_kernel_one
  rw [← he]
  apply angularInverseFourier_angularFourier
  · exact Complex.continuous_ofReal.comp (continuous_kernel 1)
  · exact (integrable_kernel (by norm_num : (0 : ℝ) ≤ 1)).ofReal
  · rw [he]
    exact integrable_standardGaussianAmplitude

/-- The actual inverse Gaussian amplitude is integrable. -/
theorem integrable_inverse_standardGaussianAmplitude :
    Integrable (angularInverseFourier standardGaussianAmplitude) := by
  have he := funext angularInverseFourier_standardGaussianAmplitude
  rw [he]
  exact (integrable_kernel (by norm_num : (0 : ℝ) ≤ 1)).ofReal

end LpSelfSimilar.Gaussian
