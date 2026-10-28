module

public import LpSelfSimilar.Gaussian.StandardFourier
public import LpSelfSimilar.Gaussian.PolynomialKernel
public import LpSelfSimilar.Fourier.IntegrableDerivativeTransform

@[expose] public section

/-!
# Derivative and inverse-derivative data for the standard Gaussian

Polynomial Gaussian moments give the L1 inputs. The actual amplitude derivative
is -u*exp(-u^2/2). The general integrable-derivative Fourier theorem identifies
its inverse as -i*x times the variance-one density, with no boundary assumption.
-/

open MeasureTheory
open LpSelfSimilar.Fourier

namespace LpSelfSimilar.Gaussian

/-- The first spatial moment of the standard Gaussian density is integrable. -/
theorem integrable_mul_kernel_one :
    Integrable (fun x : ℝ => (x : ℂ) * (kernel 1 x : ℂ)) := by
  have h : Integrable (fun x : ℝ => ((Polynomial.X.eval x * kernel 1 x : ℝ) : ℂ)) :=
    (integrable_polynomial_mul_kernel Polynomial.X (by norm_num : (0 : ℝ) < 1)).ofReal
  simpa only [Polynomial.eval_X, Complex.ofReal_mul] using! h

/-- The frequency-weighted standard Gaussian amplitude is integrable. -/
theorem integrable_mul_standardGaussianAmplitude :
    Integrable (fun u : ℝ => (u : ℂ) * standardGaussianAmplitude u) := by
  have h := integrable_mul_kernel_one.const_mul (Real.sqrt (2 * Real.pi) : ℂ)
  convert! h using 1
  funext u
  rw [standardGaussianAmplitude_eq_mul_kernel]
  ring

/-- The displayed Gaussian derivative is its actual derivative. -/
theorem hasDerivAt_standardGaussianAmplitude (u : ℝ) :
    HasDerivAt standardGaussianAmplitude (-(u : ℂ) * standardGaussianAmplitude u) u := by
  convert! ((((hasDerivAt_id u).pow 2).neg.div_const 2).exp).ofReal_comp using 1 <;>
    simp only [standardGaussianAmplitude, Pi.pow_apply, Pi.neg_apply, id_eq, pow_one, mul_one,
      Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat] <;> norm_num <;> ring

/-- The actual Gaussian frequency derivative is integrable. -/
theorem integrable_deriv_standardGaussianAmplitude : Integrable (deriv standardGaussianAmplitude) := by
  have he : deriv standardGaussianAmplitude = (fun u : ℝ => -((u : ℂ) * standardGaussianAmplitude u)) := by
    funext u
    rw [(hasDerivAt_standardGaussianAmplitude u).deriv, neg_mul]
  rw [he]
  exact integrable_mul_standardGaussianAmplitude.neg

/-- The inverse of the actual Gaussian derivative is exactly -i*x times the standard density. -/
theorem inverse_deriv_standardGaussianAmplitude (x : ℝ) :
    angularInverseFourier (deriv standardGaussianAmplitude) x =
      -Complex.I * (x : ℂ) * (kernel 1 x : ℂ) := by
  rw [angularInverseFourier_deriv_of_integrable integrable_standardGaussianAmplitude
    (fun u => (hasDerivAt_standardGaussianAmplitude u).differentiableAt)
    integrable_deriv_standardGaussianAmplitude,
    angularInverseFourier_standardGaussianAmplitude]

/-- The inverse of the actual Gaussian frequency derivative is integrable. -/
theorem integrable_inverse_deriv_standardGaussianAmplitude :
    Integrable (angularInverseFourier (deriv standardGaussianAmplitude)) := by
  have he : angularInverseFourier (deriv standardGaussianAmplitude) =
      (fun x : ℝ => -Complex.I * ((x : ℂ) * (kernel 1 x : ℂ))) := by
    funext x
    rw [inverse_deriv_standardGaussianAmplitude]
    ring
  rw [he]
  exact integrable_mul_kernel_one.const_mul (-Complex.I)

end LpSelfSimilar.Gaussian
