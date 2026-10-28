module

public import LpSelfSimilar.Gaussian.PolynomialKernel
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

/-!
# Gaussian integration by parts for bounded differentiable functions

Polynomial Gaussian integrability and boundedness of a function and its
continuous derivative justify the whole-line integration-by-parts theorem.
Its vanishing boundary terms follow from integrability in Mathlib's theorem;
no informal tail cancellation is assumed. The final identity uses the actual
standard Gaussian probability law.
-/

open MeasureTheory Real

namespace LpSelfSimilar.Gaussian

/-- A standard Gaussian expectation is the integral against the established kernel. -/
theorem integral_standard_gaussian_eq_kernel (f : ℝ → ℝ) :
    (∫ x, f x ∂ProbabilityTheory.gaussianReal 0 1) = ∫ x, kernel 1 x * f x := by
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)]
  simp only [ProbabilityTheory.gaussianPDFReal, kernel, NNReal.coe_one, sub_zero, mul_one, smul_eq_mul]

/-- Integration by parts with the explicit standard Gaussian density. -/
theorem kernel_integration_by_parts_of_bounded {f f' : ℝ → ℝ} {C D : ℝ}
    (hd : ∀ x, HasDerivAt f (f' x) x) (hfd : Continuous f')
    (hC : ∀ x, |f x| ≤ C) (hD : ∀ x, |f' x| ≤ D) :
    (∫ x : ℝ, x * f x * kernel 1 x) = ∫ x : ℝ, f' x * kernel 1 x := by
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hfn : ∀ᵐ x : ℝ ∂volume, ‖f x‖ ≤ C := by simpa only [Real.norm_eq_abs] using ae_of_all volume hC
  have hfn' : ∀ᵐ x : ℝ ∂volume, ‖f' x‖ ≤ D := by simpa only [Real.norm_eq_abs] using ae_of_all volume hD
  have hk := integrable_kernel (y := 1) (by norm_num)
  have hx : Integrable (fun x : ℝ => x * kernel 1 x) volume := by
    simpa only [Polynomial.eval_X] using
      integrable_polynomial_mul_kernel (Polynomial.X : Polynomial ℝ) (y := 1) (by norm_num)
  have hneg : Integrable (fun x : ℝ => -x * kernel 1 x) volume := by
    exact hx.neg.congr (ae_of_all _ (fun x => by dsimp; ring))
  have hu := hneg.bdd_mul hf.aestronglyMeasurable hfn
  have hv := hk.bdd_mul hfd.aestronglyMeasurable hfn'
  have huv := hk.bdd_mul hf.aestronglyMeasurable hfn
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := f) (u' := f') (v := kernel 1) (v' := fun x => -x * kernel 1 x)
    (fun x _ => hd x)
    (fun x _ => by simpa only [div_one] using hasDerivAt_kernel_space (y := 1) (by norm_num) x)
    hu hv huv
  calc
    _ = -(∫ x : ℝ, f x * (-x * kernel 1 x)) := by
      rw [← integral_neg]
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by ring)
    _ = _ := by rw [h]; ring

/-- Stein's identity for the genuine standard Gaussian, with proved boundary control. -/
theorem standard_gaussian_integration_by_parts_of_bounded {f f' : ℝ → ℝ} {C D : ℝ}
    (hd : ∀ x, HasDerivAt f (f' x) x) (hfd : Continuous f')
    (hC : ∀ x, |f x| ≤ C) (hD : ∀ x, |f' x| ≤ D) :
    (∫ x : ℝ, x * f x ∂ProbabilityTheory.gaussianReal 0 1) =
      ∫ x : ℝ, f' x ∂ProbabilityTheory.gaussianReal 0 1 := by
  rw [integral_standard_gaussian_eq_kernel, integral_standard_gaussian_eq_kernel]
  convert kernel_integration_by_parts_of_bounded hd hfd hC hD using 1 <;>
    congr 1 <;> funext x <;> ring

end LpSelfSimilar.Gaussian
