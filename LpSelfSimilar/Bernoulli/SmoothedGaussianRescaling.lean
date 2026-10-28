module

public import LpSelfSimilar.Bernoulli.SmoothedGaussianPlancherel
public import LpSelfSimilar.Gaussian.KernelRescaling

@[expose] public section

/-!
# Returning the Gaussian error to the original variance scale

Both the actual Bernoulli smoothing and the comparison Gaussian transform by
the same positive spatial scale. The inverse Jacobian cancels in the L1
integral, so the normalized error is exactly the error at variance
(1 - theta^2) inverse. No probabilistic variance hypothesis is needed.
-/

open MeasureTheory
open LpSelfSimilar.Analysis LpSelfSimilar.Fourier LpSelfSimilar.Gaussian

namespace LpSelfSimilar.Bernoulli

/-- The actual Gaussian approximation error is unchanged by variance normalization. -/
theorem integral_abs_smoothedGaussianError_eq_original {θ ε : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hε : 0 < ε) :
    (∫ x : ℝ, |varianceNormalizedSmoothing θ ε x - kernel 1 x|) =
      ∫ x : ℝ, |measureFunctionConvolution (convolution θ)
        (rescaledKernel (-Real.log θ) (quinticSmoothingKernel ε)) x -
          kernel ((1 - θ ^ 2)⁻¹) x| := by
  have hτ : 0 < 1 - θ ^ 2 := variance_scale_pos hθ0.le hθ1
  have ha : 0 < Real.sqrt (1 - θ ^ 2) := Real.sqrt_pos.mpr hτ
  have hg : rescaledKernel (Real.sqrt (1 - θ ^ 2))
      (kernel ((1 - θ ^ 2)⁻¹)) = kernel 1 := by
    simpa only [Real.sq_sqrt hτ.le] using rescaledKernel_kernel_inverse_square ha
  have he : (fun x => varianceNormalizedSmoothing θ ε x - kernel 1 x) =
      rescaledKernel (Real.sqrt (1 - θ ^ 2))
        (fun x => measureFunctionConvolution (convolution θ)
          (rescaledKernel (-Real.log θ) (quinticSmoothingKernel ε)) x -
            kernel ((1 - θ ^ 2)⁻¹) x) := by
    rw [varianceNormalizedSmoothing_eq_rescaled hθ0 hθ1 hε, ← hg]
    funext x
    simp only [rescaledKernel, smul_sub]
  have hi := integral_norm_rescaledKernel
    (fun x => measureFunctionConvolution (convolution θ)
      (rescaledKernel (-Real.log θ) (quinticSmoothingKernel ε)) x -
        kernel ((1 - θ ^ 2)⁻¹) x) ha
  rw [← he] at hi
  simpa only [Real.norm_eq_abs] using hi

end LpSelfSimilar.Bernoulli
