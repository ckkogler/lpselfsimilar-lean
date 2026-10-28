module

public import LpSelfSimilar.Fourier.QuinticKernelDerivatives
public import LpSelfSimilar.Analysis.RescaledKernelDerivative

@[expose] public section

/-!
# The exact scale derivative of the actual quintic smoothing kernel

Combining the proved spatial identity with the general scale chain rule yields
d/dr phi_r(x) = -psi_r(x)/r at every nonzero scale. All kernels in this identity
are the actual real angular inverse integrals.
-/

namespace LpSelfSimilar.Fourier

/-- Differentiating the actual smoothing kernel in its scale gives exactly minus detail over scale. -/
theorem hasDerivAt_rescaled_quinticSmoothingKernel {ε : ℝ} (hε : 0 < ε)
    {r : ℝ} (hr : r ≠ 0) (x : ℝ) :
    HasDerivAt (fun s => Analysis.rescaledKernel s (quinticSmoothingKernel ε) x)
      (-Analysis.rescaledKernel r (quinticDetailKernel ε) x / r) r := by
  exact Analysis.hasDerivAt_rescaledKernel_scale_of_detail
    (fun y => (hasDerivAt_quinticSmoothingKernel hε y).differentiableAt)
    (quinticDetailKernel_eq_add_mul_deriv hε) hr x

end LpSelfSimilar.Fourier
