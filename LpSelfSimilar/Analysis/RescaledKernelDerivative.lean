module

public import LpSelfSimilar.Analysis.AffineKernelConvolution
public import Mathlib.Analysis.Calculus.Deriv.Inv

@[expose] public section

/-!
# Differentiation in the scale of a rescaled real kernel

The inverse-scale normalization and the spatial change of variables both
contribute to the derivative. Their sum is exactly minus the rescaled detail
kernel divided by the scale when psi(x) = phi(x) + x*phi'(x).
-/

namespace LpSelfSimilar.Analysis

/-- The chain and product rules for the actual inverse-scale normalized kernel. -/
theorem hasDerivAt_rescaledKernel_scale {f : ℝ → ℝ} {r x f' : ℝ} (hr : r ≠ 0)
    (hf : HasDerivAt f f' (x / r)) :
    HasDerivAt (fun s => rescaledKernel s f x)
      (-(f (x / r) + (x / r) * f') / r ^ 2) r := by
  have hu := (hasDerivAt_const r x).div (hasDerivAt_id r) hr
  have hv := (hasDerivAt_id r).inv hr
  change HasDerivAt (fun s => s⁻¹ * f (x / s)) _ r
  convert! hv.mul (hf.comp r hu) using 1 <;>
    simp only [Pi.inv_apply, Function.comp_apply, id_eq, mul_one, zero_mul, zero_sub] <;> field_simp <;> ring

/-- A proved spatial detail identity gives the exact scale derivative -psi_r/r. -/
theorem hasDerivAt_rescaledKernel_scale_of_detail {f ψ : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hψ : ∀ y, ψ y = f y + y * deriv f y)
    {r : ℝ} (hr : r ≠ 0) (x : ℝ) :
    HasDerivAt (fun s => rescaledKernel s f x) (-rescaledKernel r ψ x / r) r := by
  convert! hasDerivAt_rescaledKernel_scale hr (hf (x / r)).hasDerivAt using 1
  rw [rescaledKernel, hψ]
  simp only [smul_eq_mul]
  field_simp

end LpSelfSimilar.Analysis
