module

public import LpSelfSimilar.Analysis.RescaledKernelIntegrability

@[expose] public section

/-!
# Uniform bounds on positive scale intervals

A globally bounded real kernel remains bounded after rescaling. Staying above
a positive scale a bounds detail divided by scale by C/a^2, uniformly in the
spatial argument. This supplies finite-measure Fubini and domination inputs.
-/

namespace LpSelfSimilar.Analysis

/-- The exact inverse-scale factor controls a bounded real kernel. -/
theorem norm_rescaledKernel_le {f : ℝ → ℝ} {C : ℝ} (hf : ∀ x, ‖f x‖ ≤ C)
    {r : ℝ} (hr : 0 < r) (x : ℝ) : ‖rescaledKernel r f x‖ ≤ C / r := by
  simp only [rescaledKernel, smul_eq_mul, norm_mul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hr)]
  calc
    r⁻¹ * |f (x / r)| ≤ r⁻¹ * C := mul_le_mul_of_nonneg_left (hf (x / r)) (by positivity)
    _ = C / r := by ring

/-- Detail over scale has a single uniform bound on each positive compact scale interval. -/
theorem norm_rescaledKernel_div_scale_le {f : ℝ → ℝ} {C : ℝ} (hf : ∀ x, ‖f x‖ ≤ C)
    {a r : ℝ} (ha : 0 < a) (har : a ≤ r) (x : ℝ) :
    ‖rescaledKernel r f x / r‖ ≤ C / a ^ 2 := by
  have hr : 0 < r := ha.trans_le har
  have hC : 0 ≤ C := (norm_nonneg (f 0)).trans (hf 0)
  rw [norm_div, Real.norm_eq_abs r, abs_of_pos hr]
  calc
    ‖rescaledKernel r f x‖ / r ≤ (C / r) / r :=
      div_le_div_of_nonneg_right (norm_rescaledKernel_le hf hr x) hr.le
    _ = C / r ^ 2 := by ring
    _ ≤ C / a ^ 2 := by gcongr

end LpSelfSimilar.Analysis
