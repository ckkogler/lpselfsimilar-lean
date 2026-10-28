module

public import LpSelfSimilar.Fourier.QuinticSpatialKernels

@[expose] public section

/-!
# Uniform bounds for the actual real quintic kernels

The elementary inverse-transform norm estimate supplies a global bound for
each real kernel. These bounds are used only for finite-measure domination;
the sharper spatial L1 estimates are supplied by the earlier integration by
parts proofs.
-/

namespace LpSelfSimilar.Fourier

/-- The actual real smoothing kernel has a global finite norm bound. -/
theorem exists_bound_quinticSmoothingKernel (ε : ℝ) :
    ∃ C : ℝ, ∀ x, ‖quinticSmoothingKernel ε x‖ ≤ C := by
  refine ⟨(2 * Real.pi)⁻¹ * ∫ ξ : ℝ, ‖(quinticFourierCutoff ε ξ : ℂ)‖, ?_⟩
  intro x
  exact (Complex.abs_re_le_norm _).trans (norm_angularInverseFourier_le _ x)

/-- The actual real detail kernel has a global finite norm bound. -/
theorem exists_bound_quinticDetailKernel (ε : ℝ) :
    ∃ C : ℝ, ∀ x, ‖quinticDetailKernel ε x‖ ≤ C := by
  refine ⟨(2 * Real.pi)⁻¹ * ∫ ξ : ℝ, ‖(quinticFourierDetail ε ξ : ℂ)‖, ?_⟩
  intro x
  exact (Complex.abs_re_le_norm _).trans (norm_angularInverseFourier_le _ x)

end LpSelfSimilar.Fourier
