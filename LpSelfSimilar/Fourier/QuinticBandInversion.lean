module

public import LpSelfSimilar.Fourier.QuinticBandProduct

@[expose] public section

/-!
# Inversion estimates for the actual quintic band product

All interval hypotheses in the reusable integration-by-parts theorem are derived
from the explicit cutoff and amplitude derivatives. Only smoothness of the
amplitude is supplied; compact support and the vanishing endpoint terms come
from the proved quintic construction.
-/

open Set MeasureTheory
open LpSelfSimilar.Analysis

namespace LpSelfSimilar.Fourier

/-- The band product is integrable for every continuous amplitude. -/
theorem integrable_quinticBandProduct {ε : ℝ} (hε : 0 < ε) {P : ℝ → ℂ} (hP : Continuous P) :
    Integrable (quinticBandProduct ε P) := by
  apply integrable_of_intervalIntegrable_zero_off_Ioo
    ((continuous_quinticBandProduct hε hP).intervalIntegrable (1 - ε) (1 + ε))
  intro ξ hξ
  exact (quinticBandProduct_zero_off hε hξ P P P).1

/-- The full curvature formula is integrable for continuous amplitude derivative data. -/
theorem integrable_quinticBandProductCurvature {ε : ℝ} (hε : 0 < ε)
    {P P₁ P₂ : ℝ → ℂ} (hP : Continuous P) (hP₁ : Continuous P₁) (hP₂ : Continuous P₂) :
    Integrable (quinticBandProductCurvature ε P P₁ P₂) := by
  apply integrable_of_intervalIntegrable_zero_off_Ioo
    (intervalIntegrable_quinticBandProductCurvature hε hP hP₁ hP₂)
  intro ξ hξ
  exact (quinticBandProduct_zero_off hε hξ P P₁ P₂).2.2

/-- The actual band product satisfies the second-derivative transform identity. -/
theorem angularFourier_quinticBandProduct_secondDerivative {ε : ℝ} (hε : 0 < ε)
    {P P₁ P₂ : ℝ → ℂ} (hP : ∀ ξ, HasDerivAt P (P₁ ξ) ξ)
    (hP₁ : ∀ ξ, HasDerivAt P₁ (P₂ ξ) ξ) (hP₂ : Continuous P₂) (x : ℝ) :
    (∫ ξ, angularFourierPhase x ξ * quinticBandProductCurvature ε P P₁ P₂ ξ) =
      -(x : ℂ) ^ 2 * ∫ ξ, angularFourierPhase x ξ * quinticBandProduct ε P ξ := by
  have hcP : Continuous P := continuous_iff_continuousAt.mpr (fun ξ ↦ (hP ξ).continuousAt)
  have hcP₁ : Continuous P₁ := continuous_iff_continuousAt.mpr (fun ξ ↦ (hP₁ ξ).continuousAt)
  apply angularFourier_secondDerivative_identity_of_interval (a := 1 - ε) (b := 1 + ε)
    (g' := quinticBandProductSlope ε P P₁) (by linarith)
    (continuous_quinticBandProduct hε hcP).continuousOn
    (continuous_quinticBandProductSlope hε hcP hcP₁).continuousOn
    (fun ξ hξ ↦ hasDerivAt_quinticBandProduct hε (hP ξ))
    (fun ξ hξ ↦ hasDerivAt_quinticBandProductSlope_of_mem hε hξ (hP ξ) (hP₁ ξ))
    (intervalIntegrable_quinticBandProductCurvature hε hcP hcP₁ hP₂)
    (fun ξ hξ ↦ (quinticBandProduct_zero_off hε hξ P P₁ P₂).1)
    (fun ξ hξ ↦ (quinticBandProduct_zero_off hε hξ P P₁ P₂).2.2)
    (quinticBandProduct_zero_off hε (Or.inl le_rfl) P P₁ P₂).2.1
    (quinticBandProduct_zero_off hε (Or.inr le_rfl) P P₁ P₂).2.1 x

/-- The inverse of the actual band product is integrable and has the exact half-factor bound. -/
theorem quinticBandProduct_inverse_L1_bound {ε : ℝ} (hε : 0 < ε)
    {P P₁ P₂ : ℝ → ℂ} (hP : ∀ ξ, HasDerivAt P (P₁ ξ) ξ)
    (hP₁ : ∀ ξ, HasDerivAt P₁ (P₂ ξ) ξ) (hP₂ : Continuous P₂) :
    Integrable (angularInverseFourier (quinticBandProduct ε P)) ∧
      (∫ x, ‖angularInverseFourier (quinticBandProduct ε P) x‖) ≤
        (1 / 2) * ((∫ ξ, ‖quinticBandProduct ε P ξ‖) +
          ∫ ξ, ‖quinticBandProductCurvature ε P P₁ P₂ ξ‖) := by
  have hcP : Continuous P := continuous_iff_continuousAt.mpr (fun ξ ↦ (hP ξ).continuousAt)
  have hcP₁ : Continuous P₁ := continuous_iff_continuousAt.mpr (fun ξ ↦ (hP₁ ξ).continuousAt)
  have hg := integrable_quinticBandProduct hε hcP
  have hg₂ := integrable_quinticBandProductCurvature hε hcP hcP₁ hP₂
  have hid := angularFourier_quinticBandProduct_secondDerivative hε hP hP₁ hP₂
  exact ⟨integrable_angularInverseFourier_of_secondDerivative_identity hg hg₂ hid,
    integral_norm_angularInverseFourier_le_of_secondDerivative_identity hg hg₂ hid⟩

end LpSelfSimilar.Fourier
