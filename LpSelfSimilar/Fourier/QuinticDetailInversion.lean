module

public import LpSelfSimilar.Fourier.QuinticDetailProduct
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

@[expose] public section

/-!
# Exact inverse-transform bound for the full quintic detail product

Positive-band integration by parts and reflected-band integration by parts are
combined with the correct first-derivative sign. The resulting estimate uses
the actual second derivative of `psiHat*P`, with only ordinary `C2` smoothness
of the amplitude. The cutoff's own endpoint behavior is entirely derived.
-/

open MeasureTheory

namespace LpSelfSimilar.Fourier

/-- The full detail product satisfies the proved second-derivative transform identity. -/
theorem angularFourier_quinticDetailProduct_secondDerivative {ε : ℝ} (hε : 0 < ε)
    {P P₁ P₂ : ℝ → ℂ} (hP : ∀ ξ, HasDerivAt P (P₁ ξ) ξ)
    (hP₁ : ∀ ξ, HasDerivAt P₁ (P₂ ξ) ξ) (hP₂ : Continuous P₂) (x : ℝ) :
    (∫ ξ, angularFourierPhase x ξ * quinticDetailProductCurvature ε P P₁ P₂ ξ) =
      -(x : ℂ) ^ 2 * ∫ ξ, angularFourierPhase x ξ * quinticDetailProduct ε P ξ := by
  have hcP : Continuous P := continuous_iff_continuousAt.mpr (fun ξ ↦ (hP ξ).continuousAt)
  have hcP₁ : Continuous P₁ := continuous_iff_continuousAt.mpr (fun ξ ↦ (hP₁ ξ).continuousAt)
  have hrP : ∀ ξ, HasDerivAt (fun t ↦ P (-t)) (-P₁ (-ξ)) ξ := by
    intro ξ
    convert! (hP (-ξ)).scomp ξ (hasDerivAt_neg' (x := ξ)) using 1 <;>
      simp only [Function.comp_apply, Pi.neg_apply, id_eq, neg_one_smul, neg_neg] <;> ring
  have hrP₁ : ∀ ξ, HasDerivAt (fun t ↦ -P₁ (-t)) (P₂ (-ξ)) ξ := by
    intro ξ
    convert! ((hP₁ (-ξ)).scomp ξ (hasDerivAt_neg' (x := ξ))).neg using 1 <;>
      simp only [Function.comp_apply, Pi.neg_apply, id_eq, neg_one_smul, neg_neg] <;> ring
  have hp := angularFourier_quinticBandProduct_secondDerivative hε hP hP₁ hP₂
  have hn := angularFourier_secondDerivative_identity_reflect
    (angularFourier_quinticBandProduct_secondDerivative hε hrP hrP₁ (hP₂.comp continuous_neg))
  have h := angularFourier_secondDerivative_identity_add
    (integrable_quinticBandProduct hε hcP)
    (integrable_quinticBandProductCurvature hε hcP hcP₁ hP₂)
    (integrable_quinticBandProduct hε (hcP.comp continuous_neg)).comp_neg
    (integrable_quinticBandProductCurvature hε (hcP.comp continuous_neg)
      (hcP₁.comp continuous_neg).neg (hP₂.comp continuous_neg)).comp_neg hp hn x
  simp only [Function.comp_def] at h
  rw [show -(fun t ↦ P₁ (-t)) = (fun t ↦ -P₁ (-t)) from rfl] at h
  simpa only [← quinticDetailProduct_eq_bands, ← quinticDetailProductCurvature_eq_bands] using h

/-- The actual second derivative of the full product is integrable. -/
theorem integrable_deriv_deriv_quinticDetailProduct {ε : ℝ} (hε : 0 < ε)
    {P P₁ P₂ : ℝ → ℂ} (hP : ∀ ξ, HasDerivAt P (P₁ ξ) ξ)
    (hP₁ : ∀ ξ, HasDerivAt P₁ (P₂ ξ) ξ) (hP₂ : Continuous P₂) :
    Integrable (deriv (deriv (quinticDetailProduct ε P))) := by
  have hcP : Continuous P := continuous_iff_continuousAt.mpr (fun ξ ↦ (hP ξ).continuousAt)
  have hcP₁ : Continuous P₁ := continuous_iff_continuousAt.mpr (fun ξ ↦ (hP₁ ξ).continuousAt)
  exact (integrable_quinticDetailProductCurvature hε hcP hcP₁ hP₂).congr
    (ae_deriv_deriv_quinticDetailProduct hε hP hP₁).symm

/-- The inverse estimate uses the actual second derivative, with all cutoff hypotheses proved. -/
theorem quinticDetailProduct_inverse_L1_bound_of_derivative_data {ε : ℝ} (hε : 0 < ε)
    {P P₁ P₂ : ℝ → ℂ} (hP : ∀ ξ, HasDerivAt P (P₁ ξ) ξ)
    (hP₁ : ∀ ξ, HasDerivAt P₁ (P₂ ξ) ξ) (hP₂ : Continuous P₂) :
    Integrable (angularInverseFourier (quinticDetailProduct ε P)) ∧
      (∫ x, ‖angularInverseFourier (quinticDetailProduct ε P) x‖) ≤
        (1 / 2) * ((∫ ξ, ‖quinticDetailProduct ε P ξ‖) +
          ∫ ξ, ‖deriv (deriv (quinticDetailProduct ε P)) ξ‖) := by
  have hg := integrable_quinticDetailProduct hε
    (continuous_iff_continuousAt.mpr (fun ξ ↦ (hP ξ).continuousAt))
  have hg₂ := integrable_deriv_deriv_quinticDetailProduct hε hP hP₁ hP₂
  have hid (x : ℝ) :
      (∫ ξ, angularFourierPhase x ξ * deriv (deriv (quinticDetailProduct ε P)) ξ) =
        -(x : ℂ) ^ 2 * ∫ ξ, angularFourierPhase x ξ * quinticDetailProduct ε P ξ := by
    calc
      _ = ∫ ξ, angularFourierPhase x ξ * quinticDetailProductCurvature ε P P₁ P₂ ξ := by
        apply integral_congr_ae
        filter_upwards [ae_deriv_deriv_quinticDetailProduct hε hP hP₁] with ξ hξ
        rw [hξ]
      _ = _ := angularFourier_quinticDetailProduct_secondDerivative hε hP hP₁ hP₂ x
  exact ⟨integrable_angularInverseFourier_of_secondDerivative_identity hg hg₂ hid,
    integral_norm_angularInverseFourier_le_of_secondDerivative_identity hg hg₂ hid⟩

/-- For every C2 amplitude the actual detail product satisfies the half-factor inverse estimate. -/
theorem quinticDetailProduct_inverse_L1_bound {ε : ℝ} (hε : 0 < ε)
    {P : ℝ → ℂ} (hP : ContDiff ℝ 2 P) :
    Integrable (quinticDetailProduct ε P) ∧
      Integrable (deriv (deriv (quinticDetailProduct ε P))) ∧
        Integrable (angularInverseFourier (quinticDetailProduct ε P)) ∧
          (∫ x, ‖angularInverseFourier (quinticDetailProduct ε P) x‖) ≤
            (1 / 2) * ((∫ ξ, ‖quinticDetailProduct ε P ξ‖) +
              ∫ ξ, ‖deriv (deriv (quinticDetailProduct ε P)) ξ‖) := by
  have hd : ∀ ξ, HasDerivAt P (deriv P ξ) ξ := fun ξ ↦ (hP.differentiable (by norm_num) ξ).hasDerivAt
  have hd₁ : ∀ ξ, HasDerivAt (deriv P) (deriv (deriv P) ξ) ξ :=
    fun ξ ↦ (hP.differentiable_deriv_two ξ).hasDerivAt
  have hP' : ContDiff ℝ 1 (deriv P) := hP.deriv'
  have hc₂ : Continuous (deriv (deriv P)) := hP'.continuous_deriv_one
  exact ⟨integrable_quinticDetailProduct hε hP.continuous,
    integrable_deriv_deriv_quinticDetailProduct hε hd hd₁ hc₂,
    quinticDetailProduct_inverse_L1_bound_of_derivative_data hε hd hd₁ hc₂⟩

end LpSelfSimilar.Fourier
