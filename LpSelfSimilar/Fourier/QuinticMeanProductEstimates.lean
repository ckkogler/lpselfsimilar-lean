module

public import LpSelfSimilar.Fourier.QuinticDetailWeights
public import LpSelfSimilar.Fourier.QuinticDetailProduct
public import LpSelfSimilar.Analysis.FiniteWeightedIntegral

@[expose] public section

/-!
# Averaging the two norms in the inverse estimate

Amplitude bounds are required only in mean and only on the two frequency bands.
The detail and its derivative formulas vanish elsewhere. Finite expectation is
interchanged with frequency integration before applying the three weight bounds.
-/

open MeasureTheory
open scoped BigOperators

namespace LpSelfSimilar.Fourier

/-- Pointwise triangle inequality for the explicit product curvature. -/
theorem norm_quinticDetailProductCurvature_le (ε ξ : ℝ) (P P₁ P₂ : ℝ → ℂ) :
    ‖quinticDetailProductCurvature ε P P₁ P₂ ξ‖ ≤
      |quinticFourierDetailCurvature ε ξ| * ‖P ξ‖ +
        2 * |quinticFourierDetailSlope ε ξ| * ‖P₁ ξ‖ +
          |quinticFourierDetail ε ξ| * ‖P₂ ξ‖ := by
  unfold quinticDetailProductCurvature
  calc
    _ ≤ ‖(quinticFourierDetailCurvature ε ξ : ℂ) * P ξ‖ +
        ‖2 * (quinticFourierDetailSlope ε ξ : ℂ) * P₁ ξ‖ +
          ‖(quinticFourierDetail ε ξ : ℂ) * P₂ ξ‖ := norm_add₃_le
    _ = _ := by simp [norm_mul, Complex.norm_real, Real.norm_eq_abs]

/-- Mean bounds on the band control the actual product everywhere. -/
theorem sum_norm_quinticDetailProduct_le {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (P : ι → ℝ → ℂ) {ε B : ℝ} (hε : 0 < ε)
    (hb : ∀ ξ, |(|ξ| - 1)| ≤ ε → (∑ i, w i * ‖P i ξ‖) ≤ B) (ξ : ℝ) :
    (∑ i, w i * ‖quinticDetailProduct ε (P i) ξ‖) ≤
      |quinticFourierDetail ε ξ| * B := by
  by_cases hξ : |(|ξ| - 1)| ≤ ε
  · calc
      _ = |quinticFourierDetail ε ξ| * ∑ i, w i * ‖P i ξ‖ := by
        simp only [quinticDetailProduct, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hb ξ hξ) (abs_nonneg _)
  · have hz := (quinticDetail_formulas_zero_off_band hε (lt_of_not_ge hξ)).1
    simp [quinticDetailProduct, hz]

/-- The curvature estimate retains the original weights and three separate mean bounds. -/
theorem sum_norm_quinticDetailProductCurvature_le {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (P P₁ P₂ : ι → ℝ → ℂ)
    {ε B₀ B₁ B₂ : ℝ} (hε : 0 < ε)
    (h₀ : ∀ ξ, |(|ξ| - 1)| ≤ ε → (∑ i, w i * ‖P i ξ‖) ≤ B₀)
    (h₁ : ∀ ξ, |(|ξ| - 1)| ≤ ε → (∑ i, w i * ‖P₁ i ξ‖) ≤ B₁)
    (h₂ : ∀ ξ, |(|ξ| - 1)| ≤ ε → (∑ i, w i * ‖P₂ i ξ‖) ≤ B₂) (ξ : ℝ) :
    (∑ i, w i * ‖quinticDetailProductCurvature ε (P i) (P₁ i) (P₂ i) ξ‖) ≤
      |quinticFourierDetailCurvature ε ξ| * B₀ +
        2 * |quinticFourierDetailSlope ε ξ| * B₁ + |quinticFourierDetail ε ξ| * B₂ := by
  by_cases hξ : |(|ξ| - 1)| ≤ ε
  · calc
      _ ≤ ∑ i, w i * (|quinticFourierDetailCurvature ε ξ| * ‖P i ξ‖ +
          2 * |quinticFourierDetailSlope ε ξ| * ‖P₁ i ξ‖ +
            |quinticFourierDetail ε ξ| * ‖P₂ i ξ‖) :=
        Finset.sum_le_sum (fun i hi ↦ mul_le_mul_of_nonneg_left
          (norm_quinticDetailProductCurvature_le ε ξ (P i) (P₁ i) (P₂ i)) (hw i))
      _ = |quinticFourierDetailCurvature ε ξ| * (∑ i, w i * ‖P i ξ‖) +
          2 * |quinticFourierDetailSlope ε ξ| * (∑ i, w i * ‖P₁ i ξ‖) +
            |quinticFourierDetail ε ξ| * (∑ i, w i * ‖P₂ i ξ‖) := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum,
          mul_comm, mul_left_comm, mul_assoc]
      _ ≤ _ := add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left (h₀ ξ hξ) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (h₁ ξ hξ) (by positivity)))
        (mul_le_mul_of_nonneg_left (h₂ ξ hξ) (abs_nonneg _))
  · obtain ⟨hz, hz₁, hz₂⟩ := quinticDetail_formulas_zero_off_band hε (lt_of_not_ge hξ)
    simp [quinticDetailProductCurvature, hz, hz₁, hz₂]

/-- Integrating the mean product bound uses exactly the detail mass bound 2.1. -/
theorem sum_integral_norm_quinticDetailProduct_le {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (P : ι → ℝ → ℂ) {ε B : ℝ} (hε : 0 < ε)
    (hεsmall : ε ≤ 1 / 100000) (hB : 0 ≤ B) (hP : ∀ i, Continuous (P i))
    (hb : ∀ ξ, |(|ξ| - 1)| ≤ ε → (∑ i, w i * ‖P i ξ‖) ≤ B) :
    (∑ i, w i * ∫ ξ, ‖quinticDetailProduct ε (P i) ξ‖) ≤ (21 / 10) * B := by
  have h := Analysis.sum_mul_integral_norm_le w (fun i ↦ quinticDetailProduct ε (P i))
    (fun i ↦ integrable_quinticDetailProduct hε (hP i))
    ((integrable_quinticFourierDetail hε).abs.mul_const B)
    (sum_norm_quinticDetailProduct_le w P hε hb)
  rw [integral_mul_const] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (quinticDetail_formula_integral_bounds hε hεsmall).1 hB)

/-- The integrated mean curvature bound with the exact three product-rule coefficients. -/
theorem sum_integral_norm_quinticDetailProductCurvature_le {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (P P₁ P₂ : ι → ℝ → ℂ)
    {ε B₀ B₁ B₂ : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1 / 100000)
    (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hP : ∀ i, Continuous (P i)) (hP₁ : ∀ i, Continuous (P₁ i))
    (hP₂ : ∀ i, Continuous (P₂ i))
    (h₀ : ∀ ξ, |(|ξ| - 1)| ≤ ε → (∑ i, w i * ‖P i ξ‖) ≤ B₀)
    (h₁ : ∀ ξ, |(|ξ| - 1)| ≤ ε → (∑ i, w i * ‖P₁ i ξ‖) ≤ B₁)
    (h₂ : ∀ ξ, |(|ξ| - 1)| ≤ ε → (∑ i, w i * ‖P₂ i ξ‖) ≤ B₂) :
    (∑ i, w i * ∫ ξ, ‖quinticDetailProductCurvature ε (P i) (P₁ i) (P₂ i) ξ‖) ≤
      (32 / ε ^ 2) * B₀ + (14 / ε) * B₁ + (21 / 10) * B₂ := by
  have hi₀ := (integrable_quinticFourierDetail hε).abs
  have hi₁ := (integrable_quinticFourierDetailSlope hε).abs
  have hi₂ := (integrable_quinticFourierDetailCurvature ε).abs
  have h := Analysis.sum_mul_integral_norm_le w
    (fun i ↦ quinticDetailProductCurvature ε (P i) (P₁ i) (P₂ i))
    (fun i ↦ integrable_quinticDetailProductCurvature hε (hP i) (hP₁ i) (hP₂ i))
    (((hi₂.mul_const B₀).add ((hi₁.const_mul 2).mul_const B₁)).add (hi₀.mul_const B₂))
    (sum_norm_quinticDetailProductCurvature_le w hw P P₁ P₂ hε h₀ h₁ h₂)
  simp only [Pi.add_apply] at h
  have hi₂₁ : Integrable (fun ξ ↦ |quinticFourierDetailCurvature ε ξ| * B₀ +
      2 * |quinticFourierDetailSlope ε ξ| * B₁) :=
    (hi₂.mul_const B₀).add ((hi₁.const_mul 2).mul_const B₁)
  rw [integral_add hi₂₁
    (hi₀.mul_const B₂), integral_add (hi₂.mul_const B₀) ((hi₁.const_mul 2).mul_const B₁)] at h
  simp only [integral_mul_const, integral_const_mul] at h
  obtain ⟨hb₀, hb₁, hb₂⟩ := quinticDetail_formula_integral_bounds hε hεsmall
  have hh₀ := mul_le_mul_of_nonneg_right hb₂ hB₀
  have hh₁ := mul_le_mul_of_nonneg_right hb₁ hB₁
  have hh₂ := mul_le_mul_of_nonneg_right hb₀ hB₂
  calc
    _ ≤ _ := h
    _ ≤ (32 / ε ^ 2) * B₀ + 2 * ((7 / ε) * B₁) + (21 / 10) * B₂ := by nlinarith
    _ = _ := by ring

end LpSelfSimilar.Fourier
