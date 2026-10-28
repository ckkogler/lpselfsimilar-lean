module

public import LpSelfSimilar.Fourier.QuinticMeanProductEstimates
public import LpSelfSimilar.Fourier.QuinticDetailInversion
public import LpSelfSimilar.Fourier.MeanProductDerivatives

@[expose] public section

/-!
# The averaged inverse estimate with the paper's exact prefactor

Only averaged amplitude derivative bounds are used. Each inverse is the actual
normalized oscillatory integral, and its integrability is derived from the C2
amplitude and the proved cutoff endpoint data. The probability version averages
over the original finite label law, including labels of weight zero.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace LpSelfSimilar.Fourier

/-- Averaging the inverse estimate retains the exact coefficients of all three weights. -/
theorem sum_quinticDetail_inverse_L1_bound {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (P : ι → ℝ → ℂ)
    {ε D B : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1 / 100000)
    (hD : 0 ≤ D) (hB : 0 ≤ B) (hP : ∀ i, ContDiff ℝ 2 (P i))
    (hb : ∀ ξ, |(|ξ| - 1)| ≤ ε → ∀ j ≤ 2,
      (∑ i, w i * ‖iteratedDeriv j (P i) ξ‖) ≤ D ^ j * B) :
    (∑ i, w i * ∫ x, ‖angularInverseFourier (quinticDetailProduct ε (P i)) x‖) ≤
      (1 / 2) * (21 / 10 + 32 / ε ^ 2 + 14 * D / ε + (21 / 10) * D ^ 2) * B := by
  have hc₀ i : Continuous (P i) := (hP i).continuous
  have hc₁ i : Continuous (deriv (P i)) := (hP i).continuous_deriv (by norm_num)
  have hc₂ i : Continuous (deriv (deriv (P i))) := by
    have h : ContDiff ℝ 1 (deriv (P i)) := (hP i).deriv'
    exact h.continuous_deriv_one
  have h₀ ξ (hξ : |(|ξ| - 1)| ≤ ε) : (∑ i, w i * ‖P i ξ‖) ≤ B := by
    simpa only [iteratedDeriv_zero, pow_zero, one_mul] using hb ξ hξ 0 (by omega)
  have h₁ ξ (hξ : |(|ξ| - 1)| ≤ ε) : (∑ i, w i * ‖deriv (P i) ξ‖) ≤ D * B := by
    simpa only [iteratedDeriv_one, pow_one] using hb ξ hξ 1 (by omega)
  have h₂ ξ (hξ : |(|ξ| - 1)| ≤ ε) :
      (∑ i, w i * ‖deriv (deriv (P i)) ξ‖) ≤ D ^ 2 * B := by
    simpa only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one,
      iteratedDeriv_zero]
      using hb ξ hξ 2 (by omega)
  have hg := sum_integral_norm_quinticDetailProduct_le w P hε hεsmall hB hc₀ h₀
  have hg₂ := sum_integral_norm_quinticDetailProductCurvature_le w hw P
    (fun i ↦ deriv (P i)) (fun i ↦ deriv (deriv (P i))) hε hεsmall hB
    (mul_nonneg hD hB) (mul_nonneg (sq_nonneg D) hB) hc₀ hc₁ hc₂ h₀ h₁ h₂
  have he i : (∫ ξ, ‖deriv (deriv (quinticDetailProduct ε (P i))) ξ‖) =
      ∫ ξ, ‖quinticDetailProductCurvature ε (P i) (deriv (P i))
        (deriv (deriv (P i))) ξ‖ := by
    apply integral_congr_ae
    filter_upwards [ae_deriv_deriv_quinticDetailProduct hε
      (fun ξ ↦ ((hP i).differentiable (by norm_num) ξ).hasDerivAt)
      (fun ξ ↦ ((hP i).differentiable_deriv_two ξ).hasDerivAt)] with ξ hξ
    rw [hξ]
  calc
    _ ≤ ∑ i, w i * ((1 / 2) * ((∫ ξ, ‖quinticDetailProduct ε (P i) ξ‖) +
        ∫ ξ, ‖quinticDetailProductCurvature ε (P i) (deriv (P i))
          (deriv (deriv (P i))) ξ‖)) := by
      apply Finset.sum_le_sum
      intro i hi
      have h := (quinticDetailProduct_inverse_L1_bound hε (hP i)).2.2.2
      rw [he i] at h
      exact mul_le_mul_of_nonneg_left h (hw i)
    _ = (1 / 2) * ((∑ i, w i * ∫ ξ, ‖quinticDetailProduct ε (P i) ξ‖) +
        ∑ i, w i * ∫ ξ, ‖quinticDetailProductCurvature ε (P i) (deriv (P i))
          (deriv (deriv (P i))) ξ‖) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring
    _ ≤ (1 / 2) * ((21 / 10) * B +
        ((32 / ε ^ 2) * B + (14 / ε) * (D * B) + (21 / 10) * (D ^ 2 * B))) := by
      linarith
    _ = _ := by ring

/-- The numerical prefactor absorbs every inverse-estimate term, including the zeroth one. -/
theorem quintic_inverse_prefactor_le {ε D : ℝ} (hε : 0 < ε)
    (hεsmall : ε ≤ 1 / 100000) (hD : 0 ≤ D) :
    (1 / 2) * (21 / 10 + 32 / ε ^ 2 + 14 * D / ε + (21 / 10) * D ^ 2) ≤
      20 / ε ^ 2 * (1 + ε * D) ^ 2 := by
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hε)).mp
  have hε1 : ε ≤ 1 := by linarith
  have hεsq : ε ^ 2 ≤ 1 := by nlinarith
  have hεD : 0 ≤ ε * D := mul_nonneg hε.le hD
  field_simp
  nlinarith [sq_nonneg (ε * D)]

/-- The convenient exact twenty-prefactor bound for any finite nonnegative label weights. -/
theorem sum_quinticDetail_inverse_L1_le_twenty {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (P : ι → ℝ → ℂ)
    {ε D B : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1 / 100000)
    (hD : 0 ≤ D) (hB : 0 ≤ B) (hP : ∀ i, ContDiff ℝ 2 (P i))
    (hb : ∀ ξ, |(|ξ| - 1)| ≤ ε → ∀ j ≤ 2,
      (∑ i, w i * ‖iteratedDeriv j (P i) ξ‖) ≤ D ^ j * B) :
    (∑ i, w i * ∫ x, ‖angularInverseFourier (quinticDetailProduct ε (P i)) x‖) ≤
      20 / ε ^ 2 * (1 + ε * D) ^ 2 * B :=
  (sum_quinticDetail_inverse_L1_bound w hw P hε hεsmall hD hB hP hb).trans
    (mul_le_mul_of_nonneg_right (quintic_inverse_prefactor_le hε hεsmall hD) hB)

/-- The averaged inverse bound for the actual finite label probability measure. -/
theorem integral_quinticDetail_inverse_L1_le_twenty {ι : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (p : PMF ι) (P : ι → ℝ → ℂ)
    {ε D B : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1 / 100000)
    (hD : 0 ≤ D) (hB : 0 ≤ B) (hP : ∀ i, ContDiff ℝ 2 (P i))
    (hb : ∀ ξ, |(|ξ| - 1)| ≤ ε → ∀ j ≤ 2,
      (∫ i, ‖iteratedDeriv j (P i) ξ‖ ∂p.toMeasure) ≤ D ^ j * B) :
    (∫ i, (∫ x, ‖angularInverseFourier (quinticDetailProduct ε (P i)) x‖) ∂p.toMeasure) ≤
      20 / ε ^ 2 * (1 + ε * D) ^ 2 * B := by
  simp_rw [PMF.integral_eq_sum, smul_eq_mul] at hb ⊢
  exact sum_quinticDetail_inverse_L1_le_twenty (fun i ↦ (p i).toReal)
    (fun i ↦ ENNReal.toReal_nonneg) P hε hεsmall hD hB hP hb

end LpSelfSimilar.Fourier
