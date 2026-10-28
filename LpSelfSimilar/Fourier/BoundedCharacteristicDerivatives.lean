module

public import LpSelfSimilar.Fourier.CharacteristicDerivativeLimits

@[expose] public section

/-!
# Characteristic derivatives of bounded probability laws

Actual almost-sure support bounds imply every moment. The proved characteristic
integral formula then bounds the derivative of order `k` by the support radius
to the power `k`. These estimates apply to translated conditional block laws;
no smooth density is required.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LpSelfSimilar.Fourier

/-- Bounded actual probability laws have characteristic functions of every finite smoothness order. -/
theorem contDiff_charFun_of_ae_abs_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {D : ℝ} (hb : ∀ᵐ x ∂μ, |x| ≤ D) (n : ℕ) : ContDiff ℝ n (charFun μ) := by
  apply contDiff_charFun
  apply MemLp.of_bound (by fun_prop) D
  simpa only [id_eq, Real.norm_eq_abs] using hb

/-- A support radius bounds each actual characteristic derivative by its corresponding power. -/
theorem norm_iteratedDeriv_charFun_le_of_ae_abs_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {D : ℝ}
    (hb : ∀ᵐ x ∂μ, |x| ≤ D) (k : ℕ) (s : ℝ) :
    ‖iteratedDeriv k (charFun μ) s‖ ≤ D ^ k := by
  have hm : MemLp id k μ := MemLp.of_bound (by fun_prop) D
    (by simpa only [id_eq, Real.norm_eq_abs] using hb)
  rw [iteratedDeriv_charFun hm, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul]
  have he : ∀ᵐ (x : ℝ) ∂μ, ‖(x : ℂ) ^ k * Complex.exp ((s : ℂ) * x * Complex.I)‖ ≤ D ^ k := by
    filter_upwards [hb] with x hx
    rw [show (s : ℂ) * x * Complex.I = ((s * x : ℝ) : ℂ) * Complex.I by simp]
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    exact pow_le_pow_left₀ (abs_nonneg x) hx k
  simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
    norm_integral_le_of_norm_le_const he

/-- Full mass in `[0,D]` supplies the absolute support bound for a translated conditional law. -/
theorem ae_abs_le_of_mass_Icc_eq_one (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {D : ℝ} (hμ : μ (Icc 0 D) = 1) : ∀ᵐ x ∂μ, |x| ≤ D := by
  have hm : ∀ᵐ x ∂μ, x ∈ Icc 0 D := (mem_ae_iff_prob_eq_one measurableSet_Icc).mpr hμ
  filter_upwards [hm] with x hx
  rw [abs_of_nonneg hx.1]
  exact hx.2

end LpSelfSimilar.Fourier
