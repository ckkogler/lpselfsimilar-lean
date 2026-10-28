module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
Moment bounds for bounded real probability laws. Almost-everywhere support
bounds suffice, so zero-probability outcomes impose no conditions.
-/

open MeasureTheory Real

namespace LpSelfSimilar

lemma integrable_abs_pow_of_ae_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    {R : ℝ} (hR : 0 ≤ R) (hb : ∀ᵐ u ∂μ, |u| ≤ R) (n : ℕ) :
    Integrable (fun u : ℝ ↦ |u| ^ n) μ := by
  apply (integrable_const (R ^ n)).mono' (by fun_prop)
  filter_upwards [hb] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg u) n)]
  exact pow_le_pow_left₀ (abs_nonneg u) hu n

lemma integrable_id_of_ae_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    {R : ℝ} (hR : 0 ≤ R) (hb : ∀ᵐ u ∂μ, |u| ≤ R) :
    Integrable (fun u : ℝ ↦ u) μ := by
  apply (integrable_norm_iff (by fun_prop)).mp
  simpa only [Real.norm_eq_abs, pow_one] using integrable_abs_pow_of_ae_bound μ hR hb 1

lemma integrable_sq_of_ae_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    {R : ℝ} (hR : 0 ≤ R) (hb : ∀ᵐ u ∂μ, |u| ≤ R) :
    Integrable (fun u : ℝ ↦ u ^ 2) μ := by
  simpa only [sq_abs] using integrable_abs_pow_of_ae_bound μ hR hb 2

lemma integral_sq_le_of_ae_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {R : ℝ} (hR : 0 ≤ R) (hb : ∀ᵐ u ∂μ, |u| ≤ R) :
    (∫ u : ℝ, u ^ 2 ∂μ) ≤ R ^ 2 := by
  have h := integral_mono_ae (integrable_sq_of_ae_bound μ hR hb) (integrable_const (R ^ 2))
    (hb.mono (fun u hu ↦ by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg u) hu 2))
  simpa using h

lemma integral_abs_cube_le_of_ae_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    {R : ℝ} (hR : 0 ≤ R) (hb : ∀ᵐ u ∂μ, |u| ≤ R) :
    (∫ u : ℝ, |u| ^ 3 ∂μ) ≤ R * ∫ u : ℝ, u ^ 2 ∂μ := by
  have h := integral_mono_ae (integrable_abs_pow_of_ae_bound μ hR hb 3)
    ((integrable_sq_of_ae_bound μ hR hb).const_mul R) (hb.mono (fun u hu ↦ by
      have hh := mul_le_mul_of_nonneg_right hu (sq_nonneg u)
      have he : |u| ^ 3 = |u| * u ^ 2 := by rw [pow_succ, sq_abs]; ring
      change |u| ^ 3 ≤ R * u ^ 2
      rw [he]
      exact hh))
  simpa only [integral_const_mul] using h

end LpSelfSimilar
