module

public import LpSelfSimilar.Analysis.HalfL1MassDifference
public import LpSelfSimilar.Analysis.BoundedApproximationMass

@[expose] public section

/-!
# Small-set bounds from an equal-mass bounded approximation

The equality of total integrals improves the usual L1 error term by one half.
We prove the probability-density normalization explicitly and retain the exact
half error in the universal measurable-set estimate. Infinite-volume sets are
handled separately, so no finite-volume assumption survives in that estimate.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LpSelfSimilar.Analysis

/-- A nonnegative integrable density of an actual probability measure has integral one. -/
theorem integral_eq_one_of_probability_density {X : Type*} [MeasurableSpace X]
    (μ σ : Measure X) [IsProbabilityMeasure σ] {f : X → ℝ}
    (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x)
    (hσ : σ = μ.withDensity (fun x => ENNReal.ofReal (f x))) : ∫ x, f x ∂μ = 1 := by
  have h : ENNReal.ofReal (∫ x, f x ∂μ) = 1 := by
    calc
      _ = ∫⁻ x, ENNReal.ofReal (f x) ∂μ :=
        ofReal_integral_eq_lintegral_ofReal hf (ae_of_all _ hf0)
      _ = σ Set.univ := by rw [hσ, withDensity_apply _ MeasurableSet.univ]; simp
      _ = 1 := measure_univ
  have ht := congrArg ENNReal.toReal h
  simpa only [ENNReal.toReal_ofReal (integral_nonneg hf0), ENNReal.toReal_one] using ht

/-- Equal total masses give the half-L1 error bound for sets with a finite volume budget. -/
theorem measure_le_of_equal_mass_bounded_approximation {X : Type*} [MeasurableSpace X]
    {μ σ : Measure X} {f g : X → ℝ} (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x)
    (hσ : σ = μ.withDensity (fun x => ENNReal.ofReal (f x))) (hg : Integrable g μ)
    (hmass : (∫ x, f x ∂μ) = ∫ x, g x ∂μ) {C e t : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ x, g x ≤ C)
    (herr : (∫ x, |f x - g x| ∂μ) ≤ 2 * e) {E : Set X} (hE : MeasurableSet E)
    (hvol : μ E ≤ ENNReal.ofReal t) (ht : 0 ≤ t) : σ E ≤ ENNReal.ofReal (e + C * t) := by
  have hfinite : μ E < ⊤ := hvol.trans_lt ENNReal.ofReal_lt_top
  letI : IsFiniteMeasure (μ.restrict E) := ⟨by simpa using hfinite⟩
  have hvolreal : μ.real E ≤ t := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_lt_top.ne hvol
    simpa only [measureReal_def, ENNReal.toReal_ofReal ht] using h
  have hdiff : (∫ x in E, f x ∂μ) - ∫ x in E, g x ∂μ ≤ e := by
    have h := abs_setIntegral_sub_le_half_integral_abs μ hf hg hmass hE
    have hle := le_abs_self ((∫ x in E, f x ∂μ) - ∫ x in E, g x ∂μ)
    linarith
  have hgE : (∫ x in E, g x ∂μ) ≤ C * t := by
    have h := integral_mono hg.integrableOn (integrable_const (μ := μ.restrict E) C) hbound
    simp only [integral_const, Measure.restrict_apply_univ, measureReal_def, smul_eq_mul] at h
    exact h.trans (by simpa only [measureReal_def, mul_comm] using
      mul_le_mul_of_nonneg_left hvolreal hC)
  rw [hσ, withDensity_apply _ hE,
    ← ofReal_integral_eq_lintegral_ofReal hf.integrableOn (ae_of_all _ hf0)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- The universal small-set estimate retains half the L1 error and includes infinite-volume sets. -/
theorem small_set_bound_of_equal_mass_bounded_approximation {X : Type*} [MeasurableSpace X]
    {μ σ : Measure X} {f g : X → ℝ} (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x)
    (hσ : σ = μ.withDensity (fun x => ENNReal.ofReal (f x))) (hg : Integrable g μ)
    (hmass : (∫ x, f x ∂μ) = ∫ x, g x ∂μ) {C e : ℝ}
    (hC : 0 < C) (he : 0 ≤ e) (hbound : ∀ x, g x ≤ C)
    (herr : (∫ x, |f x - g x| ∂μ) ≤ 2 * e) {E : Set X} (hE : MeasurableSet E) :
    σ E ≤ ENNReal.ofReal C * μ E + ENNReal.ofReal e := by
  by_cases htop : μ E = ∞
  · simp [htop, (ENNReal.ofReal_pos.mpr hC).ne']
  · have h := measure_le_of_equal_mass_bounded_approximation hf hf0 hσ hg hmass hC.le
      hbound herr hE (t := (μ E).toReal) (by rw [ENNReal.ofReal_toReal htop]) ENNReal.toReal_nonneg
    have heq : ENNReal.ofReal (e + C * (μ E).toReal) =
        ENNReal.ofReal C * μ E + ENNReal.ofReal e := by
      rw [ENNReal.ofReal_add he (by positivity), ENNReal.ofReal_mul hC.le,
        ENNReal.ofReal_toReal htop, add_comm]
    exact h.trans_eq heq

end LpSelfSimilar.Analysis
