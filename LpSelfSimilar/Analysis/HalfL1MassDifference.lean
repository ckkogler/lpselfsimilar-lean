module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic

@[expose] public section

/-!
# The half-L1 bound for equal-mass integrable functions

An integrable real function of integral zero has equal total positive and
negative mass. Its integral on any measurable set is therefore bounded in
absolute value by half its L1 norm. Applied to the difference of probability
densities, this retains the factor one half needed in the Gaussian-to-L2 step.
-/

open MeasureTheory Set

namespace LpSelfSimilar.Analysis

/-- An integral-zero real function has set integrals bounded by half its L1 norm. -/
theorem abs_setIntegral_le_half_integral_abs_of_integral_eq_zero
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {h : X → ℝ}
    (hh : Integrable h μ) (hzero : ∫ x, h x ∂μ = 0)
    {E : Set X} (hE : MeasurableSet E) :
    |∫ x in E, h x ∂μ| ≤ (∫ x, |h x| ∂μ) / 2 := by
  have hsum := integral_add_compl hE hh
  have habssum := integral_add_compl hE hh.abs
  have he : |∫ x in E, h x ∂μ| ≤ ∫ x in E, |h x| ∂μ := abs_integral_le_integral_abs
  have hc : |∫ x in Eᶜ, h x ∂μ| ≤ ∫ x in Eᶜ, |h x| ∂μ := abs_integral_le_integral_abs
  have hneg : (∫ x in Eᶜ, h x ∂μ) = -(∫ x in E, h x ∂μ) := by linarith
  rw [hneg, abs_neg] at hc
  linarith

/-- Equal-mass integrable functions differ on any measurable set by at most half their L1 distance. -/
theorem abs_setIntegral_sub_le_half_integral_abs
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {f g : X → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hmass : (∫ x, f x ∂μ) = ∫ x, g x ∂μ) {E : Set X} (hE : MeasurableSet E) :
    |(∫ x in E, f x ∂μ) - ∫ x in E, g x ∂μ| ≤ (∫ x, |f x - g x| ∂μ) / 2 := by
  have hzero : (∫ x, (f - g) x ∂μ) = 0 := by
    change (∫ x, f x - g x ∂μ) = 0
    rw [integral_sub hf hg, hmass, sub_self]
  have h := abs_setIntegral_le_half_integral_abs_of_integral_eq_zero μ (hf.sub hg) hzero hE
  simpa only [Pi.sub_apply, integral_sub hf.integrableOn hg.integrableOn] using h

end LpSelfSimilar.Analysis
