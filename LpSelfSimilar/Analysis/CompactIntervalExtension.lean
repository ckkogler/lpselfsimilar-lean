module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-!
# Integrability of an interval formula extended by zero

Vanishing at and outside both endpoints identifies the support with a subset of
the half-open interval used by interval integrals. The lemmas work for arbitrary
normed vector-valued amplitudes, including complex Fourier integrands.
-/

open Set MeasureTheory

namespace LpSelfSimilar.Analysis

/-- Endpoint-inclusive vanishing gives support in the half-open interval. -/
theorem support_subset_Ioc_of_zero_off_Ioo {E : Type*} [Zero E]
    {f : ℝ → E} {a b : ℝ} (hz : ∀ x, x ≤ a ∨ b ≤ x → f x = 0) :
    Function.support f ⊆ Ioc a b := by
  intro x hx
  constructor
  · by_contra h
    exact hx (hz x (Or.inl (le_of_not_gt h)))
  · by_contra h
    exact hx (hz x (Or.inr (le_of_lt (lt_of_not_ge h))))

/-- Integrability on the compact interval gives whole-line integrability of its zero extension. -/
theorem integrable_of_intervalIntegrable_zero_off_Ioo {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {a b : ℝ} (hi : IntervalIntegrable f volume a b)
    (hz : ∀ x, x ≤ a ∨ b ≤ x → f x = 0) : Integrable f := by
  exact (integrableOn_iff_integrable_of_support_subset
    (support_subset_Ioc_of_zero_off_Ioo hz)).mp hi.1

/-- The whole-line integral equals the interval integral for an endpoint-zero extension. -/
theorem integral_eq_interval_of_zero_off_Ioo {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b : ℝ} (hz : ∀ x, x ≤ a ∨ b ≤ x → f x = 0) :
    (∫ x, f x) = ∫ x in a..b, f x :=
  (intervalIntegral.integral_eq_integral_of_support_subset
    (support_subset_Ioc_of_zero_off_Ioo hz)).symm

end LpSelfSimilar.Analysis
