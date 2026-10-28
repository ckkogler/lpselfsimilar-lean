module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-!
# Integrating a function supported inside an open interval

Vanishing outside the open interval includes both endpoint values. It lets the
whole-line integral agree with the oriented interval integral without any
integrability assumption; subsequent uses prove integrability separately.
-/

open Set MeasureTheory

namespace LpSelfSimilar.Analysis

/-- A function vanishing at and beyond both endpoints has exactly its interval integral. -/
theorem integral_eq_interval_of_eq_zero_off_Ioo {f : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ x, x ≤ a ∨ b ≤ x → f x = 0) :
    (∫ x, f x) = ∫ x in a..b, f x := by
  apply (intervalIntegral.integral_eq_integral_of_support_subset ?_).symm
  intro x hx
  constructor
  · by_contra h
    exact hx (hf x (Or.inl (le_of_not_gt h)))
  · by_contra h
    exact hx (hf x (Or.inr (le_of_lt (lt_of_not_ge h))))

end LpSelfSimilar.Analysis
