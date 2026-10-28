module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.Tactic

@[expose] public section

/-!
# Integrating the two tails of an even real function

Reflection identifies the negative tail with the positive one. Lebesgue
singletons have zero measure, so both endpoint conventions agree. The exact
factor two cancels the one-half weight used in Fourier energy estimates.
-/

open MeasureTheory Set

namespace LpSelfSimilar.Analysis

/-- The integral over both strict absolute tails is twice the positive tail for an even function. -/
theorem integral_abs_tail_eq_twice_Ioi {f : ℝ → ℝ} {b : ℝ}
    (hb : 0 ≤ b) (hf : Integrable f) (heven : ∀ x : ℝ, f (-x) = f x) :
    (∫ x : ℝ in {x | b < |x|}, f x) = 2 * ∫ x : ℝ in Ioi b, f x := by
  have hs : {x : ℝ | b < |x|} = Iio (-b) ∪ Ioi b := by
    ext x
    simp only [mem_setOf_eq, lt_abs, mem_union, mem_Iio, mem_Ioi]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl (by linarith)
    · rintro (h | h)
      · exact Or.inr (by linarith)
      · exact Or.inl h
  have hd : Disjoint (Iio (-b)) (Ioi b) := by
    rw [disjoint_left]
    intro x hx hn
    have h0 : x < -b := hx
    have h1 : b < x := hn
    linarith
  have he : (∫ x : ℝ in Iio (-b), f x) = ∫ x : ℝ in Ioi b, f x := by
    calc
      _ = ∫ x : ℝ in Iic (-b), f x := integral_Iic_eq_integral_Iio.symm
      _ = ∫ x : ℝ in Ioi b, f (-x) := (integral_comp_neg_Ioi b f).symm
      _ = _ := setIntegral_congr_fun measurableSet_Ioi (fun x hx => heven x)
  rw [hs, setIntegral_union hd measurableSet_Ioi hf.integrableOn hf.integrableOn, he]
  ring

end LpSelfSimilar.Analysis
