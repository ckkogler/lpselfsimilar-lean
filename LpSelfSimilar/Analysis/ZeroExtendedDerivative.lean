module

public import LpSelfSimilar.Analysis.DerivativeGluing
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Almost-everywhere differentiation of an interval extension by zero

A function agreeing with a differentiable formula inside an interval and with
zero outside has the indicated derivative away from the two endpoints. Lebesgue
volume gives those endpoints measure zero. No differentiability at joins is
assumed or asserted by this reusable statement.
-/

open Set MeasureTheory Filter
open scoped Topology

namespace LpSelfSimilar.Analysis

/-- Differentiate an interval formula extended by zero, ignoring only its endpoints. -/
theorem ae_hasDerivAt_of_eqOn_zero_off_Ioo {f g g' : ℝ → ℝ} {a b : ℝ}
    (he : EqOn f g (Icc a b)) (hz : ∀ x, x ≤ a ∨ b ≤ x → f x = 0)
    (hd : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x) :
    ∀ᵐ x, HasDerivAt f ((Ioo a b).indicator g' x) x := by
  have ha : ∀ᵐ x : ℝ, x ≠ a := by simp [ae_iff]
  have hb : ∀ᵐ x : ℝ, x ≠ b := by simp [ae_iff]
  filter_upwards [ha, hb] with x hxa hxb
  by_cases hx : x ∈ Ioo a b
  · rw [indicator_of_mem hx]
    apply (hd x hx).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact he ⟨hy.1.le, hy.2.le⟩
  · rw [indicator_of_notMem hx]
    apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
    have ho : x < a ∨ b < x := by
      by_cases h : a < x
      · exact Or.inr (lt_of_le_of_ne (le_of_not_gt (fun h' ↦ hx ⟨h, h'⟩)) hxb.symm)
      · exact Or.inl (lt_of_le_of_ne (le_of_not_gt h) hxa)
    rcases ho with ho | ho
    · filter_upwards [isOpen_Iio.mem_nhds ho] with y hy
      exact hz y (Or.inl (show y < a from hy).le)
    · filter_upwards [isOpen_Ioi.mem_nhds ho] with y hy
      exact hz y (Or.inr (show b < y from hy).le)

end LpSelfSimilar.Analysis
