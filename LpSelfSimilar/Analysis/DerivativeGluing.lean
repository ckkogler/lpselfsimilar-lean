module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.Order.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Gluing derivatives across a real threshold

Matching values and first derivatives give an actual derivative at a join.
Away from the join the selected piece agrees locally with the whole function.
This elementary rule avoids imposing global smoothness on later piecewise
polynomial cutoff derivatives.
-/

open Set Filter
open scoped Topology

namespace LpSelfSimilar.Analysis

/-- Piecewise functions across a closed half-line are differentiable when the endpoint data match. -/
theorem hasDerivAt_if_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : ℝ → F} {a x : ℝ} {f' g' : F}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x)
    (hval : f a = g a) (hder : x = a → f' = g') :
    HasDerivAt (fun y ↦ if y ≤ a then f y else g y) (if x ≤ a then f' else g') x := by
  classical
  rcases lt_trichotomy x a with hlt | heq | hgt
  · rw [if_pos hlt.le]
    apply hf.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hlt] with y hy
    have hy' : y < a := hy
    simp only [if_pos hy'.le]
  · subst x
    rw [if_pos le_rfl]
    have hl : HasDerivWithinAt (fun y ↦ if y ≤ a then f y else g y) f' (Iic a) a :=
      hf.hasDerivWithinAt.congr_of_mem (fun y hy ↦ by simp only [if_pos (show y ≤ a from hy)]) (by simp)
    have hr : HasDerivWithinAt (fun y ↦ if y ≤ a then f y else g y) g' (Ici a) a := by
      apply hg.hasDerivWithinAt.congr_of_mem _ (by simp)
      intro y hy
      have hya : a ≤ y := hy
      by_cases hy' : y ≤ a
      · have he : y = a := le_antisymm hy' hya
        simpa only [he, if_pos le_rfl] using hval
      · simp only [if_neg hy']
    rw [← hder rfl] at hr
    simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hl.union hr
  · rw [if_neg (not_le.mpr hgt)]
    apply hg.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hgt] with y hy
    have hy' : a < y := hy
    simp only [if_neg (not_le.mpr hy')]

end LpSelfSimilar.Analysis
