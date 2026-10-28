module

public import LpSelfSimilar.Analysis.QuinticTransition

@[expose] public section

/-!
# The exact squared slope integral of the quintic transition

An explicit polynomial antiderivative gives 10/7. This is the source of the
exact 10/(7*epsilon) whole-line cutoff derivative energy after both transition
bands and their Jacobians are included.
-/

open MeasureTheory

namespace LpSelfSimilar.Analysis

/-- The transition slope has squared integral exactly ten sevenths. -/
theorem integral_sq_quinticTransitionSlope :
    (∫ u in (0 : ℝ)..1, quinticTransitionSlope u ^ 2) = 10 / 7 := by
  have hd (u : ℝ) :
      HasDerivAt (fun v : ℝ => 180 * v ^ 5 - 600 * v ^ 6 +
        (5400 / 7) * v ^ 7 - 450 * v ^ 8 + 100 * v ^ 9)
        (quinticTransitionSlope u ^ 2) u := by
    convert! ((((((hasDerivAt_id u).pow 5).const_mul 180).sub
      (((hasDerivAt_id u).pow 6).const_mul 600)).add
      (((hasDerivAt_id u).pow 7).const_mul (5400 / 7))).sub
      (((hasDerivAt_id u).pow 8).const_mul 450)).add
      (((hasDerivAt_id u).pow 9).const_mul 100) using 1 <;>
      simp only [quinticTransitionSlope, Pi.pow_apply, id_eq] <;> ring
  have hi : IntervalIntegrable (fun u => quinticTransitionSlope u ^ 2) volume 0 1 :=
    (show Continuous (fun u => quinticTransitionSlope u ^ 2) by
      unfold quinticTransitionSlope; fun_prop).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u hu => hd u) hi
  norm_num at h
  exact h

end LpSelfSimilar.Analysis
