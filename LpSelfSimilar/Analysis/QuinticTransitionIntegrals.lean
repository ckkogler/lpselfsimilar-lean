module

public import LpSelfSimilar.Analysis.QuinticTransition

@[expose] public section

/-!
# Exact transition mass and derivative integrals

The absolute slope has mass one and first moment one half. These exact identities
control the zeroth-order Fourier cutoff norm after affine rescaling. Rational
bounds on the next two derivatives provide its first and second norm estimates.
-/

open MeasureTheory Set

namespace LpSelfSimilar.Analysis

/-- The absolute slope of the transition has unit integral. -/
theorem integral_abs_quinticTransitionSlope :
    (∫ u in (0 : ℝ)..1, |quinticTransitionSlope u|) = 1 := by
  have he : (fun u ↦ |quinticTransitionSlope u|) = fun u ↦ -quinticTransitionSlope u :=
    funext (fun u ↦ abs_of_nonpos (quinticTransitionSlope_nonpos u))
  rw [he, intervalIntegral.integral_neg]
  have hi : IntervalIntegrable quinticTransitionSlope volume 0 1 :=
    (show Continuous quinticTransitionSlope by unfold quinticTransitionSlope; fun_prop).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu ↦ hasDerivAt_quinticTransition u) hi]
  norm_num [quinticTransition]

/-- The absolute slope's first moment is exactly one half. -/
theorem integral_mul_abs_quinticTransitionSlope :
    (∫ u in (0 : ℝ)..1, u * |quinticTransitionSlope u|) = 1 / 2 := by
  have hd (u : ℝ) :
      HasDerivAt (fun v : ℝ ↦ (15 / 2) * v ^ 4 - 12 * v ^ 5 + 5 * v ^ 6)
        (u * |quinticTransitionSlope u|) u := by
    rw [abs_of_nonpos (quinticTransitionSlope_nonpos u)]
    convert! ((((hasDerivAt_id u).pow 4).const_mul (15 / 2)).sub
      (((hasDerivAt_id u).pow 5).const_mul 12)).add
      (((hasDerivAt_id u).pow 6).const_mul 5) using 1 <;>
      simp only [quinticTransitionSlope, Pi.pow_apply, id_eq] <;> ring
  have hi : IntervalIntegrable (fun u ↦ u * |quinticTransitionSlope u|) volume 0 1 :=
    (show Continuous (fun u : ℝ ↦ u * |quinticTransitionSlope u|) by
      unfold quinticTransitionSlope; fun_prop).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u hu ↦ hd u) hi
  norm_num at h
  exact h

/-- The curvature's absolute integral has the sufficient rational bound six. -/
theorem integral_abs_quinticTransitionCurvature_le :
    (∫ u in (0 : ℝ)..1, |quinticTransitionCurvature u|) ≤ 6 := by
  have hi : IntervalIntegrable (fun u ↦ |quinticTransitionCurvature u|) volume 0 1 :=
    (show Continuous (fun u : ℝ ↦ |quinticTransitionCurvature u|) by
      unfold quinticTransitionCurvature; fun_prop).intervalIntegrable _ _
  have h := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hi
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ (6 : ℝ)) volume 0 1)
    (fun u hu ↦ abs_quinticTransitionCurvature_le hu)
  simpa using h

/-- The third derivative's absolute integral is at most sixty. -/
theorem integral_abs_quinticTransitionThird_le :
    (∫ u in (0 : ℝ)..1, |quinticTransitionThird u|) ≤ 60 := by
  have hi : IntervalIntegrable (fun u ↦ |quinticTransitionThird u|) volume 0 1 :=
    (show Continuous (fun u : ℝ ↦ |quinticTransitionThird u|) by
      unfold quinticTransitionThird; fun_prop).intervalIntegrable _ _
  have h := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hi
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ (60 : ℝ)) volume 0 1)
    (fun u hu ↦ abs_quinticTransitionThird_le hu)
  simpa using h

end LpSelfSimilar.Analysis
