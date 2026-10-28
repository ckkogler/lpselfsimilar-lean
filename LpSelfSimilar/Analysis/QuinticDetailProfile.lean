module

public import LpSelfSimilar.Analysis.QuinticTransitionIntegrals

@[expose] public section

/-!
# The detail profile on one transition interval

The positive-band multiplier is an affine rescaling of `quinticDetailProfile`.
Its mass is exactly one, since the absolute quintic slope has mass one and first
moment one half. Bounds on its next derivatives retain the constants needed
after rescaling both transition bands.
-/

open Set MeasureTheory

namespace LpSelfSimilar.Analysis

/-- The numerator of the detail multiplier in transition coordinates. -/
noncomputable def quinticDetailProfile (ε u : ℝ) : ℝ :=
  -(1 - ε + 2 * ε * u) * quinticTransitionSlope u

/-- First derivative of the transition-coordinate detail profile. -/
noncomputable def quinticDetailProfileSlope (ε u : ℝ) : ℝ :=
  -2 * ε * quinticTransitionSlope u -
    (1 - ε + 2 * ε * u) * quinticTransitionCurvature u

/-- Second derivative of the transition-coordinate detail profile. -/
noncomputable def quinticDetailProfileCurvature (ε u : ℝ) : ℝ :=
  -4 * ε * quinticTransitionCurvature u -
    (1 - ε + 2 * ε * u) * quinticTransitionThird u

/-- The profile slope is its actual derivative. -/
theorem hasDerivAt_quinticDetailProfile (ε u : ℝ) :
    HasDerivAt (quinticDetailProfile ε) (quinticDetailProfileSlope ε u) u := by
  convert! (((hasDerivAt_id u).const_mul (2 * ε)).const_add (1 - ε)).neg.mul
    (hasDerivAt_quinticTransitionSlope u) using 1 <;>
    simp only [quinticDetailProfile, quinticDetailProfileSlope, id_eq, Pi.neg_apply] <;> ring

/-- The profile curvature is its actual second derivative. -/
theorem hasDerivAt_quinticDetailProfileSlope (ε u : ℝ) :
    HasDerivAt (quinticDetailProfileSlope ε) (quinticDetailProfileCurvature ε u) u := by
  convert! ((hasDerivAt_quinticTransitionSlope u).const_mul (-2 * ε)).sub
    ((((hasDerivAt_id u).const_mul (2 * ε)).const_add (1 - ε)).mul
      (hasDerivAt_quinticTransitionCurvature u)) using 1 <;>
    simp only [quinticDetailProfileSlope, quinticDetailProfileCurvature, id_eq] <;> ring

/-- Both the profile and its first derivative vanish at both endpoints. -/
theorem quinticDetailProfile_endpoints (ε : ℝ) :
    quinticDetailProfile ε 0 = 0 ∧ quinticDetailProfile ε 1 = 0 ∧
    quinticDetailProfileSlope ε 0 = 0 ∧ quinticDetailProfileSlope ε 1 = 0 := by
  norm_num [quinticDetailProfile, quinticDetailProfileSlope,
    quinticTransitionSlope, quinticTransitionCurvature]

/-- The affine spatial coordinate is nonnegative and at most the outer endpoint. -/
theorem quinticDetailProfile_coordinate_bounds {ε u : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hu : u ∈ Icc 0 1) :
    0 ≤ 1 - ε + 2 * ε * u ∧ 1 - ε + 2 * ε * u ≤ 1 + ε := by
  constructor <;> nlinarith [mul_nonneg hε0 hu.1,
    mul_nonneg hε0 (sub_nonneg.mpr hu.2)]

/-- The detail profile is nonnegative on the transition interval. -/
theorem quinticDetailProfile_nonneg {ε u : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hu : u ∈ Icc 0 1) :
    0 ≤ quinticDetailProfile ε u := by
  unfold quinticDetailProfile
  exact mul_nonneg_of_nonpos_of_nonpos
    (neg_nonpos.mpr (quinticDetailProfile_coordinate_bounds hε0 hε1 hu).1)
    (quinticTransitionSlope_nonpos u)

/-- The integral of the profile is one, independent of the band width. -/
theorem integral_quinticDetailProfile (ε : ℝ) :
    (∫ u in (0 : ℝ)..1, quinticDetailProfile ε u) = 1 := by
  have he : quinticDetailProfile ε = fun u ↦
      (1 - ε) * |quinticTransitionSlope u| +
        (2 * ε) * (u * |quinticTransitionSlope u|) := by
    funext u
    rw [abs_of_nonpos (quinticTransitionSlope_nonpos u)]
    unfold quinticDetailProfile
    ring
  have hi : IntervalIntegrable (fun u ↦ |quinticTransitionSlope u|) volume 0 1 :=
    (show Continuous (fun u ↦ |quinticTransitionSlope u|) by
      unfold quinticTransitionSlope; fun_prop).intervalIntegrable _ _
  have hj : IntervalIntegrable (fun u ↦ u * |quinticTransitionSlope u|) volume 0 1 :=
    (show Continuous (fun u ↦ u * |quinticTransitionSlope u|) by
      unfold quinticTransitionSlope; fun_prop).intervalIntegrable _ _
  rw [he, intervalIntegral.integral_add (hi.const_mul _) (hj.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_abs_quinticTransitionSlope, integral_mul_abs_quinticTransitionSlope]
  ring

/-- The absolute profile mass is exactly one. -/
theorem integral_abs_quinticDetailProfile {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (∫ u in (0 : ℝ)..1, |quinticDetailProfile ε u|) = 1 := by
  calc
    _ = ∫ u in (0 : ℝ)..1, quinticDetailProfile ε u := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
      exact abs_of_nonneg (quinticDetailProfile_nonneg hε0 hε1 hu)
    _ = 1 := integral_quinticDetailProfile ε

/-- A pointwise majorant for the absolute profile slope. -/
theorem abs_quinticDetailProfileSlope_le {ε u : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hu : u ∈ Icc 0 1) :
    |quinticDetailProfileSlope ε u| ≤
      2 * ε * |quinticTransitionSlope u| + (1 + ε) * |quinticTransitionCurvature u| := by
  have ha := quinticDetailProfile_coordinate_bounds hε0 hε1 hu
  calc
    _ ≤ |-2 * ε * quinticTransitionSlope u| +
        |(1 - ε + 2 * ε * u) * quinticTransitionCurvature u| := abs_sub _ _
    _ = 2 * ε * |quinticTransitionSlope u| +
        (1 - ε + 2 * ε * u) * |quinticTransitionCurvature u| := by
      norm_num [abs_mul, abs_of_nonneg hε0, abs_of_nonneg ha.1]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right ha.2 (abs_nonneg _))

/-- A pointwise majorant for the absolute profile curvature. -/
theorem abs_quinticDetailProfileCurvature_le {ε u : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hu : u ∈ Icc 0 1) :
    |quinticDetailProfileCurvature ε u| ≤
      4 * ε * |quinticTransitionCurvature u| + (1 + ε) * |quinticTransitionThird u| := by
  have ha := quinticDetailProfile_coordinate_bounds hε0 hε1 hu
  calc
    _ ≤ |-4 * ε * quinticTransitionCurvature u| +
        |(1 - ε + 2 * ε * u) * quinticTransitionThird u| := abs_sub _ _
    _ = 4 * ε * |quinticTransitionCurvature u| +
        (1 - ε + 2 * ε * u) * |quinticTransitionThird u| := by
      norm_num [abs_mul, abs_of_nonneg hε0, abs_of_nonneg ha.1]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right ha.2 (abs_nonneg _))

/-- The profile slope's absolute integral retains the constant needed for seven. -/
theorem integral_abs_quinticDetailProfileSlope_le {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (∫ u in (0 : ℝ)..1, |quinticDetailProfileSlope ε u|) ≤ 6 + 8 * ε := by
  have hi : IntervalIntegrable (fun u ↦ |quinticDetailProfileSlope ε u|) volume 0 1 :=
    (show Continuous (fun u ↦ |quinticDetailProfileSlope ε u|) by
      unfold quinticDetailProfileSlope quinticTransitionSlope quinticTransitionCurvature
      fun_prop).intervalIntegrable _ _
  have hs : IntervalIntegrable (fun u ↦ |quinticTransitionSlope u|) volume 0 1 :=
    (show Continuous (fun u ↦ |quinticTransitionSlope u|) by
      unfold quinticTransitionSlope; fun_prop).intervalIntegrable _ _
  have hc : IntervalIntegrable (fun u ↦ |quinticTransitionCurvature u|) volume 0 1 :=
    (show Continuous (fun u ↦ |quinticTransitionCurvature u|) by
      unfold quinticTransitionCurvature; fun_prop).intervalIntegrable _ _
  have h := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hi
    ((hs.const_mul (2 * ε)).add (hc.const_mul (1 + ε)))
    (fun u hu ↦ abs_quinticDetailProfileSlope_le hε0 hε1 hu)
  rw [intervalIntegral.integral_add (hs.const_mul _) (hc.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_abs_quinticTransitionSlope] at h
  nlinarith [mul_le_mul_of_nonneg_left integral_abs_quinticTransitionCurvature_le
    (show 0 ≤ 1 + ε by linarith)]

/-- The profile curvature's absolute integral retains the constant needed for thirty-two. -/
theorem integral_abs_quinticDetailProfileCurvature_le {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (∫ u in (0 : ℝ)..1, |quinticDetailProfileCurvature ε u|) ≤ 60 + 84 * ε := by
  have hi : IntervalIntegrable (fun u ↦ |quinticDetailProfileCurvature ε u|) volume 0 1 :=
    (show Continuous (fun u ↦ |quinticDetailProfileCurvature ε u|) by
      unfold quinticDetailProfileCurvature quinticTransitionCurvature quinticTransitionThird
      fun_prop).intervalIntegrable _ _
  have hc : IntervalIntegrable (fun u ↦ |quinticTransitionCurvature u|) volume 0 1 :=
    (show Continuous (fun u ↦ |quinticTransitionCurvature u|) by
      unfold quinticTransitionCurvature; fun_prop).intervalIntegrable _ _
  have ht : IntervalIntegrable (fun u ↦ |quinticTransitionThird u|) volume 0 1 :=
    (show Continuous (fun u ↦ |quinticTransitionThird u|) by
      unfold quinticTransitionThird; fun_prop).intervalIntegrable _ _
  have h := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hi
    ((hc.const_mul (4 * ε)).add (ht.const_mul (1 + ε)))
    (fun u hu ↦ abs_quinticDetailProfileCurvature_le hε0 hε1 hu)
  rw [intervalIntegral.integral_add (hc.const_mul _) (ht.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
  nlinarith [mul_le_mul_of_nonneg_left integral_abs_quinticTransitionCurvature_le
    (show 0 ≤ 4 * ε by positivity),
    mul_le_mul_of_nonneg_left integral_abs_quinticTransitionThird_le
      (show 0 ≤ 1 + ε by linarith)]

end LpSelfSimilar.Analysis
