module

public import LpSelfSimilar.Fourier.QuinticDetailBandIntegrals
public import LpSelfSimilar.Analysis.ZeroExtendedDerivative

@[expose] public section

/-!
# The second derivative of a detail band almost everywhere

An open-interval indicator records the curvature away from the joins. It is the
actual derivative of the globally continuous band slope almost everywhere. Its
integrability and exact scaling come from a polynomial on the bounded interval.
-/

open Set MeasureTheory
open LpSelfSimilar.Analysis

namespace LpSelfSimilar.Fourier

/-- The band curvature, with arbitrary zero values at the two exceptional endpoints. -/
noncomputable def quinticDetailBandCurvature (ε : ℝ) : ℝ → ℝ :=
  (Ioo (1 - ε) (1 + ε)).indicator
    (fun x ↦ quinticDetailProfileCurvature ε (quinticBandCoordinate ε x) / (2 * ε) ^ 3)

/-- Derivative of the rescaled slope profile before extension by zero. -/
theorem hasDerivAt_quinticDetailBandSlopeProfile {ε : ℝ} (hε : ε ≠ 0) (x : ℝ) :
    HasDerivAt (fun y ↦ quinticDetailProfileSlope ε (quinticBandCoordinate ε y) / (2 * ε) ^ 2)
      (quinticDetailProfileCurvature ε (quinticBandCoordinate ε x) / (2 * ε) ^ 3) x := by
  convert! ((hasDerivAt_quinticDetailProfileSlope ε (quinticBandCoordinate ε x)).comp x
    (hasDerivAt_quinticBandCoordinate ε x)).div_const ((2 * ε) ^ 2) using 1 <;> field_simp <;> ring

/-- The specified curvature is the actual derivative of the band slope almost everywhere. -/
theorem ae_hasDerivAt_quinticDetailBandSlope {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x, HasDerivAt (quinticDetailBandSlope ε) (quinticDetailBandCurvature ε x) x := by
  apply ae_hasDerivAt_of_eqOn_zero_off_Ioo
    (fun x hx ↦ quinticDetailBandSlope_eq_profile hε hx)
    (fun x hx ↦ (quinticDetailBand_eq_zero hε hx).2)
  intro x hx
  exact hasDerivAt_quinticDetailBandSlopeProfile (ne_of_gt hε) x

/-- The curvature vanishes off the open positive band, including endpoints. -/
theorem quinticDetailBandCurvature_eq_zero {ε x : ℝ}
    (hx : x ≤ 1 - ε ∨ 1 + ε ≤ x) : quinticDetailBandCurvature ε x = 0 := by
  apply indicator_of_notMem
  intro h
  rcases hx with hx | hx
  · exact (not_lt_of_ge hx) h.1
  · exact (not_lt_of_ge hx) h.2

/-- The curvature equals its rescaled polynomial throughout the open band. -/
theorem quinticDetailBandCurvature_eq_profile {ε x : ℝ}
    (hx : x ∈ Ioo (1 - ε) (1 + ε)) :
    quinticDetailBandCurvature ε x =
      quinticDetailProfileCurvature ε (quinticBandCoordinate ε x) / (2 * ε) ^ 3 :=
  indicator_of_mem hx _

/-- The indicated almost-everywhere curvature is integrable. -/
theorem integrable_quinticDetailBandCurvature (ε : ℝ) :
    Integrable (quinticDetailBandCurvature ε) := by
  have hc : Continuous (fun x ↦
      quinticDetailProfileCurvature ε (quinticBandCoordinate ε x) / (2 * ε) ^ 3) := by
    unfold quinticDetailProfileCurvature quinticTransitionCurvature
      quinticTransitionThird quinticBandCoordinate
    fun_prop
  exact (integrable_indicator_iff measurableSet_Ioo).mpr
    ((hc.integrableOn_Icc (μ := volume)).mono_set Ioo_subset_Icc_self)

/-- The curvature's absolute integral has its exact cubic rescaling factor. -/
theorem integral_abs_quinticDetailBandCurvature_eq {ε : ℝ} (hε : 0 < ε) :
    (∫ x, |quinticDetailBandCurvature ε x|) =
      (∫ u in (0 : ℝ)..1, |quinticDetailProfileCurvature ε u|) / (2 * ε) ^ 2 := by
  rw [integral_eq_interval_of_eq_zero_off_Ioo (a := 1 - ε) (b := 1 + ε)
    (fun x hx ↦ by rw [quinticDetailBandCurvature_eq_zero hx, abs_zero])]
  have he : (∫ x in (1 - ε)..(1 + ε), |quinticDetailBandCurvature ε x|) =
      ∫ x in (1 - ε)..(1 + ε),
        |quinticDetailProfileCurvature ε (quinticBandCoordinate ε x)| / (2 * ε) ^ 3 := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by linarith : 1 - ε ≤ 1 + ε)
    intro x hx
    dsimp only
    rw [quinticDetailBandCurvature_eq_profile hx, abs_div,
      abs_of_pos (by positivity : 0 < (2 * ε) ^ 3)]
  rw [he, intervalIntegral.integral_div,
    integral_comp_quinticBandCoordinate (ne_of_gt hε) (fun u ↦ |quinticDetailProfileCurvature ε u|)]
  field_simp
  <;> ring

/-- The sufficient bound for one band's absolute curvature integral. -/
theorem integral_abs_quinticDetailBandCurvature_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ x, |quinticDetailBandCurvature ε x|) ≤ (60 + 84 * ε) / (2 * ε) ^ 2 := by
  rw [integral_abs_quinticDetailBandCurvature_eq hε]
  exact div_le_div_of_nonneg_right
    (integral_abs_quinticDetailProfileCurvature_le hε.le hε1) (sq_nonneg _)

end LpSelfSimilar.Fourier
