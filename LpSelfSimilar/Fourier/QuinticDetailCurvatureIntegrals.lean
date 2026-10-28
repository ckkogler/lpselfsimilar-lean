module

public import LpSelfSimilar.Fourier.QuinticDetailIntegrals
public import LpSelfSimilar.Fourier.QuinticDetailBandCurvature

@[expose] public section

/-!
# All three detail integral bounds with actual derivatives

Reflection preserves Lebesgue null sets, so both band slopes may be
differentiated simultaneously almost everywhere. This gives the actual second
derivative, its integrability, and the precise constant thirty-two without
assuming second differentiability at the four band endpoints.
-/

open MeasureTheory

namespace LpSelfSimilar.Fourier

/-- The even almost-everywhere curvature of the Fourier detail multiplier. -/
noncomputable def quinticFourierDetailCurvature (ε x : ℝ) : ℝ :=
  quinticDetailBandCurvature ε x + quinticDetailBandCurvature ε (-x)

/-- The indicated curvature is the actual derivative of the actual first derivative a.e. -/
theorem ae_hasDerivAt_deriv_quinticFourierDetail {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x, HasDerivAt (deriv (quinticFourierDetail ε)) (quinticFourierDetailCurvature ε x) x := by
  have hp := ae_hasDerivAt_quinticDetailBandSlope hε
  have hn := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hp
  have he : deriv (quinticFourierDetail ε) = fun x ↦
      quinticDetailBandSlope ε x - quinticDetailBandSlope ε (-x) := by
    funext x
    rw [(hasDerivAt_quinticFourierDetail (ne_of_gt hε) x).deriv,
      quinticFourierDetailSlope_eq_bands]
  rw [he]
  filter_upwards [hp, hn] with x hx hnx
  convert! hx.sub (hnx.comp x (hasDerivAt_id x).neg) using 1 <;>
    simp only [quinticFourierDetailCurvature, Pi.neg_apply, Function.comp_apply, id_eq] <;> ring

/-- Equality of the actual second derivative with the reflected curvature formula almost everywhere. -/
theorem ae_deriv_deriv_quinticFourierDetail {ε : ℝ} (hε : 0 < ε) :
    deriv (deriv (quinticFourierDetail ε)) =ᵐ[volume] quinticFourierDetailCurvature ε := by
  filter_upwards [ae_hasDerivAt_deriv_quinticFourierDetail hε] with x hx
  exact hx.deriv

/-- The reflected curvature formula is integrable. -/
theorem integrable_quinticFourierDetailCurvature (ε : ℝ) :
    Integrable (quinticFourierDetailCurvature ε) :=
  (integrable_quinticDetailBandCurvature ε).add (integrable_quinticDetailBandCurvature ε).comp_neg

/-- The actual second derivative of the detail multiplier is integrable. -/
theorem integrable_deriv_deriv_quinticFourierDetail {ε : ℝ} (hε : 0 < ε) :
    Integrable (deriv (deriv (quinticFourierDetail ε))) :=
  (integrable_quinticFourierDetailCurvature ε).congr
    (ae_deriv_deriv_quinticFourierDetail hε).symm

/-- The actual second derivative has the sufficient exact rescaled integral bound. -/
theorem integral_abs_deriv_deriv_quinticFourierDetail_le {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ x, |deriv (deriv (quinticFourierDetail ε)) x|) ≤ (30 + 42 * ε) / ε ^ 2 := by
  have he : (∫ x, |deriv (deriv (quinticFourierDetail ε)) x|) =
      ∫ x, |quinticFourierDetailCurvature ε x| := by
    apply integral_congr_ae
    filter_upwards [ae_deriv_deriv_quinticFourierDetail hε] with x hx
    rw [hx]
  rw [he]
  have hb (x : ℝ) : |quinticFourierDetailCurvature ε x| ≤
      |quinticDetailBandCurvature ε x| + |quinticDetailBandCurvature ε (-x)| := abs_add_le _ _
  have h := integral_mono (integrable_quinticFourierDetailCurvature ε).abs
    ((integrable_quinticDetailBandCurvature ε).abs.add
      (integrable_quinticDetailBandCurvature ε).abs.comp_neg) hb
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_quinticDetailBandCurvature ε).abs
    (integrable_quinticDetailBandCurvature ε).abs.comp_neg,
    integral_neg_eq_self (fun x ↦ |quinticDetailBandCurvature ε x|) volume] at h
  have hc := integral_abs_quinticDetailBandCurvature_le hε hε1
  have heq : (30 + 42 * ε) / ε ^ 2 = 2 * ((60 + 84 * ε) / (2 * ε) ^ 2) := by ring
  rw [heq]
  linarith

/-- All three numerical L1 bounds in (5.3), with actual first and second derivatives. -/
theorem quinticFourierDetail_integral_bounds {ε : ℝ} (hε : 0 < ε)
    (hεsmall : ε ≤ 1 / 100000) :
    (∫ x, |quinticFourierDetail ε x|) ≤ 21 / 10 ∧
      (∫ x, |deriv (quinticFourierDetail ε) x|) ≤ 7 / ε ∧
      (∫ x, |deriv (deriv (quinticFourierDetail ε)) x|) ≤ 32 / ε ^ 2 := by
  have hfirst := quinticFourierDetail_first_integral_bounds hε hεsmall
  refine ⟨hfirst.1, hfirst.2, ?_⟩
  exact (integral_abs_deriv_deriv_quinticFourierDetail_le hε (by linarith)).trans
    (div_le_div_of_nonneg_right (by linarith : 30 + 42 * ε ≤ 32) (sq_nonneg _))

end LpSelfSimilar.Fourier
