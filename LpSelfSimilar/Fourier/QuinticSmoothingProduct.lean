module

public import LpSelfSimilar.Fourier.QuinticCutoffRegularity
public import LpSelfSimilar.Fourier.CompactInverseTransform

@[expose] public section

/-!
# Smooth amplitudes multiplied by the quintic smoothing cutoff

The explicitly continuous curvature proves that the cutoff is C2. Hence any
C2 amplitude times a scaled cutoff has an integrable inverse. The actual
first derivative is recorded with its scale factor, for later splitting into
a cutoff-slope term and a differentiated-amplitude term.
-/

open MeasureTheory
open scoped ContDiff

namespace LpSelfSimilar.Fourier

/-- The explicit cutoff slope is C1 because its actual derivative is the continuous curvature. -/
theorem contDiff_one_quinticFourierCutoffSlope {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 1 (quinticFourierCutoffSlope ε) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (hasDerivAt_quinticFourierCutoffSlope hε.ne' x).differentiableAt, ?_⟩
  have he : deriv (quinticFourierCutoffSlope ε) = quinticFourierCutoffCurvature ε :=
    funext (fun x => (hasDerivAt_quinticFourierCutoffSlope hε.ne' x).deriv)
  rw [he]
  exact continuous_quinticFourierCutoffCurvature ε

/-- The actual cutoff is C2 across all transition joins. -/
theorem contDiff_two_quinticFourierCutoff {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 2 (quinticFourierCutoff ε) := by
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun x => (hasDerivAt_quinticFourierCutoff ε x).differentiableAt, by simp, ?_⟩
  have he : deriv (quinticFourierCutoff ε) = quinticFourierCutoffSlope ε :=
    funext (fun x => (hasDerivAt_quinticFourierCutoff ε x).deriv)
  rw [he]
  exact contDiff_one_quinticFourierCutoffSlope hε

/-- Every scaled quintic cutoff times a C2 amplitude has an integrable actual inverse. -/
theorem integrable_angularInverseFourier_scaled_quinticCutoff_mul {ε r : ℝ}
    (hε : 0 < ε) (hr : 0 < r) {P : ℝ → ℂ} (hP : ContDiff ℝ 2 P) :
    Integrable (angularInverseFourier (fun ξ => (quinticFourierCutoff ε (r * ξ) : ℂ) * P ξ)) := by
  have hq : ContDiff ℝ 2 (fun ξ => (quinticFourierCutoff ε (r * ξ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_two_quinticFourierCutoff hε).comp (by fun_prop))
  exact (angularInverseFourier_compact_C2_L1_bound (hq.mul hP)
    (hasCompactSupport_scaled_quinticCutoff_mul hε hr P)).1

/-- The actual product derivative includes the frequency-scale factor on the cutoff slope. -/
theorem hasDerivAt_scaled_quinticCutoff_mul (ε r u : ℝ) {P : ℝ → ℂ} {P₁ : ℂ}
    (hP : HasDerivAt P P₁ u) :
    HasDerivAt (fun ξ => (quinticFourierCutoff ε (r * ξ) : ℂ) * P ξ)
      ((r : ℂ) * (quinticFourierCutoffSlope ε (r * u) : ℂ) * P u +
        (quinticFourierCutoff ε (r * u) : ℂ) * P₁) u := by
  have hq := ((hasDerivAt_quinticFourierCutoff ε (r * u)).comp u
    ((hasDerivAt_id u).const_mul r)).ofReal_comp
  convert! hq.mul hP using 1 <;>
    simp only [Function.comp_def, id_eq, mul_one, Complex.ofReal_mul] <;> ring

end LpSelfSimilar.Fourier
