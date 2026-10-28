module

public import LpSelfSimilar.Analysis.ClampedQuintic
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

/-!
# The even quintic Fourier cutoff and its detail multiplier

Two clamped transitions give an even cutoff without introducing an absolute-value
singularity at the origin. Their endpoint matching supplies its first two actual
derivatives. The detail multiplier is defined by `-x*deriv phiHat x`, exactly as
required for differentiation of the smoothing scale.
-/

open Set
open LpSelfSimilar.Analysis

namespace LpSelfSimilar.Fourier

/-- Affine coordinate on the positive transition band. -/
noncomputable def quinticBandCoordinate (ε x : ℝ) : ℝ := (x - (1 - ε)) / (2 * ε)

/-- The even cutoff, with two clamped quintic transitions. -/
noncomputable def quinticFourierCutoff (ε x : ℝ) : ℝ :=
  clampedQuintic (quinticBandCoordinate ε x) +
    clampedQuintic (quinticBandCoordinate ε (-x)) - 1

/-- Explicit first derivative of the even cutoff. -/
noncomputable def quinticFourierCutoffSlope (ε x : ℝ) : ℝ :=
  (clampedQuinticSlope (quinticBandCoordinate ε x) -
    clampedQuinticSlope (quinticBandCoordinate ε (-x))) / (2 * ε)

/-- Explicit second derivative of the even cutoff. -/
noncomputable def quinticFourierCutoffCurvature (ε x : ℝ) : ℝ :=
  (clampedQuinticCurvature (quinticBandCoordinate ε x) +
    clampedQuinticCurvature (quinticBandCoordinate ε (-x))) / (2 * ε) ^ 2

/-- The Fourier detail multiplier defined from the actual derivative of the cutoff. -/
noncomputable def quinticFourierDetail (ε x : ℝ) : ℝ :=
  -x * deriv (quinticFourierCutoff ε) x

/-- Explicit first derivative of the detail multiplier. -/
noncomputable def quinticFourierDetailSlope (ε x : ℝ) : ℝ :=
  -quinticFourierCutoffSlope ε x - x * quinticFourierCutoffCurvature ε x

/-- Derivative of the affine band coordinate. -/
theorem hasDerivAt_quinticBandCoordinate (ε x : ℝ) :
    HasDerivAt (quinticBandCoordinate ε) (1 / (2 * ε)) x := by
  unfold quinticBandCoordinate
  convert! ((hasDerivAt_id x).sub_const (1 - ε)).div_const (2 * ε) using 1 <;>
    simp only [id_eq]

/-- The explicit cutoff slope is its actual derivative. -/
theorem hasDerivAt_quinticFourierCutoff (ε x : ℝ) :
    HasDerivAt (quinticFourierCutoff ε) (quinticFourierCutoffSlope ε x) x := by
  have hp := (hasDerivAt_clampedQuintic (quinticBandCoordinate ε x)).comp x
    (hasDerivAt_quinticBandCoordinate ε x)
  have hn := (hasDerivAt_clampedQuintic (quinticBandCoordinate ε (-x))).comp x
    ((hasDerivAt_quinticBandCoordinate ε (-x)).comp x (hasDerivAt_id x).neg)
  convert! (hp.add hn).sub_const 1 using 1 <;>
    simp only [quinticFourierCutoff, quinticFourierCutoffSlope, Function.comp_apply, id_eq] <;> ring

/-- The explicit cutoff curvature is the actual derivative of its slope. -/
theorem hasDerivAt_quinticFourierCutoffSlope {ε : ℝ} (hε : ε ≠ 0) (x : ℝ) :
    HasDerivAt (quinticFourierCutoffSlope ε) (quinticFourierCutoffCurvature ε x) x := by
  have hp := (hasDerivAt_clampedQuinticSlope (quinticBandCoordinate ε x)).comp x
    (hasDerivAt_quinticBandCoordinate ε x)
  have hn := (hasDerivAt_clampedQuinticSlope (quinticBandCoordinate ε (-x))).comp x
    ((hasDerivAt_quinticBandCoordinate ε (-x)).comp x (hasDerivAt_id x).neg)
  convert! (hp.sub hn).div_const (2 * ε) using 1 <;>
    simp only [quinticFourierCutoffSlope, quinticFourierCutoffCurvature, Function.comp_apply, id_eq]
  field_simp
  <;> ring

/-- The detail multiplier has its explicit first derivative everywhere, including joins. -/
theorem hasDerivAt_quinticFourierDetail {ε : ℝ} (hε : ε ≠ 0) (x : ℝ) :
    HasDerivAt (quinticFourierDetail ε) (quinticFourierDetailSlope ε x) x := by
  have he : deriv (quinticFourierCutoff ε) = quinticFourierCutoffSlope ε :=
    funext (fun y ↦ (hasDerivAt_quinticFourierCutoff ε y).deriv)
  unfold quinticFourierDetail
  rw [he]
  convert! (hasDerivAt_id x).neg.mul (hasDerivAt_quinticFourierCutoffSlope hε x) using 1 <;>
    simp only [quinticFourierDetailSlope, Pi.neg_apply, id_eq] <;> ring

/-- The cutoff curvature is continuous. -/
theorem continuous_quinticFourierCutoffCurvature (ε : ℝ) :
    Continuous (quinticFourierCutoffCurvature ε) := by
  unfold quinticFourierCutoffCurvature
  apply Continuous.div_const
  exact (continuous_clampedQuinticCurvature.comp (by unfold quinticBandCoordinate; fun_prop)).add
    (continuous_clampedQuinticCurvature.comp (by unfold quinticBandCoordinate; fun_prop))

/-- The cutoff is even by construction. -/
theorem quinticFourierCutoff_neg (ε x : ℝ) :
    quinticFourierCutoff ε (-x) = quinticFourierCutoff ε x := by
  unfold quinticFourierCutoff
  rw [neg_neg, add_comm]

end LpSelfSimilar.Fourier
