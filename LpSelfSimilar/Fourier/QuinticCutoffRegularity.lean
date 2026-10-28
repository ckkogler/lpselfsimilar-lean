module

public import LpSelfSimilar.Fourier.QuinticCutoffInversion
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Support

@[expose] public section

/-!
# Integrable amplitudes and derivatives for scaled quintic smoothing

The explicit cutoff slope is continuous, so the cutoff is C1. Its compact
support persists after nonzero scaling and multiplication by any amplitude.
For a C1 amplitude, both the product and its actual derivative are integrable.
-/

open MeasureTheory Set

namespace LpSelfSimilar.Fourier

/-- The actual cutoff is C1, including its transition endpoints. -/
theorem contDiff_one_quinticFourierCutoff {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 1 (quinticFourierCutoff ε) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (hasDerivAt_quinticFourierCutoff ε x).differentiableAt, ?_⟩
  have he : deriv (quinticFourierCutoff ε) = quinticFourierCutoffSlope ε :=
    funext (fun x => (hasDerivAt_quinticFourierCutoff ε x).deriv)
  rw [he]
  exact continuous_quinticFourierCutoffSlope hε.ne'

/-- The scaled cutoff confines every amplitude to an explicit compact interval. -/
theorem hasCompactSupport_scaled_quinticCutoff_mul {ε r : ℝ}
    (hε : 0 < ε) (hr : 0 < r) (P : ℝ → ℂ) :
    HasCompactSupport (fun ξ => (quinticFourierCutoff ε (r * ξ) : ℂ) * P ξ) := by
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact (Icc (-((1 + ε) / r)) ((1 + ε) / r)))
  intro ξ hξ
  have habs : (1 + ε) / r ≤ |ξ| := by
    by_contra hn
    have hlt := abs_lt.mp (lt_of_not_ge hn)
    exact hξ ⟨hlt.1.le, hlt.2.le⟩
  have harg : 1 + ε ≤ |r * ξ| := by
    rw [abs_mul, abs_of_pos hr]
    exact (div_le_iff₀ hr).mp habs |>.trans_eq (mul_comm _ _)
  rw [quinticFourierCutoff_eq_zero hε harg, Complex.ofReal_zero, zero_mul]

/-- A C1 multiplier gives an integrable amplitude and integrable actual derivative. -/
theorem integrable_scaled_quinticCutoff_mul_and_deriv {ε r : ℝ}
    (hε : 0 < ε) (hr : 0 < r) {P : ℝ → ℂ} (hP : ContDiff ℝ 1 P) :
    Integrable (fun ξ => (quinticFourierCutoff ε (r * ξ) : ℂ) * P ξ) ∧
      Integrable (deriv (fun ξ => (quinticFourierCutoff ε (r * ξ) : ℂ) * P ξ)) := by
  have hq : ContDiff ℝ 1 (fun ξ => (quinticFourierCutoff ε (r * ξ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_one_quinticFourierCutoff hε).comp (by fun_prop))
  have hf := hq.mul hP
  have hs := hasCompactSupport_scaled_quinticCutoff_mul hε hr P
  exact ⟨hf.continuous.integrable_of_hasCompactSupport hs,
    hf.continuous_deriv_one.integrable_of_hasCompactSupport hs.deriv⟩

end LpSelfSimilar.Fourier
