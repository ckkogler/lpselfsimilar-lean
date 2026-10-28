module

public import LpSelfSimilar.Gaussian.BinaryInformationIntegral
public import LpSelfSimilar.Analysis.TanhDerivative
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

/-!
# Dominated differentiation of binary Gaussian information

The information is first identified with an integral over a fixed standard
Gaussian. The derivative of log cosh is bounded by a linear function of the
noise on every amplitude ball. Its Gaussian integrability justifies exchanging
differentiation and integration, at every real amplitude including zero.
-/

open MeasureTheory ProbabilityTheory Real Filter Set
open LpSelfSimilar.Analysis
open scoped Topology

namespace LpSelfSimilar.Gaussian

/-- The fixed-noise logarithmic integral may be differentiated under the integral. -/
theorem hasDerivAt_binary_log_cosh_integral (u : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ x, log (cosh (t ^ 2 + t * x)) ∂gaussianReal 0 1)
      (∫ x, (2 * u + x) * tanh (u ^ 2 + u * x) ∂gaussianReal 0 1) u := by
  have htc : Continuous tanh :=
    continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_tanh x).continuousAt)
  have hi : Integrable (fun x : ℝ => x) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)
  have hF (t : ℝ) : Continuous (fun x : ℝ => log (cosh (t ^ 2 + t * x))) :=
    continuous_log_cosh.comp (continuous_const.add (continuous_const.mul continuous_id))
  have hF' (t : ℝ) : Continuous (fun x : ℝ => (2 * t + x) * tanh (t ^ 2 + t * x)) :=
    (continuous_const.add continuous_id).mul
      (htc.comp (continuous_const.add (continuous_const.mul continuous_id)))
  have hd (t x : ℝ) : HasDerivAt (fun s : ℝ => log (cosh (s ^ 2 + s * x)))
      ((2 * t + x) * tanh (t ^ 2 + t * x)) t := by
    convert! (hasDerivAt_log_cosh (t ^ 2 + t * x)).comp t
      (((hasDerivAt_id t).pow 2).add ((hasDerivAt_id t).mul_const x)) using 1 <;> simp only [id_eq] <;> ring
  have hbound : ∀ x t : ℝ, t ∈ Metric.ball u 1 →
      ‖(2 * t + x) * tanh (t ^ 2 + t * x)‖ ≤ 2 * (|u| + 1) + |x| := by
    intro x t ht
    have ht' : |t - u| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using ht
    have htu : |t| ≤ |u| + 1 := by
      have h := abs_add_le (t - u) u
      rw [sub_add_cancel] at h
      linarith
    rw [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ |2 * t + x| := mul_le_of_le_one_right (abs_nonneg _) (abs_tanh_lt_one _).le
      _ ≤ |2 * t| + |x| := abs_add_le _ _
      _ ≤ _ := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (F := fun t x : ℝ => log (cosh (t ^ 2 + t * x)))
    (F' := fun t x : ℝ => (2 * t + x) * tanh (t ^ 2 + t * x))
    (bound := fun x : ℝ => 2 * (|u| + 1) + |x|)
    (Metric.ball_mem_nhds u (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall (fun t => (hF t).aestronglyMeasurable))
    (integrable_log_cosh ((integrable_const (u ^ 2)).add (hi.const_mul u)))
    (hF' u).aestronglyMeasurable
    (ae_of_all _ (fun x t ht => hbound x t ht))
    ((integrable_const (2 * (|u| + 1))).add hi.abs)
    (ae_of_all _ (fun x t ht => hd t x))
  exact h.2

/-- Differentiability of the actual finite KL information, before the variance cancellation. -/
theorem hasDerivAt_binaryGaussianInformation_raw (u : ℝ) :
    HasDerivAt binaryGaussianInformation
      (2 * u - ∫ x, (2 * u + x) * tanh (u ^ 2 + u * x) ∂gaussianReal 0 1) u := by
  have he : binaryGaussianInformation =
      fun t : ℝ => t ^ 2 - ∫ x, log (cosh (t ^ 2 + t * x)) ∂gaussianReal 0 1 :=
    funext binaryGaussianInformation_eq_standard_integral
  rw [he]
  convert! ((hasDerivAt_id u).pow 2).sub (hasDerivAt_binary_log_cosh_integral u) using 1 <;> simp only [id_eq] <;> ring

end LpSelfSimilar.Gaussian
