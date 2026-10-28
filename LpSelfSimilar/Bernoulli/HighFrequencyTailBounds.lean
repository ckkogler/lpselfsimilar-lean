module

public import LpSelfSimilar.Bernoulli.FourierPrefixTail
public import LpSelfSimilar.Bernoulli.SmallAngleFourierDerivative
public import LpSelfSimilar.Bernoulli.ReservedTailFourier

@[expose] public section

/-!
# Tail Gaussian decay controls the complete characteristic function

The splitting index is fixed while differentiating the exact prefix-tail
identity. The prefix is then bounded by one and its finite coefficient sum;
the tail supplies Gaussian decay with derivative cost two. Adding these costs
before discarding the factor theta^n retains twice the full coefficient sum.
-/

open MeasureTheory
open scoped BigOperators

namespace LpSelfSimilar.Bernoulli

/-- Discarding a finite prefix retains the exact Gaussian decay from any small-angle tail. -/
theorem norm_charFun_scaled_convolution_le_tail_gaussian {θ a u : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (n : ℕ)
    (hA : |(a * θ ^ n) * u| < Real.pi / 2) :
    ‖charFun ((convolution θ).map (fun x => a * x)) u‖ ≤
      Real.exp (-(((a * θ ^ n) * u) ^ 2) / (2 * (1 - θ ^ 2))) := by
  have hθ : |θ| < 1 := by rwa [abs_of_nonneg hθ0]
  rw [charFun_scaled_convolution_prefix_tail hθ a u n, norm_mul]
  calc
    _ ≤ ‖charFun ((convolution θ).map (fun x => (a * θ ^ n) * x)) u‖ :=
      mul_le_of_le_one_left (norm_nonneg _) (norm_cosine_prefix_le_one a θ u n)
    _ ≤ _ := by
      rw [charFun_map_mul]
      exact norm_charFun_convolution_le_gaussian hθ0 hθ1 hA

/-- The complete derivative retains the tail exponential with twice the full coefficient sum. -/
theorem norm_deriv_charFun_scaled_convolution_le_tail_gaussian {θ a u : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (ha : 0 ≤ a) (n : ℕ)
    (hA : |(a * θ ^ n) * u| ≤ 101 / 100) :
    ‖deriv (charFun ((convolution θ).map (fun x => a * x))) u‖ ≤
      (2 * (a / (1 - θ))) *
        Real.exp (-(((a * θ ^ n) * u) ^ 2) / (2 * (1 - θ ^ 2))) := by
  let P : ℝ → ℂ := fun v => ∏ j : Fin n, (Real.cos ((a * θ ^ (j : ℕ)) * v) : ℂ)
  let T : ℝ → ℂ := charFun ((convolution θ).map (fun x => (a * θ ^ n) * x))
  let E : ℝ := Real.exp (-(((a * θ ^ n) * u) ^ 2) / (2 * (1 - θ ^ 2)))
  have hθ : |θ| < 1 := by rwa [abs_of_nonneg hθ0]
  have hP : ContDiff ℝ 1 P := by
    dsimp only [P]
    apply contDiff_prod
    intro j hj
    exact Complex.ofRealCLM.contDiff.comp
      (show ContDiff ℝ 1 (fun v : ℝ => Real.cos ((a * θ ^ (j : ℕ)) * v)) from by fun_prop)
  have hT : ContDiff ℝ 1 T := by
    apply contDiff_charFun (n := 1)
    simpa only [Nat.cast_one] using memLp_id_scaled_convolution hθ0 hθ1 (a * θ ^ n) 1
  have he : charFun ((convolution θ).map (fun x => a * x)) = fun v => P v * T v :=
    funext (fun v => charFun_scaled_convolution_prefix_tail hθ a v n)
  have hd : deriv (charFun ((convolution θ).map (fun x => a * x))) u =
      deriv P u * T u + P u * deriv T u := by
    rw [he]
    exact ((hP.differentiable (by norm_num)).differentiableAt.hasDerivAt.mul
      (hT.differentiable (by norm_num)).differentiableAt.hasDerivAt).deriv
  have hp : ‖P u‖ ≤ 1 := norm_cosine_prefix_le_one a θ u n
  have hdp : ‖deriv P u‖ ≤ a * (1 - θ ^ n) / (1 - θ) :=
    norm_deriv_cosine_prefix_le hθ0 hθ1 ha u n
  have ht : ‖T u‖ ≤ E := by
    dsimp only [T, E]
    rw [charFun_map_mul]
    exact norm_charFun_convolution_le_gaussian hθ0 hθ1 (by linarith [Real.pi_gt_d2])
  have hdt : ‖deriv T u‖ ≤ (2 * (a * θ ^ n / (1 - θ))) * E :=
    norm_deriv_charFun_scaled_convolution_le_half_gaussian hθ0 hθ1
      (mul_nonneg ha (pow_nonneg hθ0 _)) hA
  have hd0 : 0 < 1 - θ := sub_pos.mpr hθ1
  have hsum0 : 0 ≤ a * (1 - θ ^ n) / (1 - θ) := by
    exact div_nonneg (mul_nonneg ha (sub_nonneg.mpr (pow_le_one₀ hθ0 hθ1.le))) hd0.le
  have hc : a * (1 - θ ^ n) / (1 - θ) + 2 * (a * θ ^ n / (1 - θ)) ≤
      2 * (a / (1 - θ)) := by
    have hp := mul_le_of_le_one_right ha (pow_le_one₀ hθ0 hθ1.le : θ ^ n ≤ 1)
    apply (mul_le_mul_iff_left₀ hd0).mp
    field_simp
    nlinarith
  rw [hd]
  calc
    _ ≤ ‖deriv P u * T u‖ + ‖P u * deriv T u‖ := norm_add_le _ _
    _ ≤ (a * (1 - θ ^ n) / (1 - θ)) * E +
        (2 * (a * θ ^ n / (1 - θ))) * E := by
      rw [norm_mul, norm_mul]
      exact add_le_add (mul_le_mul hdp ht (norm_nonneg _) hsum0)
        ((mul_le_of_le_one_left (norm_nonneg _) hp).trans hdt)
    _ = (a * (1 - θ ^ n) / (1 - θ) + 2 * (a * θ ^ n / (1 - θ))) * E := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le

end LpSelfSimilar.Bernoulli
