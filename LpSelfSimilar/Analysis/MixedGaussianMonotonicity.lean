module

public import LpSelfSimilar.Analysis.MixedGaussianTail
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-!
# Monotonicity of the mixed inverse-scale Gaussian tail

The logarithm has derivative
(1/2 - x - x/(2*sqrt(2*x)))/x^2. On the prescribed interval the final
numerator cost is at most 1/40. This proves the supporting monotonicity
claim directly, separately from the pure-exponential majorant used in
the already proved numerical tail estimate.
-/

open Set

namespace LpSelfSimilar.Analysis

/-- The exact mixed Gaussian tail is monotone on the full positive interval through 1/250. -/
theorem monotoneOn_mixed_gaussian_tail :
    MonotoneOn (fun x : ℝ => x⁻¹ * Real.exp (-(1 / 2 : ℝ) / x + 1 / Real.sqrt (2 * x)))
      (Ioc 0 (1 / 250)) := by
  let g : ℝ → ℝ := fun x => -Real.log x - (1 / 2 : ℝ) * x⁻¹ + (Real.sqrt (2 * x))⁻¹
  have hd (x : ℝ) (hx : 0 < x) :
      HasDerivAt g ((1 / 2 - x - x / (2 * Real.sqrt (2 * x))) / x ^ 2) x := by
    have hx2 : 2 * x ≠ 0 := by positivity
    have hs : Real.sqrt (2 * x) ≠ 0 := (Real.sqrt_pos.mpr (by positivity : 0 < 2 * x)).ne'
    have hsq := Real.sq_sqrt (by positivity : 0 ≤ 2 * x)
    have hroot := (Real.hasDerivAt_sqrt hx2).comp x ((hasDerivAt_id x).const_mul 2)
    convert! (((Real.hasDerivAt_log hx.ne').neg).sub
      (((hasDerivAt_id x).inv hx.ne').const_mul (1 / 2 : ℝ))).add (hroot.inv hs) using 1
    simp only [id_eq, Function.comp_apply]
    field_simp
    rw [hsq]
    ring_nf
    simp only [show x * 2 = 2 * x by ring]
    rw [show Real.sqrt (2 * x) ^ 3 = (2 * x) * Real.sqrt (2 * x) by rw [pow_succ, hsq]]
    ring
  have hg : MonotoneOn g (Ioc 0 (1 / 250)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioc 0 (1 / 250))
    · intro x hx
      exact (hd x hx.1).continuousAt.continuousWithinAt
    · intro x hx
      exact (hd x (interior_subset hx).1).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Ioc 0 (1 / 250) := interior_subset hx
      rw [(hd x hx'.1).deriv]
      apply div_nonneg
      · have hc := mul_le_mul_of_nonneg_left
          (inv_sqrt_twice_le_one_div_twenty_mul hx'.1 hx'.2) (hx'.1.le)
        have hcost : x / (2 * Real.sqrt (2 * x)) ≤ 1 / 40 := by
          have he : x * (1 / (20 * x)) = 1 / 20 := by field_simp [hx'.1.ne']
          rw [he] at hc
          have heq : x / (2 * Real.sqrt (2 * x)) = (x * (1 / Real.sqrt (2 * x))) / 2 := by ring
          rw [heq]
          linarith
        linarith [hx'.2]
      · positivity
  have he (x : ℝ) (hx : 0 < x) :
      x⁻¹ * Real.exp (-(1 / 2 : ℝ) / x + 1 / Real.sqrt (2 * x)) = Real.exp (g x) := by
    rw [show x⁻¹ = Real.exp (-Real.log x) by rw [Real.exp_neg, Real.exp_log hx],
      ← Real.exp_add]
    congr 1
    dsimp only [g]
    simp only [one_div, div_eq_mul_inv]
    ring
  intro x hx y hy hxy
  dsimp only
  rw [he x hx.1, he y hy.1]
  exact Real.exp_le_exp.mpr (hg hx hy hxy)

end LpSelfSimilar.Analysis
