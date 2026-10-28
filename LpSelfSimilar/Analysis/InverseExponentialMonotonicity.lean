module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic

@[expose] public section

/-!
# Monotonicity of inverse powers times an inverse-scale exponential

Taking logarithms reduces the derivative sign to a-p*x. This supplies all
pure inverse-power exponential comparisons in the Gaussian tail numerics.
The positive interval excludes the singular endpoint explicitly.
-/

open Set

namespace LpSelfSimilar.Analysis

/-- The inverse-power exponential increases while the derivative numerator is nonnegative. -/
theorem monotoneOn_rpow_mul_exp_neg_div {a p R : ℝ}
    (hp : 0 ≤ p) (hR : p * R ≤ a) :
    MonotoneOn (fun x : ℝ => x ^ (-p) * Real.exp (-a / x)) (Ioc 0 R) := by
  let g : ℝ → ℝ := fun x => -p * Real.log x - a * x⁻¹
  have hd (x : ℝ) (hx : 0 < x) :
      HasDerivAt g ((a - p * x) / x ^ 2) x := by
    convert! ((Real.hasDerivAt_log hx.ne').const_mul (-p)).sub
      (((hasDerivAt_id x).inv hx.ne').const_mul a) using 1
    simp only [id_eq]
    field_simp
    <;> ring
  have hg : MonotoneOn g (Ioc 0 R) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioc 0 R)
    · intro x hx
      exact (hd x hx.1).continuousAt.continuousWithinAt
    · intro x hx
      exact (hd x (interior_subset hx).1).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Ioc 0 R := interior_subset hx
      rw [(hd x hx'.1).deriv]
      apply div_nonneg
      · have hpx := mul_le_mul_of_nonneg_left hx'.2 hp
        linarith
      · positivity
  have he (x : ℝ) (hx : 0 < x) : x ^ (-p) * Real.exp (-a / x) = Real.exp (g x) := by
    rw [Real.rpow_def_of_pos hx, ← Real.exp_add]
    congr 1
    dsimp only [g]
    rw [div_eq_mul_inv]
    ring
  intro x hx y hy hxy
  dsimp only
  rw [he x hx.1, he y hy.1]
  exact Real.exp_le_exp.mpr (hg hx hy hxy)

end LpSelfSimilar.Analysis
