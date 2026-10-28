module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Tactic

@[expose] public section

/-!
# Gaussian upper bounds for cosines in the positive arc

Differentiating `cos(x)*exp(x^2/2)` and using `x<=tan(x)` proves its
monotonicity on the positive arc. Symmetry then gives the exact Gaussian
bound for every `abs(x)<pi/2`. A rational lower bound at 1.43 supplies the
one-eighth margin used when omitting factors from a reserved tail product.
-/

open Set

namespace LpSelfSimilar.Analysis

/-- The Gaussian-corrected cosine decreases on every closed subinterval of the positive arc. -/
theorem cosine_gaussian_corrected_antitone {a : ℝ} (ha : 0 ≤ a) (haπ : a < Real.pi / 2) :
    AntitoneOn (fun x : ℝ ↦ Real.cos x * Real.exp (x ^ 2 / 2)) (Icc 0 a) := by
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ ↦ Real.cos y * Real.exp (y ^ 2 / 2))
      ((x * Real.cos x - Real.sin x) * Real.exp (x ^ 2 / 2)) x := by
    convert! (Real.hasDerivAt_cos x).mul (((hasDerivAt_id x).pow 2).div_const 2).exp using 1 <;> simp only [Pi.pow_apply, id_eq] <;> ring
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 a)
  · fun_prop
  · intro x hx
    exact (hd x).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : x ∈ Icc 0 a := interior_subset hx
    have hxπ : x < Real.pi / 2 := hx'.2.trans_lt haπ
    have hc : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hx'.1], hxπ⟩
    have ht := Real.le_tan hx'.1 hxπ
    rw [Real.tan_eq_sin_div_cos] at ht
    have hm := (le_div_iff₀ hc).mp ht
    rw [(hd x).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_pos _).le

/-- The exact positive-arc cosine estimate, with Gaussian exponent minus one half. -/
theorem cos_pos_le_exp_neg_half_sq {u : ℝ} (hu : |u| < Real.pi / 2) :
    0 < Real.cos u ∧ Real.cos u ≤ Real.exp (-(u ^ 2) / 2) := by
  have habs := abs_nonneg u
  have hm := cosine_gaussian_corrected_antitone habs hu
  have hv := hm (show (0 : ℝ) ∈ Icc 0 |u| from ⟨le_rfl, habs⟩)
    (show |u| ∈ Icc 0 |u| from ⟨habs, le_rfl⟩) habs
  simp only [Real.cos_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div, Real.exp_zero,
    one_mul, Real.cos_abs, sq_abs] at hv
  have hb : Real.cos u ≤ 1 / Real.exp (u ^ 2 / 2) :=
    (le_div_iff₀ (Real.exp_pos _)).mpr hv
  refine ⟨Real.cos_pos_of_mem_Ioo (abs_lt.mp hu), ?_⟩
  simpa only [neg_div, Real.exp_neg, one_div] using hb

/-- The largest first angle retains a strict one-eighth cosine margin. -/
theorem one_eighth_lt_cos_one_point_four_three :
    (1 / 8 : ℝ) < Real.cos (143 / 100) := by
  have hlo : (14 / 100 : ℝ) < Real.pi / 2 - 143 / 100 := by linarith [Real.pi_gt_d2]
  have hhi : Real.pi / 2 - 143 / 100 ≤ (1 / 5 : ℝ) := by linarith [Real.pi_lt_d2]
  have h0 : 0 ≤ Real.pi / 2 - 143 / 100 := by linarith
  have hc := pow_le_pow_left₀ h0 hhi 3
  have hs := Real.sin_ge_sub_cube h0
  rw [Real.sin_pi_div_two_sub] at hs
  norm_num at hc
  nlinarith

end LpSelfSimilar.Analysis
