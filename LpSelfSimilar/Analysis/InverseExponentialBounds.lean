module

public import LpSelfSimilar.Analysis.InverseExponentialMonotonicity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-!
# Endpoint bounds for inverse-power Gaussian tails

Half-integral powers are written as integer powers times a square root.
The monotonicity theorem gives an endpoint comparison. At the endpoint 1/250,
the reciprocal square root is at most sixteen, yielding rational coefficients
for the remaining certified exponential calculations.
-/

open Set

namespace LpSelfSimilar.Analysis

/-- A negative half-integral real power is the exact reciprocal power-square-root expression. -/
theorem rpow_neg_nat_add_half_eq {x : ℝ} (hx : 0 < x) (n : ℕ) :
    x ^ (-((n : ℝ) + 1 / 2)) = 1 / (x ^ n * Real.sqrt x) := by
  rw [Real.rpow_neg hx.le, Real.rpow_add hx, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  simp only [one_div]

/-- The endpoint comparison for a Gaussian inverse scale with a half-integral power. -/
theorem exp_neg_div_div_pow_sqrt_le_endpoint {a x R : ℝ} (hx : 0 < x) (hxR : x ≤ R)
    (n : ℕ) (hscale : ((n : ℝ) + 1 / 2) * R ≤ a) :
    Real.exp (-a / x) / (x ^ n * Real.sqrt x) ≤
      Real.exp (-a / R) / (R ^ n * Real.sqrt R) := by
  have hR : 0 < R := hx.trans_le hxR
  have hm := monotoneOn_rpow_mul_exp_neg_div
    (p := (n : ℝ) + 1 / 2) (by positivity) hscale
  have h := hm (show x ∈ Ioc 0 R from ⟨hx, hxR⟩)
    (show R ∈ Ioc 0 R from ⟨hR, le_rfl⟩) hxR
  dsimp only at h
  rw [rpow_neg_nat_add_half_eq hx n, rpow_neg_nat_add_half_eq hR n] at h
  convert! h using 1 <;> ring

/-- The corresponding endpoint comparison for an integer power. -/
theorem exp_neg_div_div_pow_le_endpoint {a x R : ℝ} (hx : 0 < x) (hxR : x ≤ R)
    (n : ℕ) (hscale : (n : ℝ) * R ≤ a) :
    Real.exp (-a / x) / x ^ n ≤ Real.exp (-a / R) / R ^ n := by
  have hR : 0 < R := hx.trans_le hxR
  have hm := monotoneOn_rpow_mul_exp_neg_div (p := (n : ℝ)) (Nat.cast_nonneg n) hscale
  have h := hm (show x ∈ Ioc 0 R from ⟨hx, hxR⟩)
    (show R ∈ Ioc 0 R from ⟨hR, le_rfl⟩) hxR
  dsimp only at h
  rw [Real.rpow_neg hx.le, Real.rpow_neg hR.le, Real.rpow_natCast, Real.rpow_natCast] at h
  convert! h using 1 <;> ring

/-- The exact positive endpoint square root has reciprocal at most sixteen. -/
theorem inv_sqrt_one_div_two_hundred_fifty_le :
    1 / Real.sqrt (1 / 250 : ℝ) ≤ 16 := by
  have hs0 : 0 < Real.sqrt (1 / 250 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 250)
  apply (div_le_iff₀ hs0).mpr
  nlinarith

/-- Half-integral endpoint powers have a rational coefficient over exp(250*a). -/
theorem gaussian_half_power_endpoint_le (a : ℝ) (n : ℕ) :
    Real.exp (-a / (1 / 250 : ℝ)) / ((1 / 250 : ℝ) ^ n * Real.sqrt (1 / 250 : ℝ)) ≤
      16 * (250 : ℝ) ^ n / Real.exp (250 * a) := by
  have hs0 : Real.sqrt (1 / 250 : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 1 / 250)).ne'
  have hp : (1 / 250 : ℝ) ^ n = 1 / (250 : ℝ) ^ n := by rw [div_pow, one_pow]
  have he : Real.exp (-a / (1 / 250 : ℝ)) = (Real.exp (250 * a))⁻¹ := by
    rw [show -a / (1 / 250 : ℝ) = -(250 * a) by ring, Real.exp_neg]
  calc
    _ = ((250 : ℝ) ^ n / Real.exp (250 * a)) * (1 / Real.sqrt (1 / 250 : ℝ)) := by
      rw [hp, he]
      field_simp
    _ ≤ ((250 : ℝ) ^ n / Real.exp (250 * a)) * 16 :=
      mul_le_mul_of_nonneg_left inv_sqrt_one_div_two_hundred_fifty_le (by positivity)
    _ = _ := by ring

end LpSelfSimilar.Analysis
