module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Tactic

@[expose] public section

/-!
# Exact even moments of exp(-x^2)

The substitution y=x^2 in the Gamma integral gives the positive half-line
moment. Even reflection and proved integrability give the full-line identity
integral x^(2*k)*exp(-x^2)=Gamma(k+1/2), with no numerical approximation.
-/

open MeasureTheory Set

namespace LpSelfSimilar.Gaussian

/-- Every polynomial even moment of exp(-x^2) is integrable. -/
theorem integrable_gaussian_even_moment (k : ℕ) :
    Integrable (fun x : ℝ => x ^ (2 * k) * Real.exp (-(x ^ 2))) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1) (s := ((2 * k : ℕ) : ℝ))
    (by norm_num) (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg (2 * k)))
  simpa only [Real.rpow_natCast, neg_one_mul] using! h

/-- The Gamma substitution gives twice the positive-half-line Gaussian moment. -/
theorem gamma_eq_two_mul_integral_gaussian_even_moment (k : ℕ) :
    Real.Gamma ((k : ℝ) + 1 / 2) =
      2 * ∫ x : ℝ in Ioi 0, x ^ (2 * k) * Real.exp (-(x ^ 2)) := by
  rw [Real.Gamma_eq_integral (by positivity),
    ← integral_comp_rpow_Ioi_of_pos (p := 2) (by norm_num), ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx0 : 0 < x := hx
  have hm : x * (x ^ (2 : ℝ)) ^ ((k : ℝ) + 1 / 2 - 1) = x ^ (2 * k) := by
    rw [← Real.rpow_mul hx0.le]
    nth_rw 1 [← Real.rpow_one x]
    rw [← Real.rpow_add hx0]
    have he : (1 : ℝ) + 2 * ((k : ℝ) + 1 / 2 - 1) = ((2 * k : ℕ) : ℝ) := by
      push_cast
      ring
    rw [he, Real.rpow_natCast]
  simp only [smul_eq_mul]
  rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
  calc
    _ = 2 * (x * (x ^ (2 : ℝ)) ^ ((k : ℝ) + 1 / 2 - 1)) * Real.exp (-(x ^ (2 : ℝ))) := by ring
    _ = _ := by rw [hm, Real.rpow_two]; ring

/-- The whole-line Gaussian even moment is exactly Gamma(k+1/2). -/
theorem integral_gaussian_even_moment (k : ℕ) :
    (∫ x : ℝ, x ^ (2 * k) * Real.exp (-(x ^ 2))) = Real.Gamma ((k : ℝ) + 1 / 2) := by
  let f : ℝ → ℝ := fun x => x ^ (2 * k) * Real.exp (-(x ^ 2))
  have hi : Integrable f := integrable_gaussian_even_moment k
  have heven (x : ℝ) : f (-x) = f x := by
    dsimp only [f]
    rw [show (-x) ^ (2 * k) = x ^ (2 * k) by rw [pow_mul, neg_sq, ← pow_mul], neg_sq]
  have he : (∫ x in Iic (0 : ℝ), f x) = ∫ x in Ioi (0 : ℝ), f x := by
    calc
      _ = ∫ x in Ioi (0 : ℝ), f (-x) := by
        simpa only [neg_zero] using (integral_comp_neg_Ioi 0 f).symm
      _ = _ := setIntegral_congr_fun measurableSet_Ioi (fun x hx => heven x)
  change (∫ x, f x) = _
  rw [← integral_add_compl (s := Ioi 0) measurableSet_Ioi hi, compl_Ioi, he]
  have h := gamma_eq_two_mul_integral_gaussian_even_moment k
  change Real.Gamma ((k : ℝ) + 1 / 2) = 2 * ∫ x in Ioi (0 : ℝ), f x at h
  linarith

end LpSelfSimilar.Gaussian
