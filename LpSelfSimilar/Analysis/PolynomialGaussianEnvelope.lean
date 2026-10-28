module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic

@[expose] public section

/-!
# Monotonicity of a polynomial times a Gaussian tail

After the inverse-square-root substitution, the detail envelope has the shape
`u^7 * (1+u^2/b)^2 * exp(-u^2/2+c*u)`. Its logarithmic derivative is explicit.
For b>0 and c<=3 it is strictly negative on u>=15, with no asymptotic argument.
-/

namespace LpSelfSimilar.Analysis

/-- The polynomial Gaussian profile appearing after an inverse-square-root substitution. -/
noncomputable def polynomialGaussianEnvelope (b c u : ℝ) : ℝ :=
  u ^ 7 * (1 + u ^ 2 / b) ^ 2 * Real.exp (-u ^ 2 / 2 + c * u)

/-- The profile is strictly positive in the positive parameter range. -/
theorem polynomialGaussianEnvelope_pos {b u : ℝ} (hb : 0 < b) (hu : 0 < u) (c : ℝ) :
    0 < polynomialGaussianEnvelope b c u := by
  unfold polynomialGaussianEnvelope
  positivity

/-- Exact logarithmic-derivative factorization of the actual profile derivative. -/
theorem hasDerivAt_polynomialGaussianEnvelope {b u : ℝ} (hb : 0 < b) (hu : 0 < u) (c : ℝ) :
    HasDerivAt (polynomialGaussianEnvelope b c)
      (polynomialGaussianEnvelope b c u *
        (7 / u + 4 * u / (b + u ^ 2) - u + c)) u := by
  have hp : HasDerivAt (fun v : ℝ => v ^ 7) (7 * u ^ 6) u := by
    simpa using! (hasDerivAt_id u).pow 7
  have hq : HasDerivAt (fun v : ℝ => 1 + v ^ 2 / b) (2 * u / b) u := by
    simpa using! (((hasDerivAt_id u).pow 2).div_const b).const_add 1
  have he : HasDerivAt (fun v : ℝ => Real.exp (-v ^ 2 / 2 + c * v))
      (Real.exp (-u ^ 2 / 2 + c * u) * (-u + c)) u := by
    convert! ((((hasDerivAt_id u).pow 2).neg.div_const 2).add
      ((hasDerivAt_id u).const_mul c)).exp using 1 <;> simp <;> ring
  have h := (hp.mul (hq.pow 2)).mul he
  have hbq : b + u ^ 2 ≠ 0 := by positivity
  convert! h using 1 <;> simp only [polynomialGaussianEnvelope, Pi.mul_apply, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  all_goals field_simp
  all_goals ring

/-- The logarithmic derivative is strictly negative throughout the explicit tail range. -/
theorem polynomialGaussianEnvelope_logDeriv_neg {b c u : ℝ}
    (hb : 0 < b) (hc : c ≤ 3) (hu : 15 ≤ u) :
    7 / u + 4 * u / (b + u ^ 2) - u + c < 0 := by
  have hu0 : 0 < u := by linarith
  have hfrac : 4 * u / (b + u ^ 2) ≤ 4 / u := by
    apply (div_le_div_iff₀ (by positivity) hu0).mpr
    nlinarith
  have hm : 11 / u < u - 3 := by
    apply (div_lt_iff₀ hu0).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) (show 0 ≤ u + 12 by linarith)]
  have he : 7 / u + 4 / u = 11 / u := by ring
  linarith

/-- The actual profile is strictly decreasing on the entire explicit tail half-line. -/
theorem strictAntiOn_polynomialGaussianEnvelope {b c : ℝ} (hb : 0 < b) (hc : c ≤ 3) :
    StrictAntiOn (polynomialGaussianEnvelope b c) (Set.Ici 15) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
  · unfold polynomialGaussianEnvelope
    fun_prop
  · intro u hu
    have hu15 : 15 ≤ u := (interior_subset hu)
    have hu0 : 0 < u := by linarith
    rw [(hasDerivAt_polynomialGaussianEnvelope hb hu0 c).deriv]
    exact mul_neg_of_pos_of_neg (polynomialGaussianEnvelope_pos hb hu0 c)
      (polynomialGaussianEnvelope_logDeriv_neg hb hc hu15)

end LpSelfSimilar.Analysis
