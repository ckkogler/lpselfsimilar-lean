module

public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic

@[expose] public section

/-!
# Logarithmic substitution on an entire half-line

The decreasing map `R -> exp(-k*R)` carries `[a,infinity)` exactly onto
`(0,exp(-k*a)]`. The one-dimensional change-of-variables theorem proves both
integrability equivalence and the integral identity, without any continuity
assumption on the integrand or assumed convergence at the missing endpoint.
-/

open MeasureTheory Set

namespace LpSelfSimilar.Analysis

/-- Exact image of a logarithmic half-line, with the zero spatial endpoint excluded. -/
theorem image_exp_neg_mul_Ici {k : ℝ} (hk : 0 < k) (a : ℝ) :
    (fun R : ℝ => Real.exp (-k * R)) '' Ici a = Ioc 0 (Real.exp (-k * a)) := by
  ext r
  constructor
  · rintro ⟨R, hR, rfl⟩
    change a ≤ R at hR
    exact ⟨Real.exp_pos _, Real.exp_le_exp.mpr (by nlinarith)⟩
  · intro hr
    refine ⟨-Real.log r / k, ?_, ?_⟩
    · apply (le_div_iff₀ hk).mpr
      have hl := Real.log_le_log hr.1 hr.2
      rw [Real.log_exp] at hl
      linarith
    · have he : -k * (-Real.log r / k) = Real.log r := by field_simp
      change Real.exp (-k * (-Real.log r / k)) = r
      rw [he, Real.exp_log hr.1]

/-- The actual logarithmic Jacobian gives an integrability equivalence on the full range. -/
theorem integrableOn_div_iff_exp_neg_mul (f : ℝ → ℝ) {k : ℝ} (hk : 0 < k) (a : ℝ) :
    IntegrableOn (fun r => f r / r) (Ioc 0 (Real.exp (-k * a))) volume ↔
      IntegrableOn (fun R => f (Real.exp (-k * R))) (Ici a) volume := by
  have hd (R : ℝ) : HasDerivAt (fun S : ℝ => Real.exp (-k * S))
      (-k * Real.exp (-k * R)) R := by
    convert ((hasDerivAt_id R).const_mul (-k)).exp using 1 <;> simp <;> ring
  have hinj : InjOn (fun R : ℝ => Real.exp (-k * R)) (Ici a) := by
    intro R _ S _ he
    have hh := Real.exp_injective he
    nlinarith
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ici (fun R _ => (hd R).hasDerivWithinAt) hinj (fun r => f r / r)
  rw [image_exp_neg_mul_Ici hk] at h
  have he : (fun R : ℝ => |-k * Real.exp (-k * R)| •
      (f (Real.exp (-k * R)) / Real.exp (-k * R))) =
      (fun R : ℝ => k * f (Real.exp (-k * R))) := by
    funext R
    rw [abs_mul, abs_neg, abs_of_pos hk, abs_of_pos (Real.exp_pos _), smul_eq_mul]
    field_simp
  rw [he] at h
  exact h.trans (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hk.ne') _)

/-- Exact `dr/r = k*dR` identity, proved for arbitrary integrands on the entire half-line. -/
theorem integral_div_eq_mul_integral_exp_neg_mul (f : ℝ → ℝ) {k : ℝ}
    (hk : 0 < k) (a : ℝ) :
    (∫ r in Ioc 0 (Real.exp (-k * a)), f r / r) =
      k * ∫ R in Ici a, f (Real.exp (-k * R)) := by
  have hd (R : ℝ) : HasDerivAt (fun S : ℝ => Real.exp (-k * S))
      (-k * Real.exp (-k * R)) R := by
    convert ((hasDerivAt_id R).const_mul (-k)).exp using 1 <;> simp <;> ring
  have hinj : InjOn (fun R : ℝ => Real.exp (-k * R)) (Ici a) := by
    intro R _ S _ he
    have hh := Real.exp_injective he
    nlinarith
  have h := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ici (fun R _ => (hd R).hasDerivWithinAt) hinj (fun r => f r / r)
  rw [image_exp_neg_mul_Ici hk] at h
  calc
    _ = ∫ R in Ici a, |-k * Real.exp (-k * R)| •
        (f (Real.exp (-k * R)) / Real.exp (-k * R)) := h
    _ = ∫ R in Ici a, k * f (Real.exp (-k * R)) := by
      apply integral_congr_ae
      apply ae_of_all
      intro R
      change |-k * Real.exp (-k * R)| • (f (Real.exp (-k * R)) / Real.exp (-k * R)) =
        k * f (Real.exp (-k * R))
      rw [abs_mul, abs_neg, abs_of_pos hk, abs_of_pos (Real.exp_pos _), smul_eq_mul]
      field_simp
    _ = _ := integral_const_mul _ _

end LpSelfSimilar.Analysis
