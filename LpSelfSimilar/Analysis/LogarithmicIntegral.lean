module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-!
Change of variables between ds/s and logarithmic scale x=log(1/s).

The exponential map is strictly monotone with its actual derivative. Mathlib's
monotone change-of-variables theorem needs no continuity of the integrand; its
integrability equivalence transfers the independently proved logarithmic-scale
integrability to the physical-scale integral.
-/

open MeasureTheory Set Real

namespace LpSelfSimilar

private lemma hasDerivAt_exp_neg (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ Real.exp (-y)) (-Real.exp (-x)) x := by
  convert ((hasDerivAt_id x).neg.exp) using 1 <;> simp

private lemma log_integrand_comp_deriv (f : ℝ → ℝ) :
    (fun x ↦ ((fun s ↦ f s / s) ∘ (fun y ↦ Real.exp (-y))) x * (-Real.exp (-x))) =
      fun x ↦ -(f (Real.exp (-x))) := by
  funext x
  dsimp only [Function.comp_apply]
  field_simp

/-- Exact logarithmic substitution, valid even for merely measurable integrands. -/
theorem integral_div_eq_integral_exp_neg (f : ℝ → ℝ) (a b : ℝ) :
    (∫ s in Real.exp (-b)..Real.exp (-a), f s / s) =
      ∫ x in a..b, f (Real.exp (-x)) := by
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (g := fun s ↦ f s / s) (a := a) (b := b)
    (show ContinuousOn (fun x : ℝ ↦ Real.exp (-x)) (uIcc a b) by fun_prop)
    (fun x _ ↦ hasDerivAt_exp_neg x) (fun x _ ↦ neg_nonpos.mpr (Real.exp_pos _).le)
  rw [log_integrand_comp_deriv, intervalIntegral.integral_neg] at h
  calc
    _ = -(∫ s in Real.exp (-a)..Real.exp (-b), f s / s) :=
      intervalIntegral.integral_symm _ _
    _ = _ := by rw [← h, neg_neg]

lemma intervalIntegrable_div_iff_exp_neg (f : ℝ → ℝ) (a b : ℝ) :
    IntervalIntegrable (fun s ↦ f s / s) volume (Real.exp (-b)) (Real.exp (-a)) ↔
      IntervalIntegrable (fun x ↦ f (Real.exp (-x))) volume a b := by
  have h := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonpos
    (g := fun s ↦ f s / s) (a := a) (b := b)
    (show ContinuousOn (fun x : ℝ ↦ Real.exp (-x)) (uIcc a b) by fun_prop)
    (fun x _ ↦ hasDerivAt_exp_neg x) (fun x _ ↦ neg_nonpos.mpr (Real.exp_pos _).le)
  rw [log_integrand_comp_deriv] at h
  constructor
  · intro hi
    have hn := h.mpr hi.symm
    have hn' := hn.neg
    change IntervalIntegrable (fun x ↦ -(-f (Real.exp (-x)))) volume a b at hn'
    simpa only [neg_neg] using hn'
  · intro hi
    exact (h.mp hi.neg).symm

end LpSelfSimilar
