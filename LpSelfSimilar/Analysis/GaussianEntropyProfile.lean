module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic

@[expose] public section

/-!
# The explicit Gaussian entropy profile

The Gaussian information derivative bound integrates at the reciprocal
amplitudes exp(-v/2) and exp(v/2) to the profile below. It is increasing,
vanishes at zero and is concave on the nonnegative half-line. The exact
second derivative is retained for comparison with the displayed formula.
-/

open Real Set

namespace LpSelfSimilar.Analysis

noncomputable def gaussianEntropyProfile (v : ℝ) : ℝ :=
  (exp (-exp (-v)) - exp (-exp v)) / 2

noncomputable def gaussianEntropyProfileSlope (v : ℝ) : ℝ :=
  (exp (-v) * exp (-exp (-v)) + exp v * exp (-exp v)) / 2

noncomputable def gaussianEntropyProfileCurvature (v : ℝ) : ℝ :=
  (exp (-v) * exp (-exp (-v)) * (exp (-v) - 1) +
    exp v * exp (-exp v) * (1 - exp v)) / 2

@[fun_prop] theorem continuous_gaussianEntropyProfile : Continuous gaussianEntropyProfile := by
  unfold gaussianEntropyProfile
  fun_prop

theorem gaussianEntropyProfile_zero : gaussianEntropyProfile 0 = 0 := by
  simp [gaussianEntropyProfile]

theorem hasDerivAt_gaussianEntropyProfile (v : ℝ) :
    HasDerivAt gaussianEntropyProfile (gaussianEntropyProfileSlope v) v := by
  have ha := (hasDerivAt_id v).neg.exp
  have hb := hasDerivAt_exp v
  convert! (ha.neg.exp.sub hb.neg.exp).div_const 2 using 1 <;>
    simp only [gaussianEntropyProfile, gaussianEntropyProfileSlope, Pi.neg_apply, id_eq] <;> ring

theorem hasDerivAt_gaussianEntropyProfileSlope (v : ℝ) :
    HasDerivAt gaussianEntropyProfileSlope (gaussianEntropyProfileCurvature v) v := by
  have ha := (hasDerivAt_id v).neg.exp
  have hb := hasDerivAt_exp v
  convert! ((ha.mul ha.neg.exp).add (hb.mul hb.neg.exp)).div_const 2 using 1 <;>
    simp only [gaussianEntropyProfileSlope, gaussianEntropyProfileCurvature, Pi.neg_apply, id_eq] <;> ring

/-- The profile's actual second derivative is the displayed exact curvature formula. -/
theorem deriv_deriv_gaussianEntropyProfile (v : ℝ) :
    deriv (deriv gaussianEntropyProfile) v = gaussianEntropyProfileCurvature v := by
  rw [show deriv gaussianEntropyProfile = gaussianEntropyProfileSlope from
    funext (fun x => (hasDerivAt_gaussianEntropyProfile x).deriv)]
  exact (hasDerivAt_gaussianEntropyProfileSlope v).deriv

theorem gaussianEntropyProfileSlope_pos (v : ℝ) : 0 < gaussianEntropyProfileSlope v := by
  unfold gaussianEntropyProfileSlope
  positivity

theorem strictMono_gaussianEntropyProfile : StrictMono gaussianEntropyProfile := by
  apply strictMono_of_deriv_pos
  intro v
  rw [(hasDerivAt_gaussianEntropyProfile v).deriv]
  exact gaussianEntropyProfileSlope_pos v

theorem gaussianEntropyProfileCurvature_nonpos {v : ℝ} (hv : 0 ≤ v) :
    gaussianEntropyProfileCurvature v ≤ 0 := by
  have ha : exp (-v) ≤ 1 := exp_le_one_iff.mpr (neg_nonpos.mpr hv)
  have hb : 1 ≤ exp v := one_le_exp_iff.mpr hv
  unfold gaussianEntropyProfileCurvature
  apply div_nonpos_of_nonpos_of_nonneg _ (by norm_num)
  exact add_nonpos
    (mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr ha))
    (mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hb))

theorem concaveOn_gaussianEntropyProfile : ConcaveOn ℝ (Ici 0) gaussianEntropyProfile := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ici 0)
    continuous_gaussianEntropyProfile.continuousOn
    (fun x _ => (hasDerivAt_gaussianEntropyProfile x).hasDerivWithinAt)
    (fun x _ => (hasDerivAt_gaussianEntropyProfileSlope x).hasDerivWithinAt)
  intro x hx
  exact gaussianEntropyProfileCurvature_nonpos (interior_subset hx)

/-- Concavity retains the line from zero to the value at one, then monotonicity
retains that endpoint value on the remaining half-line. -/
theorem gaussianEntropyProfile_one_mul_min_le {v : ℝ} (hv : 0 ≤ v) :
    gaussianEntropyProfile 1 * min 1 v ≤ gaussianEntropyProfile v := by
  by_cases hv1 : v ≤ 1
  · rw [min_eq_right hv1]
    have h := concaveOn_gaussianEntropyProfile.2
      (show (0 : ℝ) ∈ Ici 0 from by simp)
      (show (1 : ℝ) ∈ Ici 0 from by simp)
      (show 0 ≤ 1 - v from sub_nonneg.mpr hv1) hv (by ring)
    simpa only [smul_eq_mul, gaussianEntropyProfile_zero, mul_zero, zero_mul, mul_one, zero_add, mul_comm] using h
  · rw [min_eq_left (le_of_not_ge hv1), mul_one]
    exact strictMono_gaussianEntropyProfile.monotone (le_of_not_ge hv1)

end LpSelfSimilar.Analysis
