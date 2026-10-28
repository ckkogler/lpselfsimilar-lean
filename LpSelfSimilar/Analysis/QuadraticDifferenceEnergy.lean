module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Quadratic difference energy and splitting into two frequency regions

The elementary squared triangle inequality bounds a difference by twice each
individual energy. This allows the tiny high-frequency errors to be combined
without differentiating an indicator or assuming square integrability.
-/

open MeasureTheory Set

namespace LpSelfSimilar.Analysis

/-- The squared norm of a complex difference is bounded by twice each squared norm. -/
theorem sq_norm_sub_le_twice (z w : ℂ) :
    ‖z - w‖ ^ 2 ≤ 2 * ‖z‖ ^ 2 + 2 * ‖w‖ ^ 2 := by
  have h := norm_sub_le z w
  have hs : ‖z - w‖ ^ 2 ≤ (‖z‖ + ‖w‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖z‖ - ‖w‖)]

/-- A difference of measurable square-integrable amplitudes has an integrable squared norm. -/
theorem integrable_sq_norm_sub_of_sq {f g : ℝ → ℂ}
    (hf : AEStronglyMeasurable f) (hg : AEStronglyMeasurable g)
    (hif : Integrable (fun u => ‖f u‖ ^ 2))
    (hig : Integrable (fun u => ‖g u‖ ^ 2)) :
    Integrable (fun u => ‖f u - g u‖ ^ 2) := by
  refine ((hif.const_mul 2).add (hig.const_mul 2)).mono'
    ((hf.sub hg).norm.pow 2) (ae_of_all _ (fun u => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_norm_sub_le_twice _ _

/-- The weighted pair-difference integral is bounded by twice each individual weighted energy. -/
theorem half_integral_pair_difference_le {f₀ f₁ g₀ g₁ : ℝ → ℂ} {s : Set ℝ}
    (hs : MeasurableSet s)
    (hie : Integrable (fun u => ‖f₀ u - g₀ u‖ ^ 2 + ‖f₁ u - g₁ u‖ ^ 2))
    (hif : Integrable (fun u => ‖f₀ u‖ ^ 2 + ‖f₁ u‖ ^ 2))
    (hig : Integrable (fun u => ‖g₀ u‖ ^ 2 + ‖g₁ u‖ ^ 2)) :
    (1 / 2 : ℝ) * (∫ u : ℝ in s, ‖f₀ u - g₀ u‖ ^ 2 + ‖f₁ u - g₁ u‖ ^ 2) ≤
      2 * ((1 / 2 : ℝ) * ∫ u : ℝ in s, ‖f₀ u‖ ^ 2 + ‖f₁ u‖ ^ 2) +
      2 * ((1 / 2 : ℝ) * ∫ u : ℝ in s, ‖g₀ u‖ ^ 2 + ‖g₁ u‖ ^ 2) := by
  have hm : Integrable (fun u =>
      2 * (‖f₀ u‖ ^ 2 + ‖f₁ u‖ ^ 2) + 2 * (‖g₀ u‖ ^ 2 + ‖g₁ u‖ ^ 2)) :=
    (hif.const_mul 2).add (hig.const_mul 2)
  have h := setIntegral_mono_on hie.integrableOn hm.integrableOn hs (fun u hu => by
    nlinarith [sq_norm_sub_le_twice (f₀ u) (g₀ u), sq_norm_sub_le_twice (f₁ u) (g₁ u)])
  rw [integral_add (hif.const_mul 2).integrableOn (hig.const_mul 2).integrableOn,
    integral_const_mul, integral_const_mul] at h
  linarith

/-- The low seven-fourths bound and two high one-hundredth bounds imply the target nine-fifths margin. -/
theorem lt_nine_fifths_of_energy_bounds {x A L F G : ℝ} (hx : 0 < x)
    (hA : A ^ 2 ≤ L + 2 * F + 2 * G)
    (hL : Real.sqrt L < (7 / 4 : ℝ) * x)
    (hF : Real.sqrt F < x / 100) (hG : Real.sqrt G < x / 100) :
    A < (9 / 5 : ℝ) * x := by
  have hL' := (Real.sqrt_lt' (by positivity : 0 < (7 / 4 : ℝ) * x)).mp hL
  have hF' := (Real.sqrt_lt' (by positivity : 0 < x / 100)).mp hF
  have hG' := (Real.sqrt_lt' (by positivity : 0 < x / 100)).mp hG
  nlinarith [sq_nonneg (A - (9 / 5 : ℝ) * x)]

end LpSelfSimilar.Analysis
