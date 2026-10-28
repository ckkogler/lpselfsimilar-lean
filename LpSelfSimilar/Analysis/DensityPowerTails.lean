module

public import LpSelfSimilar.Analysis.DensityGeometricTails
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Density power tails from a mass power bound

On a superlevel set the density is at least the level, so its volume times
that level is bounded by the small-set mass modulus. Finite total mass proves
that every positive-level volume is finite. Solving the resulting real-power
inequality gives exactly the exponent -1/(1-alpha), including zero-volume sets.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LpSelfSimilar.Analysis

/-- Solve the density superlevel mass inequality at the exact real exponent. -/
theorem rpow_bound_of_mass_inequality {m u C α : ℝ}
    (hm : 0 ≤ m) (hu : 0 < u) (hC : 0 < C) (hα : α < 1)
    (hbound : u * m ≤ C * m ^ α) :
    m ≤ C ^ (1 / (1 - α)) * u ^ (-1 / (1 - α)) := by
  rcases hm.eq_or_lt with hm0 | hmpos
  · rw [← hm0]
    positivity
  have hlog := Real.log_le_log (mul_pos hu hmpos) hbound
  rw [Real.log_mul hu.ne' hmpos.ne',
    Real.log_mul hC.ne' (Real.rpow_pos_of_pos hmpos α).ne', Real.log_rpow hmpos] at hlog
  have hquot : Real.log m ≤ (Real.log C - Real.log u) / (1 - α) := by
    apply (le_div_iff₀ (sub_pos.mpr hα)).mpr
    nlinarith
  apply (Real.log_le_log_iff hmpos
    (mul_pos (Real.rpow_pos_of_pos hC _) (Real.rpow_pos_of_pos hu _))).mp
  rw [Real.log_mul (Real.rpow_pos_of_pos hC _).ne' (Real.rpow_pos_of_pos hu _).ne',
    Real.log_rpow hC, Real.log_rpow hu]
  convert hquot using 1 <;> ring

/-- The superlevel volume times the level is bounded by its actual mass modulus. -/
theorem density_superlevel_volume_mul_le_smallSetMass {X : Type*} [MeasurableSpace X]
    (ν μ : Measure X) {f : X → ℝ} (hf : Measurable f)
    (hdensity : μ = ν.withDensity (fun x => ENNReal.ofReal (f x))) (u : ℝ) :
    ENNReal.ofReal u * ν {x | u < f x} ≤ smallSetMass μ ν (ν {x | u < f x}) := by
  have hS : MeasurableSet {x | u < f x} := measurableSet_lt measurable_const hf
  exact (density_level_volume_mul_le_mass ν μ hdensity hS hS subset_rfl u
    (fun _ hx => hx.le)).trans (measure_le_smallSetMass μ ν hS le_rfl)

/-- A positive superlevel set of a finite-density measure has finite reference volume. -/
theorem density_superlevel_measure_ne_top {X : Type*} [MeasurableSpace X]
    (ν μ : Measure X) [IsFiniteMeasure μ] {f : X → ℝ} (hf : Measurable f)
    (hdensity : μ = ν.withDensity (fun x => ENNReal.ofReal (f x)))
    {u : ℝ} (hu : 0 < u) : ν {x | u < f x} ≠ ∞ := by
  have hS : MeasurableSet {x | u < f x} := measurableSet_lt measurable_const hf
  have h := density_level_volume_mul_le_mass ν μ hdensity hS hS subset_rfl u
    (fun _ hx => hx.le)
  intro htop
  rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hu).ne'] at h
  exact measure_ne_top μ _ (top_le_iff.mp h)

/-- A global small-set power estimate gives the paper's exact density tail exponent. -/
theorem density_superlevel_volume_rpow_bound {X : Type*} [MeasurableSpace X]
    (ν μ : Measure X) [IsFiniteMeasure μ] {f : X → ℝ} (hf : Measurable f)
    (hdensity : μ = ν.withDensity (fun x => ENNReal.ofReal (f x)))
    {C α : ℝ} (hC : 0 < C) (hα : α < 1)
    (hmass : ∀ t : ℝ, 0 < t →
      smallSetMass μ ν (ENNReal.ofReal t) ≤ ENNReal.ofReal (C * t ^ α))
    {u : ℝ} (hu : 0 < u) :
    (ν {x | u < f x}).toReal ≤ C ^ (1 / (1 - α)) * u ^ (-1 / (1 - α)) := by
  let m := (ν {x | u < f x}).toReal
  have hm : 0 ≤ m := ENNReal.toReal_nonneg
  rcases hm.eq_or_lt with hm0 | hmpos
  · change m ≤ _
    rw [← hm0]
    positivity
  have hfin := density_superlevel_measure_ne_top ν μ hf hdensity hu
  have hmass' := hmass m hmpos
  rw [show ENNReal.ofReal m = ν {x | u < f x} from ENNReal.ofReal_toReal hfin] at hmass'
  have h := (density_superlevel_volume_mul_le_smallSetMass ν μ hf hdensity u).trans hmass'
  have hreal : u * m ≤ C * m ^ α := by
    have h' := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hu.le,
      ENNReal.toReal_ofReal (mul_pos hC (Real.rpow_pos_of_pos hmpos α)).le] using h'
  exact rpow_bound_of_mass_inequality hm hu hC hα hreal

end LpSelfSimilar.Analysis
