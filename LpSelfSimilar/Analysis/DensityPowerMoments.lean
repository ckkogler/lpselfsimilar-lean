module

public import LpSelfSimilar.Analysis.DensityPowerTails
public import LpSelfSimilar.Analysis.SquareLayerCake
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

/-!
# Square integrability from a density power tail

Near zero, total mass bounds u*volume{f>u}. Above one, the power-tail estimate
bounds it by C*u^(1-kappa), integrable exactly when kappa>2. The square
layer-cake identity then gives a finite second moment and MemLp at two.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LpSelfSimilar.Analysis

/-- A tail exponent exceeding two makes the first weighted tail integral finite. -/
theorem integrable_superlevel_first_moment_of_power_tail {X : Type*} [MeasurableSpace X]
    (ν μ : Measure X) [IsFiniteMeasure μ] {f : X → ℝ} (hf : Measurable f)
    (hdensity : μ = ν.withDensity (fun x => ENNReal.ofReal (f x)))
    {C κ : ℝ} (hC : 0 ≤ C) (hκ : 2 < κ)
    (htail : ∀ u : ℝ, 0 < u → (ν {x | u < f x}).toReal ≤ C * u ^ (-κ)) :
    IntegrableOn (fun u : ℝ => u * (ν {x | u < f x}).toReal) (Ioi 0) volume := by
  have hanti : Antitone (fun u : ℝ => ν {x | u < f x}) :=
    fun _ _ h => measure_mono (fun _ hx => lt_of_le_of_lt h hx)
  have hmeas : Measurable (fun u : ℝ => (ν {x | u < f x}).toReal) :=
    hanti.measurable.ennreal_toReal
  have hprod : Measurable (fun u : ℝ => u * (ν {x | u < f x}).toReal) :=
    measurable_id.mul hmeas
  have hnear : IntegrableOn (fun u : ℝ => u * (ν {x | u < f x}).toReal) (Ioc 0 1) volume := by
    apply (integrableOn_const (by simp) :
      IntegrableOn (fun _ : ℝ => (μ univ).toReal) (Ioc 0 1) volume).mono' hprod.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hu.1.le ENNReal.toReal_nonneg)]
    have hS : MeasurableSet {x | u < f x} := measurableSet_lt measurable_const hf
    have h := (density_level_volume_mul_le_mass ν μ hdensity hS hS subset_rfl u
      (fun _ hx => hx.le)).trans (measure_mono (subset_univ _))
    have h' := ENNReal.toReal_mono (measure_ne_top μ univ) h
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hu.1.le] using h'
  have hfar : IntegrableOn (fun u : ℝ => u * (ν {x | u < f x}).toReal) (Ioi 1) volume := by
    apply ((integrableOn_Ioi_rpow_of_lt (a := 1 - κ) (by linarith) zero_lt_one).const_mul C).mono'
      hprod.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := zero_lt_one.trans hu
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hu0.le ENNReal.toReal_nonneg)]
    calc
      _ ≤ u * (C * u ^ (-κ)) := mul_le_mul_of_nonneg_left (htail u hu0) hu0.le
      _ = C * u ^ (1 - κ) := by
        rw [sub_eq_add_neg, Real.rpow_add hu0, Real.rpow_one]
        ring
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1), integrableOn_union]
  exact ⟨hnear, hfar⟩

/-- The corresponding extended weighted tail integral is genuinely finite. -/
theorem lintegral_superlevel_first_moment_lt_top_of_power_tail {X : Type*} [MeasurableSpace X]
    (ν μ : Measure X) [IsFiniteMeasure μ] {f : X → ℝ} (hf : Measurable f)
    (hdensity : μ = ν.withDensity (fun x => ENNReal.ofReal (f x)))
    {C κ : ℝ} (hC : 0 ≤ C) (hκ : 2 < κ)
    (htail : ∀ u : ℝ, 0 < u → (ν {x | u < f x}).toReal ≤ C * u ^ (-κ)) :
    (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal u * ν {x | u < f x}) < ∞ := by
  have hi := integrable_superlevel_first_moment_of_power_tail ν μ hf hdensity hC hκ htail
  have heq : (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u * (ν {x | u < f x}).toReal)) =
      ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal u * ν {x | u < f x} := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp only
    rw [ENNReal.ofReal_mul (le_of_lt hu), ENNReal.ofReal_toReal
      (density_superlevel_measure_ne_top ν μ hf hdensity hu)]
  rw [← heq]
  exact hi.lintegral_lt_top

/-- The layer-cake argument supplies MemLp at two from the stated density power tail. -/
theorem memLp_two_of_density_power_tail {X : Type*} [MeasurableSpace X]
    (ν μ : Measure X) [IsFiniteMeasure μ] {f : X → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hdensity : μ = ν.withDensity (fun x => ENNReal.ofReal (f x)))
    {C κ : ℝ} (hC : 0 ≤ C) (hκ : 2 < κ)
    (htail : ∀ u : ℝ, 0 < u → (ν {x | u < f x}).toReal ≤ C * u ^ (-κ)) :
    MemLp f 2 ν := by
  have hi := lintegral_superlevel_first_moment_lt_top_of_power_tail ν μ hf hdensity hC hκ htail
  have hsq : (∫⁻ x, ENNReal.ofReal (f x) ^ 2 ∂ν) < ∞ := by
    rw [lintegral_sq_eq_twice_lintegral_superlevel ν hf.aemeasurable hf0]
    exact ENNReal.mul_lt_top (by norm_num) hi
  refine (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num) (by norm_num) hf.aestronglyMeasurable).mpr ?_
  convert hsq using 1
  apply lintegral_congr
  intro x
  rw [Real.enorm_of_nonneg (hf0 x)]
  norm_num

/-- The paper's real-valued layer-cake identity for an actual finite-density measure. -/
theorem integral_sq_eq_twice_integral_superlevel {X : Type*} [MeasurableSpace X]
    (ν μ : Measure X) [IsFiniteMeasure μ] {f : X → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hdensity : μ = ν.withDensity (fun x => ENNReal.ofReal (f x))) :
    (∫ x, f x ^ 2 ∂ν) = 2 * ∫ u in Ioi (0 : ℝ), u * (ν {x | u < f x}).toReal := by
  have hanti : Antitone (fun u : ℝ => ν {x | u < f x}) :=
    fun _ _ h => measure_mono (fun _ hx => lt_of_le_of_lt h hx)
  have hmeas : Measurable (fun u : ℝ => (ν {x | u < f x}).toReal) :=
    hanti.measurable.ennreal_toReal
  have hprod : Measurable (fun u : ℝ => u * (ν {x | u < f x}).toReal) :=
    measurable_id.mul hmeas
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun x => sq_nonneg (f x)))
    (hf.pow_const 2).aestronglyMeasurable]
  simp only [ENNReal.ofReal_pow (hf0 _)]
  rw [lintegral_sq_eq_twice_lintegral_superlevel ν hf.aemeasurable hf0,
    ENNReal.toReal_mul, ENNReal.toReal_ofNat]
  congr 1
  rw [integral_eq_lintegral_of_nonneg_ae
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        exact mul_nonneg (le_of_lt hu) ENNReal.toReal_nonneg)
    hprod.aestronglyMeasurable]
  congr 1
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro u hu
  dsimp only
  rw [ENNReal.ofReal_mul (le_of_lt hu), ENNReal.ofReal_toReal
    (density_superlevel_measure_ne_top ν μ hf hdensity hu)]

end LpSelfSimilar.Analysis
