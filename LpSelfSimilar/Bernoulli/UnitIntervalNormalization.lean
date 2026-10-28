module

public import LpSelfSimilar.Bernoulli.Decomposition
public import LpSelfSimilar.SelfSimilar.Concentration.Definitions

@[expose] public section

/-!
# Normalizing the actual Bernoulli law to the unit interval

The affine map T(x)=((1-theta)*x+1)/2 sends the proved geometric-series
support into [0,1]. Conjugating the actual balanced affine stationarity
identity gives the maps theta*x and theta*x+1-theta. Neither support nor
stationarity of the normalized law is assumed.
-/

open MeasureTheory Set
open LpSelfSimilar.Geometry LpSelfSimilar.SelfSimilar.Concentration
open scoped ENNReal

namespace LpSelfSimilar.Bernoulli

/-- The positive affine change of variables normalizing the Bernoulli support. -/
noncomputable def unitIntervalNormalization (θ : ℝ) (hθ1 : θ < 1) : PositiveAffine :=
  ⟨(1 - θ) / 2, 1 / 2, div_pos (sub_pos.mpr hθ1) (by norm_num)⟩

/-- The normalization has the usual single-fraction formula. -/
theorem unitIntervalNormalization_apply (θ : ℝ) (hθ1 : θ < 1) (x : ℝ) :
    unitIntervalNormalization θ hθ1 x = ((1 - θ) * x + 1) / 2 := by
  change (1 - θ) / 2 * x + 1 / 2 = _
  ring

/-- Every point in the geometric-series support maps into the unit interval. -/
theorem unitIntervalNormalization_mem_unitInterval {θ : ℝ} (hθ1 : θ < 1) {x : ℝ}
    (hx : x ∈ Icc (-(1 - θ)⁻¹) (1 - θ)⁻¹) :
    unitIntervalNormalization θ hθ1 x ∈ Icc 0 1 := by
  have hg : 0 < 1 - θ := sub_pos.mpr hθ1
  have hc : (1 - θ) * (1 - θ)⁻¹ = 1 := mul_inv_cancel₀ hg.ne'
  have h0 := mul_le_mul_of_nonneg_left hx.1 hg.le
  have h1 := mul_le_mul_of_nonneg_left hx.2 hg.le
  rw [mul_neg, hc] at h0
  rw [hc] at h1
  rw [unitIntervalNormalization_apply]
  constructor <;> linarith

/-- The normalized actual law assigns zero mass outside [0,1]. -/
theorem unitIntervalNormalization_convolution_compl_unitInterval {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ((convolution θ).map (unitIntervalNormalization θ hθ1)) (Icc (0 : ℝ) 1)ᶜ = 0 := by
  rw [Measure.map_apply (unitIntervalNormalization θ hθ1).measurable measurableSet_Icc.compl]
  apply measure_mono_null _ (convolution_compl_interval θ hθ0 hθ1)
  intro x hx hxI
  exact hx (unitIntervalNormalization_mem_unitInterval hθ1 hxI)

/-- Conjugation of each sign digit gives the normalized digit map. -/
theorem unitIntervalNormalization_conjugates_digit {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (b : Bool) (x : ℝ) :
    unitIntervalNormalization θ hθ1 (θ * x + (if b then 1 else -1)) =
      digitMap hθ0 b (unitIntervalNormalization θ hθ1 x) := by
  cases b <;> change (1 - θ) / 2 * (θ * x + _) + 1 / 2 =
    θ * ((1 - θ) / 2 * x + 1 / 2) + _
  all_goals norm_num [digitMap] <;> ring

/-- Actual stationarity of the normalized Bernoulli law for the two normalized similarities. -/
theorem unitIntervalNormalization_convolution_stationary {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    IsStationary hθ0 ((convolution θ).map (unitIntervalNormalization θ hθ1)) := by
  let q := unitIntervalNormalization θ hθ1
  have hplus : (fun x : ℝ => q (θ * x + 1)) = (fun x => digitMap hθ0 true (q x)) := by
    funext x
    exact unitIntervalNormalization_conjugates_digit hθ0 hθ1 true x
  have hminus : (fun x : ℝ => q (θ * x - 1)) = (fun x => digitMap hθ0 false (q x)) := by
    funext x
    simpa [q, sub_eq_add_neg] using unitIntervalNormalization_conjugates_digit hθ0 hθ1 false x
  unfold IsStationary
  rw [Fintype.sum_bool]
  change (convolution θ).map q = _
  conv_lhs => rw [convolution_stationary (by rwa [abs_of_pos hθ0])]
  rw [Measure.map_add _ _ q.measurable, Measure.map_smul, Measure.map_smul]
  rw [Measure.map_map q.measurable (show Measurable (fun x : ℝ => θ * x + 1) by fun_prop),
    Measure.map_map q.measurable (show Measurable (fun x : ℝ => θ * x - 1) by fun_prop),
    Measure.map_map (digitMap hθ0 true).measurable q.measurable,
    Measure.map_map (digitMap hθ0 false).measurable q.measurable]
  simp only [Function.comp_def]
  rw [hplus, hminus]

end LpSelfSimilar.Bernoulli
