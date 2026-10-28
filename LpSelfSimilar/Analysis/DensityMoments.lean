module

public import LpSelfSimilar.Analysis.GeometricMoments
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

@[expose] public section

/-! From expansion of the measure with density `f` to membership in `Lᵖ`. -/

open MeasureTheory Set
open scoped ENNReal

namespace LpSelfSimilar

lemma memLp_of_measure_expansion {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f : X → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f μ)
    {A β p T : ℝ} (hA : 1 < A) (hT : 0 < T) (hp : 1 < p)
    (hratio : β * A ^ (p - 1) < 1)
    (hstep : ∀ E, MeasurableSet E → ENNReal.ofReal A * μ E ≤ ENNReal.ofReal T →
      ∃ Ω, MeasurableSet Ω ∧ μ Ω ≤ ENNReal.ofReal A * μ E ∧
        μ.withDensity (fun x ↦ ENNReal.ofReal (f x)) E ≤
          ENNReal.ofReal β * μ.withDensity (fun x ↦ ENNReal.ofReal (f x)) Ω) :
    MemLp f (ENNReal.ofReal p) μ := by
  let ν := μ.withDensity (fun x ↦ ENNReal.ofReal (f x))
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity hf.lintegral_lt_top.ne
  have hν : ν univ = ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
    simp [ν, withDensity_apply]
  let M := (ν univ).toReal
  let L := (M + 1) / T
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hL : 0 < L := div_pos (by positivity) hT
  have hLT : L * T = M + 1 := div_mul_cancel₀ _ hT.ne'
  have hmassL : ν univ ≤ ENNReal.ofReal L * ENNReal.ofReal T := by
    rw [← ENNReal.ofReal_mul hL.le, hLT]
    calc
      ν univ = ENNReal.ofReal M := (ENNReal.ofReal_toReal (measure_ne_top ν univ)).symm
      _ ≤ ENNReal.ofReal (M + 1) := ENNReal.ofReal_le_ofReal (by linarith)
  let S : ℕ → Set X := fun n ↦ toMeasurable μ
    {x | ENNReal.ofReal (L * A ^ n) ≤ ENNReal.ofReal (f x)}
  have hS : ∀ n, MeasurableSet (S n) := fun _ ↦ measurableSet_toMeasurable _ _
  have hcover (n : ℕ) (x : X) (hx : L * A ^ n ≤ f x) : x ∈ S n :=
    subset_toMeasurable μ _ (ENNReal.ofReal_le_ofReal hx)
  have hA0 : 0 < A := lt_trans zero_lt_one hA
  have hvol (n : ℕ) : ENNReal.ofReal A ^ n * μ (S n) ≤ ENNReal.ofReal T := by
    have hm : ENNReal.ofReal (L * A ^ n) * μ (S n) ≤ ν univ := by
      rw [show μ (S n) = μ {x | ENNReal.ofReal (L * A ^ n) ≤ ENNReal.ofReal (f x)} by
        exact measure_toMeasurable _, hν]
      exact mul_meas_ge_le_lintegral₀ hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal _
    have hm' := hm.trans hmassL
    rw [ENNReal.ofReal_mul hL.le, ENNReal.ofReal_pow hA0.le, mul_assoc] at hm'
    exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hL).ne'
      ENNReal.ofReal_ne_top).mp hm'
  have hmass (n : ℕ) : ν (S n) ≤ ENNReal.ofReal β ^ n * ν univ :=
    measure_le_pow_mul_of_expansion μ ν (by simpa using ENNReal.ofReal_le_ofReal hA.le)
      hstep n (hS n) (hvol n)
  have hmoment : ∫⁻ x, ENNReal.ofReal (f x) ^ (p - 1) ∂ν < ∞ :=
    lintegral_rpow_lt_top_of_geometric_tails ν f hL hA (by linarith)
      hratio S hS hcover hmass
  have hfmeas := hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  rw [show ν = μ.withDensity (fun x ↦ ENNReal.ofReal (f x)) from rfl,
    lintegral_withDensity_eq_lintegral_mul₀ hfmeas (hfmeas.pow_const (p - 1))] at hmoment
  refine (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (ENNReal.ofReal_pos.mpr (by linarith : 0 < p)).ne' ENNReal.ofReal_ne_top
    hf.aestronglyMeasurable).2 ?_
  rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ p)]
  convert hmoment using 1
  apply lintegral_congr
  intro x
  rw [Real.enorm_of_nonneg (hf0 x)]
  change ENNReal.ofReal (f x) ^ p = ENNReal.ofReal (f x) * ENNReal.ofReal (f x) ^ (p - 1)
  conv_lhs => rw [show p = 1 + (p - 1) by ring]
  rw [ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by linarith), ENNReal.rpow_one]

end LpSelfSimilar
