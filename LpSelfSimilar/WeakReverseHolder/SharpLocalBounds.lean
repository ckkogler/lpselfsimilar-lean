module

public import LpSelfSimilar.Geometry.Euclidean
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Local density estimates for stopping balls

An upper average controls the volume occupied by a higher superlevel set.
A lower average forces at least half the mass to lie above the lower level.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped ENNReal

namespace LpSelfSimilar

lemma sharp_density_measure_apply {d : ℕ} {f : Space d → ℝ}
    (hf : Integrable f volume) (hf0 : ∀ x, 0 ≤ f x)
    {E : Set (Space d)} (hE : MeasurableSet E) :
    volume.withDensity (fun x => ENNReal.ofReal (f x)) E =
      ENNReal.ofReal (∫ x in E, f x) := by
  rw [withDensity_apply _ hE]
  exact (ofReal_integral_eq_lintegral_ofReal hf.integrableOn
    (ae_of_all _ hf0)).symm

lemma sharp_high_level_small_volume {d : ℕ} {f : Space d → ℝ}
    (hf : Integrable f volume) (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    {A ε t : ℝ} (hA : 0 < A) (ht : 0 < t) (hAε : 2 ≤ A * ε)
    {x : Space d} {r : ℝ}
    (hupper : (∫ y in ball x r, f y) ≤ 2 * t * volume.real (ball x r)) :
    volume ({y | A * t ≤ f y} ∩ ball x r) ≤
      ENNReal.ofReal ε * volume (ball x r) := by
  let E := {y | A * t ≤ f y} ∩ ball x r
  have hE : MeasurableSet E := (measurableSet_le measurable_const hfm).inter
    isOpen_ball.measurableSet
  have hEfin : volume E ≠ ∞ :=
    ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
  have hlo : A * t * volume.real E ≤ ∫ y in E, f y :=
    setIntegral_ge_of_const_le_real hE hEfin (fun y hy => hy.1) hf.integrableOn
  have hmono : (∫ y in E, f y) ≤ ∫ y in ball x r, f y :=
    setIntegral_mono_set hf.integrableOn (ae_of_all _ hf0)
      (ae_of_all _ (fun _ hx => hx.2))
  have hAv : A * volume.real E ≤ 2 * volume.real (ball x r) := by
    apply (mul_le_mul_iff_right₀ ht).mp
    nlinarith [hlo.trans (hmono.trans hupper)]
  have hV : 0 ≤ volume.real (ball x r) := ENNReal.toReal_nonneg
  have hv : volume.real E ≤ ε * volume.real (ball x r) := by
    apply (mul_le_mul_iff_right₀ hA).mp
    nlinarith [mul_le_mul_of_nonneg_right hAε hV]
  have hε : 0 ≤ ε := by nlinarith
  have h := ENNReal.ofReal_le_ofReal hv
  rw [ENNReal.ofReal_mul hε, measureReal_def, measureReal_def,
    ENNReal.ofReal_toReal hEfin, ENNReal.ofReal_toReal measure_ball_ne_top] at h
  exact h

lemma sharp_ball_lower_tail_integral {d : ℕ} {f : Space d → ℝ}
    (hf : Integrable f volume) (hfm : Measurable f)
    {t : ℝ} (ht : 0 ≤ t) {x : Space d} {r : ℝ}
    (hlower : 2 * t * volume.real (ball x r) ≤ ∫ y in ball x r, f y) :
    t * volume.real (ball x r) ≤ ∫ y in ball x r ∩ {z | t ≤ f z}, f y := by
  let S := {z | t ≤ f z}
  have hS : MeasurableSet S := measurableSet_le measurable_const hfm
  have hdiff : MeasurableSet (ball x r \ S) := isOpen_ball.measurableSet.diff hS
  have hfin : volume (ball x r \ S) ≠ ∞ :=
    ((measure_mono sdiff_subset).trans_lt measure_ball_lt_top).ne
  have hle : (∫ y in ball x r \ S, f y) ≤
      volume.real (ball x r \ S) * t := by
    have h := setIntegral_mono_on hf.integrableOn (integrableOn_const hfin) hdiff
      (fun y hy => (lt_of_not_ge hy.2).le)
    simpa only [setIntegral_const, smul_eq_mul] using h
  have hv : volume.real (ball x r \ S) ≤ volume.real (ball x r) :=
    measureReal_mono sdiff_subset measure_ball_ne_top
  have hsplit := integral_inter_add_sdiff hS (hf.integrableOn (s := ball x r))
  have hbound := mul_le_mul_of_nonneg_right hv ht
  change t * volume.real (ball x r) ≤ ∫ y in ball x r ∩ S, f y
  nlinarith

end LpSelfSimilar
