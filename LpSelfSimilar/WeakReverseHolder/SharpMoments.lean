module

public import LpSelfSimilar.Analysis.GeometricMoments
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Integrability from a density-tail contraction

A geometric contraction of the mass of the density's superlevel sets gives the
full moment whenever its weighted geometric ratio is strictly below one.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace LpSelfSimilar

theorem sharp_memLp_of_density_tail_contraction {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f : X → ℝ} (hfm : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f μ)
    {A β p T : ℝ} (hA : 1 < A) (hT : 0 < T) (hp : 1 < p)
    (hratio : β * A ^ (p - 1) < 1)
    (hstep : ∀ t : ℝ, T ≤ t →
      μ.withDensity (fun x => ENNReal.ofReal (f x)) {x | A * t ≤ f x} ≤
        ENNReal.ofReal β * μ.withDensity (fun x => ENNReal.ofReal (f x)) {x | t ≤ f x}) :
    MemLp f (ENNReal.ofReal p) μ := by
  let ν := μ.withDensity (fun x => ENNReal.ofReal (f x))
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity hf.lintegral_lt_top.ne
  let S : ℕ → Set X := fun n => {x | T * A ^ n ≤ f x}
  have hS (n : ℕ) : MeasurableSet (S n) := measurableSet_le measurable_const hfm
  have hmass (n : ℕ) : ν (S n) ≤ ENNReal.ofReal β ^ n * ν univ := by
    induction n with
    | zero => simpa using (measure_mono (subset_univ (S 0)) : ν (S 0) ≤ ν univ)
    | succ n ih =>
      have hTn : T ≤ T * A ^ n := by
        exact le_mul_of_one_le_right hT.le (one_le_pow₀ hA.le)
      have h := hstep (T * A ^ n) hTn
      have he : A * (T * A ^ n) = T * A ^ (n + 1) := by rw [pow_succ]; ring
      change ν {x | A * (T * A ^ n) ≤ f x} ≤ ENNReal.ofReal β * ν (S n) at h
      rw [he] at h
      calc
        ν (S (n + 1)) ≤ ENNReal.ofReal β * ν (S n) := h
        _ ≤ ENNReal.ofReal β * (ENNReal.ofReal β ^ n * ν univ) := by gcongr
        _ = ENNReal.ofReal β ^ (n + 1) * ν univ := by rw [pow_succ]; ac_rfl
  have hmoment : ∫⁻ x, ENNReal.ofReal (f x) ^ (p - 1) ∂ν < ∞ :=
    lintegral_rpow_lt_top_of_geometric_tails ν f hT hA (by linarith) hratio
      S hS (fun _ _ hx => hx) hmass
  have hfmeas := hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  rw [show ν = μ.withDensity (fun x => ENNReal.ofReal (f x)) from rfl,
    lintegral_withDensity_eq_lintegral_mul₀ hfmeas (hfmeas.pow_const (p - 1))] at hmoment
  refine (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (ENNReal.ofReal_pos.mpr (by linarith : 0 < p)).ne' ENNReal.ofReal_ne_top
    hf.aestronglyMeasurable).2 ?_
  rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ p)]
  convert hmoment using 1
  apply lintegral_congr
  intro x
  rw [Real.enorm_of_nonneg (hf0 x)]
  change ENNReal.ofReal (f x) ^ p =
    ENNReal.ofReal (f x) * ENNReal.ofReal (f x) ^ (p - 1)
  conv_lhs => rw [show p = 1 + (p - 1) by ring]
  rw [ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by linarith), ENNReal.rpow_one]

end LpSelfSimilar
