module

public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

@[expose] public section

/-!
Conversion between real nonnegative densities and their extended-valued power
integrals. Finite mass makes the toReal representative valid almost everywhere.
-/

open MeasureTheory
open scoped ENNReal

namespace LpSelfSimilar

lemma memLp_nonneg_iff_power_integral {f : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hf : AEStronglyMeasurable f volume) (hn : ∀ x, 0 ≤ f x) :
    MemLp f (ENNReal.ofReal p) volume ↔
      (∫⁻ x, ENNReal.ofReal (f x) ^ p) < ∞ := by
  rw [MemLp, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by positivity : ENNReal.ofReal p ≠ 0) ENNReal.ofReal_ne_top hf]
  simp only [ENNReal.toReal_ofReal hp.le, Real.enorm_eq_ofReal (hn _)]

lemma ennreal_toReal_ae {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    (hfin : (∫⁻ x, f x) < ∞) :
    (fun x ↦ ENNReal.ofReal (f x).toReal) =ᵐ[volume] f := by
  filter_upwards [ae_lt_top hf hfin.ne] with x hx
  exact ENNReal.ofReal_toReal hx.ne

lemma integrable_ennreal_toReal {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    (hfin : (∫⁻ x, f x) < ∞) : Integrable (fun x ↦ (f x).toReal) volume := by
  rw [← memLp_one_iff_integrable]
  rw [← ENNReal.ofReal_one]
  apply (memLp_nonneg_iff_power_integral (by norm_num : (0 : ℝ) < 1) hf.ennreal_toReal.aestronglyMeasurable
    (fun _ ↦ ENNReal.toReal_nonneg)).mpr
  simpa only [ENNReal.rpow_one] using
    (lintegral_congr_ae (ennreal_toReal_ae hf hfin)).trans_lt hfin

lemma memLp_ennreal_toReal {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    {p : ℝ} (hp : 0 < p) (hfin : (∫⁻ x, f x ^ p) < ∞) :
    MemLp (fun x ↦ (f x).toReal) (ENNReal.ofReal p) volume := by
  apply (memLp_nonneg_iff_power_integral hp hf.ennreal_toReal.aestronglyMeasurable
    (fun _ ↦ ENNReal.toReal_nonneg)).mpr
  apply lt_of_le_of_lt (lintegral_mono (fun x ↦ ?_)) hfin
  exact ENNReal.rpow_le_rpow ENNReal.ofReal_toReal_le hp.le

end LpSelfSimilar
