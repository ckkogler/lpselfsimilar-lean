module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Tactic

@[expose] public section

/-!
# Identifying a signed integrable function with a positive measure

Equality against bounded continuous tests first gives the equality of positive
measures mu + f_minus dx = f_plus dx. The positive and negative parts are
mutually singular, so domination forces the negative measure to be zero. Thus
the function is nonnegative almost everywhere and represents the original
measure. Positivity is derived rather than assumed.
-/

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal BoundedContinuousFunction

namespace LpSelfSimilar.Analysis

/-- An integrable signed function has a finite positive-part density measure. -/
theorem isFiniteMeasure_withDensity_ofReal_of_integrable {f : ℝ → ℝ} (hf : Integrable f) :
    IsFiniteMeasure (volume.withDensity (fun x => ENNReal.ofReal (f x))) := by
  have hp : Integrable (fun x => max (f x) 0) := hf.sup (integrable_zero _ _ _)
  apply isFiniteMeasure_withDensity
  have he : (∫⁻ x, ENNReal.ofReal (f x)) = ∫⁻ x, ENNReal.ofReal (max (f x) 0) := by
    apply lintegral_congr
    intro x
    simp
  rw [he, ← ofReal_integral_eq_lintegral_ofReal hp (ae_of_all _ (fun x => le_max_right _ _))]
  exact ENNReal.ofReal_ne_top

/-- The ordinary integral against a positive-part density is exactly the truncated weighted integral. -/
theorem integral_bounded_test_withDensity_ofReal {f : ℝ → ℝ} (hf : Measurable f)
    (v : ℝ →ᵇ ℝ) :
    (∫ x, v x ∂volume.withDensity (fun x => ENNReal.ofReal (f x))) =
      ∫ x, v x * max (f x) 0 := by
  rw [integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
    (ae_of_all _ (fun x => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal', smul_eq_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => mul_comm _ _)

/-- A positive finite measure represented by signed L1 tests has a nonnegative density. -/
theorem ae_nonneg_and_eq_withDensity_of_bounded_tests
    (μ : Measure ℝ) [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hfm : Measurable f) (hfi : Integrable f)
    (htest : ∀ v : ℝ →ᵇ ℝ, (∫ x, v x ∂μ) = ∫ x, v x * f x) :
    (∀ᵐ x, 0 ≤ f x) ∧ μ = volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
  have hnfm : Measurable (fun x => -f x) := hfm.neg
  let νp := volume.withDensity (fun x => ENNReal.ofReal (f x))
  let νm := volume.withDensity (fun x => ENNReal.ofReal (-f x))
  haveI : IsFiniteMeasure νp := isFiniteMeasure_withDensity_ofReal_of_integrable hfi
  haveI : IsFiniteMeasure νm := isFiniteMeasure_withDensity_ofReal_of_integrable hfi.neg
  have hm : Integrable (fun x => max (-f x) 0) := hfi.neg.sup (integrable_zero _ _ _)
  have hparts (x : ℝ) : f x + max (-f x) 0 = max (f x) 0 := by
    simp only [max_def]
    split_ifs <;> linarith
  have he : μ + νm = νp := by
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro v
    rw [integral_add_measure (v.integrable μ) (v.integrable νm)]
    change (∫ x, v x ∂μ) + (∫ x, v x ∂volume.withDensity (fun x => ENNReal.ofReal (-f x))) =
      ∫ x, v x ∂volume.withDensity (fun x => ENNReal.ofReal (f x))
    rw [integral_bounded_test_withDensity_ofReal hnfm v,
      integral_bounded_test_withDensity_ofReal hfm v, htest v]
    have hvi := hfi.bdd_mul v.continuous.aestronglyMeasurable
      (ae_of_all _ (fun x => v.norm_coe_le_norm x))
    have hvmi := hm.bdd_mul v.continuous.aestronglyMeasurable
      (ae_of_all _ (fun x => v.norm_coe_le_norm x))
    rw [← integral_add hvi hvmi]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by
      change v x * f x + v x * max (-f x) 0 = v x * max (f x) 0
      rw [← mul_add, hparts])
  have hs : νp ⟂ₘ νm := withDensity_ofReal_mutuallySingular hfm
  have hle : νm ≤ νp := by
    rw [← he]
    intro s
    rw [Measure.add_apply]
    exact le_add_of_nonneg_left (show 0 ≤ μ s from zero_le)
  have hz : νm = 0 := (MutuallySingular.self_iff νm).mp (hs.mono hle le_rfl)
  have hneg : (fun x => ENNReal.ofReal (-f x)) =ᵐ[volume] 0 :=
    (withDensity_eq_zero_iff hnfm.ennreal_ofReal.aemeasurable).mp hz
  refine ⟨?_, ?_⟩
  · filter_upwards [hneg] with x hx
    have hn : -f x ≤ 0 := ENNReal.ofReal_eq_zero.mp hx
    linarith
  · simpa only [hz, add_zero] using he

end LpSelfSimilar.Analysis
