module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.Tactic

@[expose] public section

/-!
Finite absolutely continuous measures admit a nonnegative, integrable real
Radon–Nikodym density and a uniform small-volume estimate. These facts do not
require a Euclidean space or compact support.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LpSelfSimilar

variable {X : Type*} [MeasurableSpace X]

/-- The everywhere nonnegative real representative of the Radon–Nikodym derivative. -/
noncomputable def density (ν μ : Measure X) (x : X) : ℝ := (ν.rnDeriv μ x).toReal

lemma density_nonneg (ν μ : Measure X) (x : X) : 0 ≤ density ν μ x := ENNReal.toReal_nonneg

lemma integrable_density (ν μ : Measure X) [IsFiniteMeasure ν] :
    Integrable (density ν μ) μ := by
  exact integrable_toReal_of_lintegral_ne_top (Measure.measurable_rnDeriv ν μ).aemeasurable
    (Measure.lintegral_rnDeriv_lt_top ν μ).ne

lemma withDensity_density (ν μ : Measure X) [IsFiniteMeasure ν] [SigmaFinite μ]
    (hac : ν ≪ μ) : μ.withDensity (fun x ↦ ENNReal.ofReal (density ν μ x)) = ν := by
  calc
    μ.withDensity (fun x ↦ ENNReal.ofReal (density ν μ x)) = μ.withDensity (ν.rnDeriv μ) := by
      apply withDensity_congr_ae
      filter_upwards [Measure.rnDeriv_lt_top ν μ] with x hx
      exact ENNReal.ofReal_toReal hx.ne
    _ = ν := Measure.withDensity_rnDeriv_eq ν μ hac

/-- Absolute continuity is uniform on measurable sets when the upper measure is finite. -/
lemma exists_pos_measure_le_of_measure_le (ν μ : Measure X)
    [IsFiniteMeasure ν] [SigmaFinite μ] (hac : ν ≪ μ) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ E, MeasurableSet E →
      μ E ≤ ENNReal.ofReal δ → ν E ≤ ENNReal.ofReal η := by
  obtain ⟨δ, hδ, hbound⟩ := exists_pos_setLIntegral_lt_of_measure_lt
    (Measure.lintegral_rnDeriv_lt_top ν μ).ne (ENNReal.ofReal_pos.mpr hη).ne'
  obtain ⟨a, _, ha, haδ⟩ := ENNReal.lt_iff_exists_real_btwn.mp hδ
  refine ⟨a, ENNReal.ofReal_pos.mp ha, fun E hE hvol ↦ ?_⟩
  rw [← Measure.withDensity_rnDeriv_eq ν μ hac, withDensity_apply _ hE]
  exact (hbound E (hvol.trans_lt haδ)).le

end LpSelfSimilar
