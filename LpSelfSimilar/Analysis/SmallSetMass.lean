module

public import LpSelfSimilar.Analysis.AbsoluteContinuity

@[expose] public section

/-!
The mass modulus `ω(t)` from page 3: the largest mass of a measurable set
whose reference measure is at most `t`. Uniform absolute continuity controls
this modulus near zero.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LpSelfSimilar

variable {X : Type*} [MeasurableSpace X]

/-- The measurable-set version of the paper's modulus `ω`. -/
noncomputable def smallSetMass (ν μ : Measure X) (t : ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ E : Set X, ⨆ (_ : MeasurableSet E), ⨆ (_ : μ E ≤ t), ν E

lemma measure_le_smallSetMass (ν μ : Measure X) {t : ℝ≥0∞}
    {E : Set X} (hE : MeasurableSet E) (hvol : μ E ≤ t) : ν E ≤ smallSetMass ν μ t :=
  le_iSup_of_le E (le_iSup_of_le hE (le_iSup_of_le hvol le_rfl))

lemma smallSetMass_le (ν μ : Measure X) {t b : ℝ≥0∞}
    (hbound : ∀ E, MeasurableSet E → μ E ≤ t → ν E ≤ b) : smallSetMass ν μ t ≤ b :=
  iSup_le fun E ↦ iSup_le fun hE ↦ iSup_le fun hvol ↦ hbound E hE hvol

lemma smallSetMass_mono (ν μ : Measure X) {s t : ℝ≥0∞} (hst : s ≤ t) :
    smallSetMass ν μ s ≤ smallSetMass ν μ t :=
  smallSetMass_le ν μ fun _ hE hvol ↦ measure_le_smallSetMass ν μ hE (hvol.trans hst)

/-- The epsilon-delta form of `ω(t) → 0`, sufficient for the small-set criterion. -/
lemma exists_pos_smallSetMass_le (ν μ : Measure X) [IsFiniteMeasure ν] [SigmaFinite μ]
    (hac : ν ≪ μ) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ smallSetMass ν μ (ENNReal.ofReal δ) ≤ ENNReal.ofReal η := by
  obtain ⟨δ, hδ, hbound⟩ := exists_pos_measure_le_of_measure_le ν μ hac hη
  exact ⟨δ, hδ, smallSetMass_le ν μ hbound⟩

end LpSelfSimilar
