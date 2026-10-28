module

public import LpSelfSimilar.Analysis.SmallSetMass
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Tactic

@[expose] public section

/-!
# Extending an open-set mass recurrence by outer approximation

Any strict enlargement of the volume multiplier allows the open-set estimate
to pass to all measurable sets, away from the endpoint of the volume budget.
No continuity assumption on the small-set modulus is used. A strict analytic
margin, such as beta^2*D0<1, allows this enlargement without changing the final
strict hypothesis in the concentration criterion.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LpSelfSimilar.Analysis

/-- An open-set recurrence yields a measurable-set modulus recurrence with any larger multiplier. -/
theorem smallSetMass_recurrence_of_open_sets (μ : Measure ℝ) {r D₀ D : ℝ}
    (hD₀ : 0 < D₀) (hD : D₀ < D) (β : ℝ≥0∞)
    (hopen : ∀ U : Set ℝ, IsOpen U → volume U ≤ ENNReal.ofReal r →
      μ U ≤ β * smallSetMass μ volume (ENNReal.ofReal D₀ * volume U))
    {t : ℝ} (ht : 0 < t) (htr : t < r) :
    smallSetMass μ volume (ENNReal.ofReal t) ≤
      β * smallSetMass μ volume (ENNReal.ofReal (D * t)) := by
  have hratio : 1 < D / D₀ := (lt_div_iff₀ hD₀).mpr (by simpa using hD)
  have htu : t < min r (D / D₀ * t) := lt_min htr (by nlinarith)
  have hu : 0 < min r (D / D₀ * t) := ht.trans htu
  apply smallSetMass_le μ volume
  intro E hE hv
  obtain ⟨U, hEU, hU, hUv⟩ := E.exists_isOpen_lt_of_lt
    (μ := volume) (ENNReal.ofReal (min r (D / D₀ * t)))
    (hv.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hu).mpr htu))
  have hUr : volume U ≤ ENNReal.ofReal r :=
    hUv.le.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _))
  have hvol : ENNReal.ofReal D₀ * volume U ≤ ENNReal.ofReal (D * t) := by
    calc
      _ ≤ ENNReal.ofReal D₀ * ENNReal.ofReal (min r (D / D₀ * t)) :=
        mul_le_mul' le_rfl hUv.le
      _ = ENNReal.ofReal (D₀ * min r (D / D₀ * t)) := (ENNReal.ofReal_mul hD₀.le).symm
      _ ≤ ENNReal.ofReal (D₀ * (D / D₀ * t)) := ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (min_le_right _ _) hD₀.le)
      _ = ENNReal.ofReal (D * t) := by congr 1; field_simp [hD₀.ne']
  exact (measure_mono hEU).trans ((hopen U hU hUr).trans
    (mul_le_mul' le_rfl (smallSetMass_mono μ volume hvol)))

end LpSelfSimilar.Analysis
