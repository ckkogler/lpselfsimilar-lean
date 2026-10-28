module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic

@[expose] public section

/-!
# Prescribing the measure of a real measurable subset

For a finite measure on the real line with null singletons, the mass of a
moving half-line is continuous. Its limits at the two ends of the line and
the intermediate value theorem give subsets of every intermediate mass.
Applying this to restricted Lebesgue volume supplies exact trimming, including
both endpoint masses, without an assumed abstract atomless splitting theorem.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace LpSelfSimilar.Analysis

/-- The real-valued cumulative mass of a finite real measure with null singletons is continuous. -/
theorem continuous_real_measure_Iic (μ : Measure ℝ) [IsFiniteMeasure μ]
    [NullSingletonClass μ] : Continuous (fun x : ℝ => (μ (Iic x)).toReal) := by
  have hconst : Integrable (fun _ : ℝ => (1 : ℝ)) μ := integrable_const 1
  have hcont : Continuous (fun x : ℝ => ∫ y in Iic x, (1 : ℝ) ∂μ) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact ((hconst.integrableOn (s := Iic (x + 1))).continuousOn_Iic_primitive_Iic
      x (by simp)).continuousAt (Iic_mem_nhds (by linarith))
  simpa [integral_const, measureReal_def] using hcont

/-- Cumulative mass tends to zero at minus infinity for a finite real measure. -/
theorem tendsto_measure_Iic_atBot_zero (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Tendsto (fun x : ℝ => μ (Iic x)) atBot (𝓝 0) := by
  have h := tendsto_measure_iInter_atBot (μ := μ)
    (fun x : ℝ => measurableSet_Iic.nullMeasurableSet) monotone_Iic
    ⟨0, measure_ne_top μ _⟩
  have hinter : (⋂ x : ℝ, Iic x) = ∅ := by
    ext y
    simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false]
    intro hy
    have := hy (y - 1)
    linarith
  simpa only [Function.comp_def, hinter, measure_empty] using h

/-- Every strictly intermediate mass is attained by a half-line. -/
theorem exists_measure_Iic_eq (μ : Measure ℝ) [IsFiniteMeasure μ]
    [NullSingletonClass μ] {t : ℝ} (ht : 0 < t) (htμ : t < (μ univ).toReal) :
    ∃ x : ℝ, μ (Iic x) = ENNReal.ofReal t := by
  have hlo : Tendsto (fun x : ℝ => (μ (Iic x)).toReal) atBot (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (tendsto_measure_Iic_atBot_zero μ)
  have hhi := (ENNReal.tendsto_toReal (measure_ne_top μ univ)).comp
    (tendsto_measure_Iic_atTop μ)
  obtain ⟨x, hx⟩ := intermediate_value_univ₂_eventually₂
    (continuous_real_measure_Iic μ) continuous_const
    ((hlo.eventually (gt_mem_nhds ht)).mono fun _ h => h.le)
    ((hhi.eventually (lt_mem_nhds htμ)).mono fun _ h => h.le)
  exact ⟨x, by rw [← hx, ENNReal.ofReal_toReal (measure_ne_top μ _)]⟩

/-- A finite measurable real set has a measurable subset of any prescribed smaller mass. -/
theorem exists_measurable_subset_measure_eq (μ : Measure ℝ) [NullSingletonClass μ]
    {E : Set ℝ} (hE : MeasurableSet E) (hfin : μ E ≠ ∞)
    {t : ℝ≥0∞} (ht : t ≤ μ E) :
    ∃ A : Set ℝ, MeasurableSet A ∧ A ⊆ E ∧ μ A = t := by
  by_cases ht0 : t = 0
  · exact ⟨∅, MeasurableSet.empty, empty_subset _, by simp [ht0]⟩
  by_cases hte : t = μ E
  · exact ⟨E, hE, subset_rfl, hte.symm⟩
  have httop : t ≠ ∞ := ne_top_of_le_ne_top hfin ht
  have htlt : t < μ E := lt_of_le_of_ne ht hte
  let ν := μ.restrict E
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hfin
  obtain ⟨x, hx⟩ := exists_measure_Iic_eq ν
    (ENNReal.toReal_pos ht0 httop)
    (by simpa [ν] using (ENNReal.toReal_lt_toReal httop hfin).mpr htlt)
  refine ⟨Iic x ∩ E, measurableSet_Iic.inter hE, inter_subset_right, ?_⟩
  simpa [ν, Measure.restrict_apply, ENNReal.ofReal_toReal httop] using hx

/-- Exact measurable trimming for Lebesgue volume on the real line. -/
theorem exists_measurable_subset_volume_eq {E : Set ℝ} (hE : MeasurableSet E)
    (hfin : volume E ≠ ∞) {t : ℝ≥0∞} (ht : t ≤ volume E) :
    ∃ A : Set ℝ, MeasurableSet A ∧ A ⊆ E ∧ volume A = t :=
  exists_measurable_subset_measure_eq volume hE hfin ht

end LpSelfSimilar.Analysis
