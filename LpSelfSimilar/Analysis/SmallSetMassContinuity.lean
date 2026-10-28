module

public import LpSelfSimilar.Analysis.SmallSetMass
public import LpSelfSimilar.Analysis.RealMeasureSplitting

@[expose] public section

/-!
# Continuity of the small-set mass modulus on the real line

Exact volume trimming makes the modulus subadditive. Uniform absolute
continuity then controls the change when its volume budget changes, giving
continuity, including at zero. This is the approximation step that allows
an open-set recurrence to retain its exact volume multiplier.
-/

open MeasureTheory Set
open scoped ENNReal Topology

namespace LpSelfSimilar.Analysis

/-- The mass modulus is finite when the measured mass is finite. -/
theorem smallSetMass_ne_top (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ≥0∞) :
    smallSetMass μ volume t ≠ ∞ :=
  ne_top_of_le_ne_top (measure_ne_top μ univ)
    (smallSetMass_le μ volume fun E _ _ => measure_mono (subset_univ E))

/-- Splitting an admissible set proves subadditivity in its nonnegative volume budget. -/
theorem smallSetMass_add_le (μ : Measure ℝ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    smallSetMass μ volume (ENNReal.ofReal (s + t)) ≤
      smallSetMass μ volume (ENNReal.ofReal s) +
      smallSetMass μ volume (ENNReal.ofReal t) := by
  apply smallSetMass_le μ volume
  intro E hE hv
  by_cases hEs : volume E ≤ ENNReal.ofReal s
  · exact (measure_le_smallSetMass μ volume hE hEs).trans le_self_add
  obtain ⟨A, hA, hAE, hAv⟩ := exists_measurable_subset_volume_eq hE
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hv) (le_of_not_ge hEs)
  have hdiff : volume (E \ A) ≤ ENNReal.ofReal t := by
    rw [measure_sdiff hAE hA.nullMeasurableSet (by rw [hAv]; exact ENNReal.ofReal_ne_top), hAv]
    apply tsub_le_iff_right.mpr
    simpa only [ENNReal.ofReal_add hs ht, add_comm] using hv
  have hmass : μ E = μ (E \ A) + μ A := by
    simpa only [inter_eq_right.mpr hAE] using (measure_sdiff_add_inter (μ := μ) E hA).symm
  rw [hmass, add_comm]
  exact add_le_add (measure_le_smallSetMass μ volume hA hAv.le)
    (measure_le_smallSetMass μ volume (hE.diff hA) hdiff)

/-- The real-valued modulus is subadditive for a finite measure. -/
theorem smallSetMass_toReal_add_le (μ : Measure ℝ) [IsFiniteMeasure μ]
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (smallSetMass μ volume (ENNReal.ofReal (s + t))).toReal ≤
      (smallSetMass μ volume (ENNReal.ofReal s)).toReal +
      (smallSetMass μ volume (ENNReal.ofReal t)).toReal := by
  have h := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨smallSetMass_ne_top μ _, smallSetMass_ne_top μ _⟩)
    (smallSetMass_add_le μ hs ht)
  simpa only [ENNReal.toReal_add (smallSetMass_ne_top μ _) (smallSetMass_ne_top μ _)] using h

/-- Changes in the volume budget are controlled by the modulus at the budget difference. -/
theorem abs_smallSetMass_toReal_sub_le (μ : Measure ℝ) [IsFiniteMeasure μ]
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |(smallSetMass μ volume (ENNReal.ofReal s)).toReal -
      (smallSetMass μ volume (ENNReal.ofReal t)).toReal| ≤
      (smallSetMass μ volume (ENNReal.ofReal |s - t|)).toReal := by
  have hmono {a b : ℝ} (h : a ≤ b) :
      (smallSetMass μ volume (ENNReal.ofReal a)).toReal ≤
      (smallSetMass μ volume (ENNReal.ofReal b)).toReal :=
    ENNReal.toReal_mono (smallSetMass_ne_top μ _)
      (smallSetMass_mono μ volume (ENNReal.ofReal_le_ofReal h))
  apply abs_le.mpr
  constructor
  · have h := (hmono (show t ≤ s + |s - t| by linarith [neg_abs_le (s - t)])).trans
      (smallSetMass_toReal_add_le μ hs (abs_nonneg _))
    linarith
  · have h := (hmono (show s ≤ t + |s - t| by linarith [le_abs_self (s - t)])).trans
      (smallSetMass_toReal_add_le μ ht (abs_nonneg _))
    linarith

/-- Uniform absolute continuity gives continuity of the real-valued mass modulus. -/
theorem continuousOn_smallSetMass_toReal (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hac : μ ≪ volume) :
    ContinuousOn (fun t : ℝ => (smallSetMass μ volume (ENNReal.ofReal t)).toReal) (Ici 0) := by
  intro t ht
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := exists_pos_smallSetMass_le μ volume hac (half_pos hε)
  refine ⟨δ, hδ, ?_⟩
  intro s hs hst
  have hsmall : (smallSetMass μ volume (ENNReal.ofReal |s - t|)).toReal ≤ ε / 2 := by
    have h := (smallSetMass_mono μ volume
      (ENNReal.ofReal_le_ofReal (show |s - t| ≤ δ by simpa only [Real.dist_eq] using hst.le))).trans hbound
    simpa only [ENNReal.toReal_ofReal (half_pos hε).le] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [Real.dist_eq]
  exact ((abs_smallSetMass_toReal_sub_le μ hs ht).trans hsmall).trans_lt (half_lt_self hε)

/-- The original extended-real mass modulus is continuous on nonnegative real budgets. -/
theorem continuousOn_smallSetMass (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hac : μ ≪ volume) :
    ContinuousOn (fun t : ℝ => smallSetMass μ volume (ENNReal.ofReal t)) (Ici 0) := by
  have h := ENNReal.continuous_ofReal.comp_continuousOn (continuousOn_smallSetMass_toReal μ hac)
  simpa only [Function.comp_def, ENNReal.ofReal_toReal (smallSetMass_ne_top μ _)] using h

end LpSelfSimilar.Analysis
