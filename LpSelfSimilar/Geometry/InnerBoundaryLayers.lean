module

public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# Vanishing inner boundary layers of open sets

For an open set with nonempty complement, its points have positive distance
from that complement. Consequently the mass, for any finite measure, of points
within a geometrically shrinking distance from the complement tends to zero.
This supplies the residual estimate for finite-horizon concentration stopping.
-/

open MeasureTheory Set Metric Filter
open scoped Topology

namespace LpSelfSimilar.Geometry

/-- Points inside E at distance at most delta from its complement. -/
def innerBoundaryLayer (E : Set ℝ) (δ : ℝ) : Set ℝ :=
  E ∩ {x | infDist x Eᶜ ≤ δ}

/-- Every inner layer of a measurable set is measurable. -/
theorem measurableSet_innerBoundaryLayer {E : Set ℝ} (hE : MeasurableSet E) (δ : ℝ) :
    MeasurableSet (innerBoundaryLayer E δ) :=
  hE.inter (isClosed_le (continuous_infDist_pt Eᶜ) continuous_const).measurableSet

/-- Decreasing the distance threshold shrinks the inner layer. -/
theorem innerBoundaryLayer_mono (E : Set ℝ) {a b : ℝ} (hab : a ≤ b) :
    innerBoundaryLayer E a ⊆ innerBoundaryLayer E b := by
  rintro x ⟨hx, hd⟩
  exact ⟨hx, hd.trans hab⟩

/-- A nearby point outside E certifies membership in its inner boundary layer. -/
theorem mem_innerBoundaryLayer_of_dist_le {E : Set ℝ} {x y δ : ℝ}
    (hx : x ∈ E) (hy : y ∉ E) (hd : dist x y ≤ δ) :
    x ∈ innerBoundaryLayer E δ :=
  ⟨hx, (infDist_le_dist_of_mem (show y ∈ Eᶜ from hy)).trans hd⟩

/-- Geometrically shrinking inner layers have empty intersection for an open set. -/
theorem iInter_innerBoundaryLayer_pow_eq_empty {E : Set ℝ} (hE : IsOpen E)
    (hne : Eᶜ.Nonempty) {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1) :
    (⋂ n : ℕ, innerBoundaryLayer E (θ ^ n)) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hall := mem_iInter.mp hx
  have hxE := (hall 0).1
  have hpos : 0 < infDist x Eᶜ :=
    (hE.isClosed_compl.notMem_iff_infDist_pos hne).mp (by simpa using hxE)
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one hθ hθ1
  have hle : infDist x Eᶜ ≤ 0 :=
    ge_of_tendsto hlim (Filter.Eventually.of_forall (fun n => (hall n).2))
  exact (not_lt_of_ge hle) hpos

/-- For every finite measure, the mass of shrinking inner layers of an open set tends to zero. -/
theorem tendsto_measure_innerBoundaryLayer_pow (μ : Measure ℝ) [IsFiniteMeasure μ]
    {E : Set ℝ} (hE : IsOpen E) (hne : Eᶜ.Nonempty)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1) :
    Tendsto (fun n : ℕ => μ (innerBoundaryLayer E (θ ^ n))) atTop (𝓝 0) := by
  have hm : Antitone (fun n : ℕ => innerBoundaryLayer E (θ ^ n)) := by
    intro m n hmn
    exact innerBoundaryLayer_mono E (pow_le_pow_of_le_one hθ hθ1.le hmn)
  have ht := tendsto_measure_iInter_atTop
    (μ := μ) (fun n => (measurableSet_innerBoundaryLayer hE.measurableSet (θ ^ n)).nullMeasurableSet)
    hm ⟨0, measure_ne_top μ _⟩
  simpa only [iInter_innerBoundaryLayer_pow_eq_empty hE hne hθ hθ1, measure_empty,
    Function.comp_def] using ht

end LpSelfSimilar.Geometry
