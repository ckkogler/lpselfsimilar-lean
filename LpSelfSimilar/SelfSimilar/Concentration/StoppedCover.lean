module

public import LpSelfSimilar.SelfSimilar.Concentration.StoppedGeometry
public import LpSelfSimilar.Analysis.SmallSetMass

@[expose] public section

/-!
# The finite cover formed by concentrated stopped intervals

Only terminal intervals that have passed the concentration test enter the
cover. Its Lebesgue volume has the exact factor three from the greedy interval
selection. A concentrated cylinder assigns its entire conditional probability
to this cover, since the original measure is supported on the unit interval.
-/

open MeasureTheory Set
open LpSelfSimilar.Geometry
open scoped ENNReal Classical

namespace LpSelfSimilar.SelfSimilar.Concentration

/-- Terminal binary words whose stopped interval passes the concentration test. -/
noncomputable def concentratedWords {θ : ℝ} (hθ : 0 < θ) (E : Set ℝ) (r : ℝ) (n : ℕ) :
    Finset (Word Bool n) :=
  Finset.univ.filter (fun w => IsConcentrated E r
    (stoppedMap hθ E r n PositiveAffine.identity w))

/-- The finite union of the concentrated terminal intervals. -/
noncomputable def stoppedCover {θ : ℝ} (hθ : 0 < θ) (E : Set ℝ) (r : ℝ) (n : ℕ) : Set ℝ :=
  ⋃ w ∈ concentratedWords hθ E r n, (stoppedMap hθ E r n PositiveAffine.identity w).interval

/-- The finite stopped cover is measurable. -/
theorem measurableSet_stoppedCover {θ : ℝ} (hθ : 0 < θ) (E : Set ℝ) (r : ℝ) (n : ℕ) :
    MeasurableSet (stoppedCover hθ E r n) := by
  unfold stoppedCover
  exact MeasurableSet.biUnion (concentratedWords hθ E r n).finite_toSet.countable
    (fun _ _ => measurableSet_Icc)

/-- Every concentrated terminal interval is contained in the stopped cover. -/
theorem stopped_interval_subset_cover {θ : ℝ} (hθ : 0 < θ) (E : Set ℝ) (r : ℝ)
    (n : ℕ) (w : Word Bool n)
    (hc : IsConcentrated E r (stoppedMap hθ E r n PositiveAffine.identity w)) :
    (stoppedMap hθ E r n PositiveAffine.identity w).interval ⊆ stoppedCover hθ E r n := by
  have hw : w ∈ concentratedWords hθ E r n := by
    simpa only [concentratedWords, Finset.mem_filter, Finset.mem_univ, true_and] using hc
  exact subset_iUnion₂_of_subset w hw subset_rfl

/-- The cover has volume at most 3/r times the volume of E. -/
theorem volume_stoppedCover_le {θ r : ℝ} (hθ : 0 < θ) (hr : 0 < r)
    {E : Set ℝ} (hE : MeasurableSet E) (n : ℕ) :
    volume (stoppedCover hθ E r n) ≤ ENNReal.ofReal (3 / r) * volume E := by
  apply volume_union_concentrated_affineIntervals_le _ _ hE hr
  intro w hw
  exact (Finset.mem_filter.mp hw).2

/-- A concentrated terminal cylinder has conditional probability one of lying in the cover. -/
theorem preimage_stoppedCover_mass_eq_one {θ : ℝ} (hθ : 0 < θ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hsupp : μ (Icc (0 : ℝ) 1)ᶜ = 0)
    (E : Set ℝ) (r : ℝ) (n : ℕ) (w : Word Bool n)
    (hc : IsConcentrated E r (stoppedMap hθ E r n PositiveAffine.identity w)) :
    μ ((stoppedMap hθ E r n PositiveAffine.identity w) ⁻¹' stoppedCover hθ E r n) = 1 := by
  let q := stoppedMap hθ E r n PositiveAffine.identity w
  have hunit : μ (Icc (0 : ℝ) 1) = 1 := by
    have h := measure_inter_conull (s := Set.univ) hsupp
    simpa only [univ_inter, measure_univ] using h
  apply le_antisymm ((measure_mono (subset_univ _)).trans_eq measure_univ)
  rw [← hunit, ← q.preimage_interval]
  exact measure_mono (preimage_mono (stopped_interval_subset_cover hθ E r n w hc))

/-- The stopped cover's mass is controlled by the measurable small-set modulus. -/
theorem stoppedCover_mass_le_smallSetMass {θ r : ℝ} (hθ : 0 < θ) (hr : 0 < r)
    (μ : Measure ℝ) {E : Set ℝ} (hE : MeasurableSet E) (n : ℕ) :
    μ (stoppedCover hθ E r n) ≤
      smallSetMass μ volume (ENNReal.ofReal (3 / r) * volume E) :=
  measure_le_smallSetMass μ volume (measurableSet_stoppedCover hθ E r n)
    (volume_stoppedCover_le hθ hr hE n)

end LpSelfSimilar.SelfSimilar.Concentration
