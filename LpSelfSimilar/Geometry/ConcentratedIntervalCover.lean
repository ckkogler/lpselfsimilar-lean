module

public import LpSelfSimilar.Geometry.FiniteTripleBallCover
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-!
# The exact volume bound for finitely many concentrated intervals

If every interval contains at least an r-fraction of a measurable set E,
the finite greedy triple cover has total union volume at most 3*|E|/r.
The selected original intervals are disjoint, so their intersections with E
can be summed without a multiplicity loss. Closed endpoints cause no
additional volume cost for Lebesgue measure.
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace LpSelfSimilar.Geometry

/-- Tripling the radius of a real closed ball triples its Lebesgue volume. -/
theorem volume_closedBall_triple (x r : ℝ) :
    volume (closedBall x (3 * r)) = (3 : ℝ≥0∞) * volume (closedBall x r) := by
  rw [Real.volume_closedBall, Real.volume_closedBall,
    show 2 * (3 * r) = 3 * (2 * r) by ring, ENNReal.ofReal_mul (by norm_num)]
  norm_num

/-- A finite union of concentrated intervals obeys the exact factor-three volume bound. -/
theorem volume_union_concentrated_closedBalls_le {ι : Type*}
    (s : Finset ι) (x r : ι → ℝ) (hr : ∀ i ∈ s, 0 ≤ r i)
    {E : Set ℝ} (hE : MeasurableSet E) {ρ : ℝ} (hρ : 0 < ρ)
    (hconc : ∀ i ∈ s, ENNReal.ofReal ρ * volume (closedBall (x i) (r i)) ≤
      volume (E ∩ closedBall (x i) (r i))) :
    volume (⋃ i ∈ s, closedBall (x i) (r i)) ≤ ENNReal.ofReal (3 / ρ) * volume E := by
  obtain ⟨t, hts, hd, hc⟩ := finite_disjoint_closedBall_triple_cover s x r hr
  have hsub : (⋃ i ∈ s, closedBall (x i) (r i)) ⊆
      ⋃ j ∈ t, closedBall (x j) (3 * r j) := by
    intro u hu
    obtain ⟨i, hi, hui⟩ := mem_iUnion₂.mp hu
    obtain ⟨j, hj, hij⟩ := hc i hi
    exact mem_iUnion₂.mpr ⟨j, hj, hij hui⟩
  have hvol : volume (⋃ i ∈ s, closedBall (x i) (r i)) ≤
      3 * ∑ j ∈ t, volume (closedBall (x j) (r j)) := by
    have h := (measure_mono (μ := volume) hsub).trans (measure_biUnion_finset_le _ _)
    simp_rw [volume_closedBall_triple] at h
    simpa only [Finset.mul_sum] using h
  have hsum : ENNReal.ofReal ρ * (∑ j ∈ t, volume (closedBall (x j) (r j))) ≤ volume E := by
    calc
      _ = ∑ j ∈ t, ENNReal.ofReal ρ * volume (closedBall (x j) (r j)) := Finset.mul_sum ..
      _ ≤ ∑ j ∈ t, volume (E ∩ closedBall (x j) (r j)) :=
        Finset.sum_le_sum (fun j hj => hconc j (hts hj))
      _ = volume (⋃ j ∈ t, E ∩ closedBall (x j) (r j)) :=
        (measure_biUnion_finset (hd.mono (fun _ => inter_subset_right))
          (fun _ _ => hE.inter measurableSet_closedBall)).symm
      _ ≤ volume E := measure_mono (iUnion₂_subset (fun _ _ => inter_subset_left))
  have hcancel : ENNReal.ofReal (3 / ρ) * ENNReal.ofReal ρ = (3 : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    rw [div_mul_cancel₀ _ hρ.ne']
    norm_num
  calc
    _ ≤ _ := hvol
    _ = ENNReal.ofReal (3 / ρ) * (ENNReal.ofReal ρ * ∑ j ∈ t, volume (closedBall (x j) (r j))) := by
      rw [← mul_assoc, hcancel]
    _ ≤ _ := mul_le_mul' le_rfl hsum

end LpSelfSimilar.Geometry
