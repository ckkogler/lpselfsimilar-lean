module

public import LpSelfSimilar.WeakReverseHolder.SharpLocalBounds
public import LpSelfSimilar.WeakReverseHolder.Theorem
public import LpSelfSimilar.Geometry.FiniteBallCover

/-!
# Weighted covering estimate for stopping balls

A disjoint subfamily of stopping balls covers a compact high-density set after
fourfold enlargement. The local small-set hypothesis estimates the mass there
by the eightfold balls. Disjointness recovers their total volume from the mass
above the lower density level, giving the exact factor `2 * 8^d * η`.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped ENNReal

namespace LpSelfSimilar

theorem sharp_compact_level_mass_bound {d : ℕ} {f : Space d → ℝ}
    (hf : Integrable f volume) (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    {A ε η t : ℝ} (hA : 0 < A) (ht : 0 < t) (hη : 0 ≤ η)
    (hAε : 2 ≤ A * ε) (hsmall : SmallSetHypothesis f ε η)
    {K : Set (Space d)} (hK : IsCompact K) (hKE : K ⊆ {x | A * t ≤ f x})
    (hballs : ∀ x ∈ K, ∃ r : ℝ, 0 < r ∧ 4 * r < 1 ∧
      2 * t * volume.real (ball x r) ≤ ∫ y in ball x r, f y ∧
      (∫ y in ball x (4 * r), f y) ≤ 2 * t * volume.real (ball x (4 * r)) ∧
      (∫ y in ball x (8 * r), f y) ≤ 2 * t * volume.real (ball x (8 * r))) :
    volume.withDensity (fun x => ENNReal.ofReal (f x)) K ≤
      ENNReal.ofReal (2 * (8 : ℝ) ^ d * η) *
        volume.withDensity (fun x => ENNReal.ofReal (f x)) {x | t ≤ f x} := by
  classical
  let ν := volume.withDensity (fun x => ENNReal.ofReal (f x))
  let E := {x | A * t ≤ f x}
  let S := {x | t ≤ f x}
  have hE : MeasurableSet E := measurableSet_le measurable_const hfm
  have hS : MeasurableSet S := measurableSet_le measurable_const hfm
  have hν {U : Set (Space d)} (hU : MeasurableSet U) :
      ν U = ENNReal.ofReal (∫ x in U, f x) := sharp_density_measure_apply hf hf0 hU
  have hw (x : K) := hballs x x.property
  choose r hr0 hr4 hlo hup4 hup8 using hw
  obtain ⟨s, hKs⟩ := hK.elim_finite_subcover (fun x : K => ball (x : Space d) (r x))
    (fun _ => isOpen_ball) (fun x hx => mem_iUnion.mpr
      ⟨⟨x, hx⟩, mem_ball_self (hr0 ⟨x, hx⟩)⟩)
  obtain ⟨u, hus, hdisj, hcover⟩ := finite_disjoint_ball_cover s
    (fun x : K => (x : Space d)) r
  have hKcover : K ⊆ ⋃ x ∈ u, E ∩ ball (x : Space d) (4 * r x) := by
    intro y hy
    obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp (hKs hy)
    obtain ⟨j, hj, hij⟩ := hcover i hi
    exact mem_iUnion₂.mpr ⟨j, hj, hKE hy, hij hyi⟩
  have hsmallball (i : K) :
      ν (E ∩ ball (i : Space d) (4 * r i)) ≤
        ENNReal.ofReal η * ν (ball (i : Space d) (8 * r i)) := by
    have hvol := sharp_high_level_small_volume hf hfm hf0 hA ht hAε (hup4 i)
    have h := hsmall (i : Space d) (4 * r i) (mul_pos (by norm_num) (hr0 i)) (hr4 i)
      (E ∩ ball (i : Space d) (4 * r i)) (hE.inter isOpen_ball.measurableSet)
      inter_subset_right hvol
    rw [show 2 * (4 * r i) = 8 * r i by ring] at h
    rw [hν (hE.inter isOpen_ball.measurableSet), hν isOpen_ball.measurableSet,
      ← ENNReal.ofReal_mul hη]
    exact ENNReal.ofReal_le_ofReal h
  have hlarge (i : K) : ν (ball (i : Space d) (8 * r i)) ≤
      ENNReal.ofReal (2 * t) * ENNReal.ofReal ((8 : ℝ) ^ d) *
        volume (ball (i : Space d) (r i)) := by
    have h := ENNReal.ofReal_le_ofReal (hup8 i)
    rw [ENNReal.ofReal_mul (by positivity), measureReal_def,
      ENNReal.ofReal_toReal measure_ball_ne_top,
      volume_ball_scale (i : Space d) (i : Space d) (by norm_num : (0 : ℝ) < 8),
      ← mul_assoc] at h
    rw [hν isOpen_ball.measurableSet]
    exact h
  have hlowmass (i : K) :
      ENNReal.ofReal t * volume (ball (i : Space d) (r i)) ≤
        ν (ball (i : Space d) (r i) ∩ S) := by
    have h := ENNReal.ofReal_le_ofReal
      (sharp_ball_lower_tail_integral hf hfm ht.le (hlo i))
    rw [ENNReal.ofReal_mul ht.le, measureReal_def,
      ENNReal.ofReal_toReal measure_ball_ne_top] at h
    rw [hν (isOpen_ball.measurableSet.inter hS)]
    exact h
  have hsum : ENNReal.ofReal t * (∑ i ∈ u, volume (ball (i : Space d) (r i))) ≤ ν S := by
    calc
      _ = ∑ i ∈ u, ENNReal.ofReal t * volume (ball (i : Space d) (r i)) := Finset.mul_sum ..
      _ ≤ ∑ i ∈ u, ν (ball (i : Space d) (r i) ∩ S) :=
        Finset.sum_le_sum (fun i _ => hlowmass i)
      _ = ν (⋃ i ∈ u, ball (i : Space d) (r i) ∩ S) :=
        (measure_biUnion_finset (hdisj.mono (fun _ => inter_subset_left))
          (fun _ _ => isOpen_ball.measurableSet.inter hS)).symm
      _ ≤ ν S := measure_mono (iUnion₂_subset (fun _ _ => inter_subset_right))
  have hcoeff : ENNReal.ofReal (2 * (8 : ℝ) ^ d * η) * ENNReal.ofReal t =
      ENNReal.ofReal η * ENNReal.ofReal (2 * t) * ENNReal.ofReal ((8 : ℝ) ^ d) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hη,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  change ν K ≤ ENNReal.ofReal (2 * (8 : ℝ) ^ d * η) * ν S
  calc
    ν K ≤ ∑ i ∈ u, ν (E ∩ ball (i : Space d) (4 * r i)) :=
      (measure_mono hKcover).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ i ∈ u, ENNReal.ofReal η * ν (ball (i : Space d) (8 * r i)) :=
      Finset.sum_le_sum (fun i _ => hsmallball i)
    _ ≤ ∑ i ∈ u, ENNReal.ofReal η * (ENNReal.ofReal (2 * t) *
        ENNReal.ofReal ((8 : ℝ) ^ d) * volume (ball (i : Space d) (r i))) := by
      gcongr with i hi
      exact hlarge i
    _ = ENNReal.ofReal (2 * (8 : ℝ) ^ d * η) *
        (ENNReal.ofReal t * ∑ i ∈ u, volume (ball (i : Space d) (r i))) := by
      simp only [← Finset.mul_sum]
      conv_rhs => rw [← mul_assoc, hcoeff]
      ac_rfl
    _ ≤ ENNReal.ofReal (2 * (8 : ℝ) ^ d * η) * ν S := by gcongr

end LpSelfSimilar
