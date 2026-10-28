module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic

@[expose] public section

/-! Euclidean geometry and Lebesgue volume used in the covering proof. -/

open MeasureTheory MeasureTheory.Measure Metric Set
open scoped ENNReal

namespace LpSelfSimilar

/-- Euclidean `d`-space with its Euclidean metric and canonical Lebesgue measure. -/
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

lemma volume_ball_scale {d : ℕ} (x y : Space d) {a : ℝ} (ha : 0 < a) (r : ℝ) :
    volume (ball x (a * r)) = ENNReal.ofReal (a ^ d) * volume (ball y r) := by
  simpa only [finrank_euclideanSpace_fin, addHaar_ball_center] using
    addHaar_ball_mul_of_pos volume x ha r

lemma volume_ball_formula {d : ℕ} (x : Space d) {r : ℝ} (hr : 0 < r) :
    volume (ball x r) = ENNReal.ofReal (r ^ d) * volume (ball (0 : Space d) 1) := by
  simpa only [finrank_euclideanSpace_fin] using addHaar_ball_of_pos volume x hr

lemma volume_real_ball_formula {d : ℕ} (x : Space d) {r : ℝ} (hr : 0 < r) :
    volume.real (ball x r) = r ^ d * volume.real (ball (0 : Space d) 1) := by
  simp only [measureReal_def, volume_ball_formula x hr, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hr.le _)]

lemma volume_real_ball_pos {d : ℕ} (x : Space d) {r : ℝ} (hr : 0 < r) :
    0 < volume.real (ball x r) :=
  ENNReal.toReal_pos (measure_ball_pos volume x hr).ne' measure_ball_ne_top

lemma ball_ae_eq_closedBall {d : ℕ} (x : Space d) {r : ℝ} (hr : 0 < r) :
    ball x r =ᵐ[volume] closedBall x r := by
  apply ae_eq_of_subset_of_measure_ge ball_subset_closedBall ?_
    isOpen_ball.measurableSet.nullMeasurableSet measure_closedBall_lt_top.ne
  rw [addHaar_closedBall volume x hr.le, addHaar_ball_of_pos volume x hr]

lemma radius_le_one_of_volume_ball_le {d : ℕ} (hd : 1 ≤ d)
    (x : Space d) {r : ℝ} (hr : 0 < r)
    (hvol : volume (ball x r) ≤ volume (ball (0 : Space d) 1)) : r ≤ 1 := by
  have hreal := ENNReal.toReal_mono measure_ball_ne_top hvol
  change volume.real (ball x r) ≤ volume.real (ball (0 : Space d) 1) at hreal
  rw [volume_real_ball_formula x hr] at hreal
  have hv := volume_real_ball_pos (0 : Space d) zero_lt_one
  have hp : r ^ d ≤ 1 := by nlinarith
  by_contra! h
  exact (one_lt_pow₀ h (by omega : d ≠ 0)).not_ge hp

lemma compl_nonempty_of_volume_le_unitBall {d : ℕ} (hd : 1 ≤ d)
    {Ω : Set (Space d)} (hvol : volume Ω ≤ volume (ball (0 : Space d) 1)) :
    Ωᶜ.Nonempty := by
  by_contra hne
  have hcomp : Ωᶜ = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
  have hΩ : Ω = univ := by
    simpa using congrArg (fun s : Set (Space d) ↦ sᶜ) hcomp
  have hball : volume (ball (0 : Space d) 2) ≤ volume (ball (0 : Space d) 1) := by
    apply le_trans (measure_mono (show ball (0 : Space d) 2 ⊆ Ω by simp [hΩ])) hvol
  have h := radius_le_one_of_volume_ball_le hd (0 : Space d) (by norm_num) hball
  norm_num at h

end LpSelfSimilar
