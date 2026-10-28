module

public import LpSelfSimilar.Geometry.Euclidean
public import LpSelfSimilar.Geometry.FiniteBallCover
public import LpSelfSimilar.Analysis.BoundedOverlap
public import Mathlib.Topology.MetricSpace.HausdorffDistance

@[expose] public section

/-! Finite ball selection and the explicit Whitney geometry. -/

open MeasureTheory Metric Set
open scoped ENNReal

namespace LpSelfSimilar

/-- The radius used in the Whitney covering. -/
noncomputable def whitneyRadius {X : Type*} [PseudoMetricSpace X]
    (Ω : Set X) (x : X) : ℝ := infDist x Ωᶜ / 20

lemma twenty_mul_whitneyRadius {X : Type*} [PseudoMetricSpace X]
    (Ω : Set X) (x : X) : 20 * whitneyRadius Ω x = infDist x Ωᶜ := by
  unfold whitneyRadius
  ring

lemma whitneyRadius_pos {X : Type*} [PseudoMetricSpace X]
    {Ω : Set X} (hΩ : IsOpen Ω) (hne : Ωᶜ.Nonempty) {x : X} (hx : x ∈ Ω) :
    0 < whitneyRadius Ω x := by
  apply div_pos ?_ (by norm_num)
  exact (hΩ.isClosed_compl.notMem_iff_infDist_pos hne).mp (by simpa using hx)

/-- The doubled covering ball stays inside the open set. -/
lemma whitney_eight_ball_subset {X : Type*} [PseudoMetricSpace X]
    {Ω : Set X} {x : X} (hr : 0 < whitneyRadius Ω x) :
    ball x (8 * whitneyRadius Ω x) ⊆ Ω := by
  intro y hy
  have hdist : dist x y < infDist x Ωᶜ := by
    rw [← twenty_mul_whitneyRadius Ω x]
    have := mem_ball'.mp hy
    linarith
  simpa using notMem_of_dist_lt_infDist hdist

/-- A complement point lies in the dilation by twenty-one. -/
lemma exists_compl_mem_whitney_ball {X : Type*} [PseudoMetricSpace X]
    {Ω : Set X} (hne : Ωᶜ.Nonempty) {x : X} (hr : 0 < whitneyRadius Ω x) :
    ∃ y ∈ Ωᶜ, y ∈ ball x (21 * whitneyRadius Ω x) := by
  have hlt : infDist x Ωᶜ < 21 * whitneyRadius Ω x := by
    rw [← twenty_mul_whitneyRadius Ω x]
    linarith
  obtain ⟨y, hy, hxy⟩ := (infDist_lt_iff hne).mp hlt
  exact ⟨y, hy, mem_ball'.mpr hxy⟩

/-- At a common point of the dilations by eight, radii differ by at most `7/3`. -/
lemma whitney_radius_comparison {X : Type*} [PseudoMetricSpace X]
    (Ω : Set X) {x y z : X}
    (hx : z ∈ ball x (8 * whitneyRadius Ω x))
    (hy : z ∈ ball y (8 * whitneyRadius Ω y)) :
    3 * whitneyRadius Ω x ≤ 7 * whitneyRadius Ω y := by
  have hdist : dist x y < 8 * whitneyRadius Ω x + 8 * whitneyRadius Ω y :=
    (dist_triangle x z y).trans_lt (add_lt_add (mem_ball'.mp hx) (mem_ball.mp hy))
  have h := infDist_le_infDist_add_dist (x := x) (y := y) (s := Ωᶜ)
  rw [← twenty_mul_whitneyRadius Ω x, ← twenty_mul_whitneyRadius Ω y] at h
  linarith

/-- Packing disjoint balls of radius at least `a` into a ball of radius `21a`
gives the exact cardinality bound used in Lemma 2.1. -/
lemma disjoint_balls_card_le {d : ℕ} {ι : Type*} (s : Finset ι)
    (x : ι → Space d) (r : ι → ℝ)
    (hdisj : (s : Set ι).PairwiseDisjoint (fun i ↦ ball (x i) (r i)))
    (z : Space d) {a : ℝ} (ha : 0 < a)
    (hr : ∀ i ∈ s, a ≤ r i)
    (hsub : ∀ i ∈ s, ball (x i) (r i) ⊆ ball z (21 * a)) :
    s.card ≤ 21 ^ d := by
  have hv : 0 < volume.real (ball z a) := volume_real_ball_pos z ha
  have hsmall (i : ι) (hi : i ∈ s) :
      volume.real (ball z a) ≤ volume.real (ball (x i) (r i)) := by
    apply ENNReal.toReal_mono measure_ball_ne_top
    calc
      volume (ball z a) = volume (ball (x i) a) := by
        rw [Measure.addHaar_ball_center volume z, Measure.addHaar_ball_center volume (x i)]
      _ ≤ volume (ball (x i) (r i)) := measure_mono (ball_subset_ball (hr i hi))
  have hsum : (∑ i ∈ s, volume.real (ball (x i) (r i))) ≤
      volume.real (ball z (21 * a)) := by
    rw [← measureReal_biUnion_finset hdisj (fun _ _ ↦ isOpen_ball.measurableSet)]
    exact measureReal_mono (iUnion₂_subset hsub) measure_ball_ne_top
  have hscale : volume.real (ball z (21 * a)) =
      (21 : ℝ) ^ d * volume.real (ball z a) := by
    change (volume (ball z (21 * a))).toReal = _
    rw [volume_ball_scale z z (by norm_num : (0 : ℝ) < 21), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity)]
    rfl
  have hcard : (s.card : ℝ) * volume.real (ball z a) ≤
      (21 : ℝ) ^ d * volume.real (ball z a) := by
    calc
      (s.card : ℝ) * volume.real (ball z a) = ∑ _i ∈ s, volume.real (ball z a) := by simp
      _ ≤ ∑ i ∈ s, volume.real (ball (x i) (r i)) := Finset.sum_le_sum hsmall
      _ ≤ volume.real (ball z (21 * a)) := hsum
      _ = (21 : ℝ) ^ d * volume.real (ball z a) := hscale
  have hcard' : (s.card : ℝ) ≤ (21 : ℝ) ^ d := (mul_le_mul_iff_left₀ hv).mp hcard
  exact_mod_cast hcard'

open scoped Classical in
/-- The dilations by eight of a disjoint Whitney family have overlap at most
exactly `21^d`. The proof compares radii `9R` and `3R/7`. -/
lemma whitney_overlap_card {d : ℕ} (Ω : Set (Space d)) (s : Finset (Space d))
    (hr : ∀ x ∈ s, 0 < whitneyRadius Ω x)
    (hdisj : (s : Set (Space d)).PairwiseDisjoint
      (fun x ↦ ball x (whitneyRadius Ω x))) (z : Space d) :
    (s.filter (fun x ↦ z ∈ ball x (8 * whitneyRadius Ω x))).card ≤ 21 ^ d := by
  classical
  let t := s.filter (fun x ↦ z ∈ ball x (8 * whitneyRadius Ω x))
  change t.card ≤ 21 ^ d
  by_cases ht : t.Nonempty
  · obtain ⟨x, hxt, hmax⟩ := t.exists_max_image (whitneyRadius Ω) ht
    have hxs : x ∈ s := (Finset.mem_filter.mp hxt).1
    have hzx : z ∈ ball x (8 * whitneyRadius Ω x) := (Finset.mem_filter.mp hxt).2
    have hR : 0 < whitneyRadius Ω x := hr x hxs
    apply disjoint_balls_card_le t id (whitneyRadius Ω)
      (fun i hi j hj hij ↦ hdisj (Finset.mem_filter.mp hi).1
        (Finset.mem_filter.mp hj).1 hij)
      z (a := 3 * whitneyRadius Ω x / 7) (by positivity)
    · intro y hy
      have hzy := (Finset.mem_filter.mp hy).2
      have hcomp := whitney_radius_comparison Ω hzx hzy
      linarith
    · intro y hy w hw
      apply mem_ball.mpr
      have hwy := mem_ball.mp hw
      have hyz := mem_ball'.mp (Finset.mem_filter.mp hy).2
      have hmaxy := hmax y hy
      have htri := dist_triangle w y z
      dsimp only [id] at hwy
      linarith
  · simp only [Finset.not_nonempty_iff_eq_empty.mp ht, Finset.card_empty, zero_le]

lemma sum_measure_whitney_eight_le {d : ℕ} (μ : Measure (Space d))
    {Ω : Set (Space d)} (hΩ : IsOpen Ω) (s : Finset (Space d))
    (hr : ∀ x ∈ s, 0 < whitneyRadius Ω x)
    (hdisj : (s : Set (Space d)).PairwiseDisjoint
      (fun x ↦ ball x (whitneyRadius Ω x))) :
    (∑ x ∈ s, μ (ball x (8 * whitneyRadius Ω x))) ≤ (21 ^ d : ℝ≥0∞) * μ Ω := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    sum_measure_le_of_overlap μ s (fun x ↦ ball x (8 * whitneyRadius Ω x)) Ω (21 ^ d)
      (fun _ _ ↦ isOpen_ball.measurableSet) hΩ.measurableSet
      (fun x hx ↦ whitney_eight_ball_subset (hr x hx))
      (fun z ↦ whitney_overlap_card Ω s hr hdisj z)

end LpSelfSimilar
