module

public import LpSelfSimilar.Geometry.Euclidean
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.MeasureTheory.Covering.Differentiation
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Dyadic stopping balls

Lebesgue differentiation supplies a small ball with average above a prescribed
level. The first such dyadic ball has controlled averages on its fourfold and
eightfold enlargements. A single global threshold makes all fourfold balls
small enough for the local weak reverse Hölder hypothesis.
-/

@[expose] public section

open MeasureTheory Metric Set Filter
open scoped Topology

namespace LpSelfSimilar

/-- Ball averages along the fixed dyadic radii. -/
noncomputable def sharpDyadicAverage {d : ℕ} (f : Space d → ℝ)
    (x : Space d) (n : ℕ) : ℝ :=
  (∫ y in ball x ((1 / 2 : ℝ) ^ n), f y) /
    volume.real (ball x ((1 / 2 : ℝ) ^ n))

lemma sharp_ae_dyadic_differentiation {d : ℕ} {f : Space d → ℝ}
    (hf : Integrable f volume) :
    ∀ᵐ x ∂volume, Tendsto (sharpDyadicAverage f x) atTop (𝓝 (f x)) := by
  have hrad : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num), ?_⟩
    exact Eventually.of_forall (fun n => by
      change 0 < (1 / 2 : ℝ) ^ n
      positivity)
  filter_upwards [(Besicovitch.vitaliFamily (volume : Measure (Space d))).ae_tendsto_average
    (f := f) hf.locallyIntegrable]
    with x hx
  have h := hx.comp ((Besicovitch.tendsto_filterAt volume x).comp hrad)
  convert h using 1
  ext n
  have hb := ball_ae_eq_closedBall x (by positivity : 0 < (1 / 2 : ℝ) ^ n)
  simp only [Function.comp_apply]
  rw [setAverage_eq, ← setIntegral_congr_set hb]
  rw [measureReal_def, ← measure_congr hb]
  simp only [sharpDyadicAverage, measureReal_def, smul_eq_mul, div_eq_inv_mul]

/-- Above this threshold, a stopping ball has radius at most one eighth. -/
noncomputable def sharpStoppingThreshold {d : ℕ} (f : Space d → ℝ) : ℝ :=
  ((∫ x, f x) + 1) / volume.real (ball (0 : Space d) (1 / 4))

lemma sharpStoppingThreshold_pos {d : ℕ} {f : Space d → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) : 0 < sharpStoppingThreshold f := by
  apply div_pos
  · have h : 0 ≤ ∫ x, f x := integral_nonneg (fun x => hf0 x)
    linarith
  · exact volume_real_ball_pos _ (by norm_num)

/-- A Lebesgue point above `2t` has a stopping ball with controlled enlargements. -/
theorem sharp_exists_stopping_ball {d : ℕ} {f : Space d → ℝ}
    (hf : Integrable f volume) (hf0 : ∀ x, 0 ≤ f x)
    {t : ℝ} (ht : sharpStoppingThreshold f ≤ t)
    {x : Space d} (hx : Tendsto (sharpDyadicAverage f x) atTop (𝓝 (f x)))
    (hxt : 2 * t < f x) :
    ∃ r : ℝ, 0 < r ∧ 4 * r < 1 ∧
      2 * t * volume.real (ball x r) ≤ ∫ y in ball x r, f y ∧
      (∫ y in ball x (4 * r), f y) ≤ 2 * t * volume.real (ball x (4 * r)) ∧
      (∫ y in ball x (8 * r), f y) ≤ 2 * t * volume.real (ball x (8 * r)) := by
  have ht0 : 0 < t := (sharpStoppingThreshold_pos hf0).trans_le ht
  have hex : ∃ n : ℕ, 2 * t ≤ sharpDyadicAverage f x n := by
    obtain ⟨n, hn⟩ := (hx.eventually (eventually_gt_nhds hxt)).exists
    exact ⟨n, hn.le⟩
  let n := Nat.find hex
  have hn : 2 * t ≤ sharpDyadicAverage f x n := Nat.find_spec hex
  have hprev (j : ℕ) (hj : j < n) : sharpDyadicAverage f x j < 2 * t := by
    exact lt_of_not_ge (Nat.find_min hex hj)
  have hbase : (∫ y, f y) + 1 ≤
      t * volume.real (ball (0 : Space d) (1 / 4)) := by
    exact (div_le_iff₀ (volume_real_ball_pos _ (by norm_num))).mp ht
  have hn3 : 3 ≤ n := by
    by_contra hn3
    have hn2 : n ≤ 2 := by omega
    have hr : (1 / 4 : ℝ) ≤ (1 / 2 : ℝ) ^ n := by
      interval_cases n <;> norm_num
    have hvol : volume.real (ball (0 : Space d) (1 / 4)) ≤
        volume.real (ball x ((1 / 2 : ℝ) ^ n)) := by
      rw [volume_real_ball_formula (0 : Space d) (r := 1 / 4) (by norm_num),
        volume_real_ball_formula x (r := (1 / 2 : ℝ) ^ n) (by positivity)]
      gcongr
    have hfirst : 2 * t * volume.real (ball x ((1 / 2 : ℝ) ^ n)) ≤
        ∫ y in ball x ((1 / 2 : ℝ) ^ n), f y :=
      (le_div_iff₀ (volume_real_ball_pos _ (by positivity))).mp hn
    have hupper := setIntegral_le_integral hf (ae_of_all _ hf0)
      (s := ball x ((1 / 2 : ℝ) ^ n))
    have hnonneg : 0 ≤ ∫ y, f y := integral_nonneg (fun y => hf0 y)
    nlinarith
  obtain ⟨m, hm⟩ : ∃ m : ℕ, n = m + 3 := ⟨n - 3, by omega⟩
  let r := (1 / 2 : ℝ) ^ (m + 3)
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hr4 : 4 * r = (1 / 2 : ℝ) ^ (m + 1) := by
    simp only [r, pow_add]
    ring
  have hr8 : 8 * r = (1 / 2 : ℝ) ^ m := by
    simp only [r, pow_add]
    ring
  refine ⟨r, hr0, ?_, ?_, ?_, ?_⟩
  · rw [hr4, pow_succ]
    have hpow : (1 / 2 : ℝ) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  · have h := (le_div_iff₀ (volume_real_ball_pos x
        (by positivity : 0 < (1 / 2 : ℝ) ^ n))).mp hn
    simpa only [hm] using h
  · rw [hr4]
    exact ((div_lt_iff₀ (volume_real_ball_pos x (by positivity))).mp
      (hprev (m + 1) (by omega))).le
  · rw [hr8]
    exact ((div_lt_iff₀ (volume_real_ball_pos x (by positivity))).mp
      (hprev m (by omega))).le

end LpSelfSimilar
