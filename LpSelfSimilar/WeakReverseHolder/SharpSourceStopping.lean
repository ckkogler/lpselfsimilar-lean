module

public import LpSelfSimilar.WeakReverseHolder.SharpStopping

/-!
# Stopping at powers of six

The first radius `6^(-n)` with average at least `2t` has average below `2t`
on its sixfold enlargement. With an exact triple cover this proves the
coefficient `2 * 6^d * η` stated in Kittle–Kogler's level-set recurrence.
-/

@[expose] public section

open MeasureTheory Metric Set Filter
open scoped Topology

namespace LpSelfSimilar

noncomputable def sharpSourceAverage {d : ℕ} (f : Space d → ℝ)
    (x : Space d) (n : ℕ) : ℝ :=
  (∫ y in ball x ((1 / 6 : ℝ) ^ n), f y) /
    volume.real (ball x ((1 / 6 : ℝ) ^ n))

lemma sharp_ae_source_differentiation {d : ℕ} {f : Space d → ℝ}
    (hf : Integrable f volume) :
    ∀ᵐ x ∂volume, Tendsto (sharpSourceAverage f x) atTop (𝓝 (f x)) := by
  have hrad : Tendsto (fun n : ℕ => (1 / 6 : ℝ) ^ n) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num), ?_⟩
    exact Eventually.of_forall (fun n => by
      change 0 < (1 / 6 : ℝ) ^ n
      positivity)
  filter_upwards [(Besicovitch.vitaliFamily (volume : Measure (Space d))).ae_tendsto_average
    (f := f) hf.locallyIntegrable] with x hx
  have h := hx.comp ((Besicovitch.tendsto_filterAt volume x).comp hrad)
  convert h using 1
  ext n
  have hb := ball_ae_eq_closedBall x (by positivity : 0 < (1 / 6 : ℝ) ^ n)
  simp only [Function.comp_apply]
  rw [setAverage_eq, ← setIntegral_congr_set hb]
  rw [measureReal_def, ← measure_congr hb]
  simp only [sharpSourceAverage, measureReal_def, smul_eq_mul, div_eq_inv_mul]

theorem sharp_source_stopping_ball {d : ℕ} {f : Space d → ℝ}
    (hf : Integrable f volume) (hf0 : ∀ x, 0 ≤ f x)
    {t : ℝ} (ht : sharpStoppingThreshold f ≤ t)
    {x : Space d} (hx : Tendsto (sharpSourceAverage f x) atTop (𝓝 (f x)))
    (hxt : 2 * t < f x) :
    ∃ r : ℝ, 0 < r ∧ 3 * r < 1 ∧
      2 * t * volume.real (ball x r) ≤ ∫ y in ball x r, f y ∧
      (∫ y in ball x (3 * r), f y) ≤
        2 * ((2 : ℝ) ^ d * t) * volume.real (ball x (3 * r)) ∧
      (∫ y in ball x (6 * r), f y) ≤ 2 * t * volume.real (ball x (6 * r)) := by
  have ht0 : 0 < t := (sharpStoppingThreshold_pos hf0).trans_le ht
  have hex : ∃ n : ℕ, 2 * t ≤ sharpSourceAverage f x n := by
    obtain ⟨n, hn⟩ := (hx.eventually (eventually_gt_nhds hxt)).exists
    exact ⟨n, hn.le⟩
  let n := Nat.find hex
  have hn : 2 * t ≤ sharpSourceAverage f x n := Nat.find_spec hex
  have hprev (j : ℕ) (hj : j < n) : sharpSourceAverage f x j < 2 * t :=
    lt_of_not_ge (Nat.find_min hex hj)
  have hbase : (∫ y, f y) + 1 ≤
      t * volume.real (ball (0 : Space d) (1 / 4)) :=
    (div_le_iff₀ (volume_real_ball_pos _ (by norm_num))).mp ht
  have hn1 : 1 ≤ n := by
    by_contra hn1
    have hn0 : n = 0 := by omega
    have hr : (1 / 4 : ℝ) ≤ (1 / 6 : ℝ) ^ n := by norm_num [hn0]
    have hvol : volume.real (ball (0 : Space d) (1 / 4)) ≤
        volume.real (ball x ((1 / 6 : ℝ) ^ n)) := by
      rw [volume_real_ball_formula (0 : Space d) (r := 1 / 4) (by norm_num),
        volume_real_ball_formula x (r := (1 / 6 : ℝ) ^ n) (by positivity)]
      gcongr
    have hfirst : 2 * t * volume.real (ball x ((1 / 6 : ℝ) ^ n)) ≤
        ∫ y in ball x ((1 / 6 : ℝ) ^ n), f y :=
      (le_div_iff₀ (volume_real_ball_pos _ (by positivity))).mp hn
    have hupper := setIntegral_le_integral hf (ae_of_all _ hf0)
      (s := ball x ((1 / 6 : ℝ) ^ n))
    have hnonneg : 0 ≤ ∫ y, f y := integral_nonneg (fun y => hf0 y)
    nlinarith
  obtain ⟨m, hm⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
  let r := (1 / 6 : ℝ) ^ (m + 1)
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hr6 : 6 * r = (1 / 6 : ℝ) ^ m := by simp only [r, pow_add]; ring
  have h6 : (∫ y in ball x (6 * r), f y) ≤
      2 * t * volume.real (ball x (6 * r)) := by
    rw [hr6]
    exact ((div_lt_iff₀ (volume_real_ball_pos x (by positivity))).mp
      (hprev m (by omega))).le
  refine ⟨r, hr0, ?_, ?_, ?_, h6⟩
  · have hpow : (1 / 6 : ℝ) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    dsimp [r]
    rw [pow_succ]
    nlinarith
  · have h := (le_div_iff₀ (volume_real_ball_pos x
        (by positivity : 0 < (1 / 6 : ℝ) ^ n))).mp hn
    simpa only [hm] using h
  · have hmono : (∫ y in ball x (3 * r), f y) ≤ ∫ y in ball x (6 * r), f y :=
      setIntegral_mono_set hf.integrableOn (ae_of_all _ hf0)
        (ae_of_all _ (fun y hy => ball_subset_ball (by linarith) hy))
    have hscale : volume.real (ball x (6 * r)) =
        (2 : ℝ) ^ d * volume.real (ball x (3 * r)) := by
      have h := volume_ball_scale x x (by norm_num : (0 : ℝ) < 2) (3 * r)
      have h' := congrArg ENNReal.toReal h
      simpa only [measureReal_def, show 2 * (3 * r) = 6 * r by ring, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by positivity : 0 ≤ (2 : ℝ) ^ d)] using h'
    calc
      _ ≤ 2 * t * volume.real (ball x (6 * r)) := hmono.trans h6
      _ = _ := by rw [hscale]; ring

end LpSelfSimilar
