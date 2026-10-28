module

public import LpSelfSimilar.WeakReverseHolder.SharpLocalBounds
public import LpSelfSimilar.WeakReverseHolder.Theorem
public import LpSelfSimilar.WeakReverseHolder.SharpTripleCover

/-!
# Weighted covering estimate for stopping balls

A disjoint subfamily of stopping balls covers a compact high-density set after
triple enlargement. The local small-set hypothesis estimates the mass there
by the sixfold balls. Disjointness recovers their total volume from the mass
above the lower density level, giving the exact factor `2 * 6^d * η`.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped ENNReal

namespace LpSelfSimilar

lemma sharp_source_ball_lower_tail_integral {d : ℕ} {f : Space d → ℝ}
    (hf : Integrable f volume) (hfm : Measurable f)
    {t : ℝ} (ht : 0 ≤ t) {x : Space d} {r : ℝ}
    (hlower : 2 * t * volume.real (ball x r) ≤ ∫ y in ball x r, f y) :
    t * volume.real (ball x r) ≤ ∫ y in ball x r ∩ {z | t < f z}, f y := by
  let S := {z | t < f z}
  have hS : MeasurableSet S := measurableSet_lt measurable_const hfm
  have hdiff : MeasurableSet (ball x r \ S) := isOpen_ball.measurableSet.diff hS
  have hfin : volume (ball x r \ S) ≠ ∞ :=
    ((measure_mono sdiff_subset).trans_lt measure_ball_lt_top).ne
  have hle : (∫ y in ball x r \ S, f y) ≤
      volume.real (ball x r \ S) * t := by
    have h := setIntegral_mono_on hf.integrableOn (integrableOn_const hfin) hdiff
      (fun y hy => not_lt.mp hy.2)
    simpa only [setIntegral_const, smul_eq_mul] using h
  have hv : volume.real (ball x r \ S) ≤ volume.real (ball x r) :=
    measureReal_mono sdiff_subset measure_ball_ne_top
  have hsplit := integral_inter_add_sdiff hS (hf.integrableOn (s := ball x r))
  have hbound := mul_le_mul_of_nonneg_right hv ht
  change t * volume.real (ball x r) ≤ ∫ y in ball x r ∩ S, f y
  nlinarith

theorem sharp_source_compact_level_mass_bound {d : ℕ} {f : Space d → ℝ}
    (hf : Integrable f volume) (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    {A ε η t : ℝ} (hA : 0 < A) (ht : 0 < t) (hη : 0 ≤ η)
    (hAε : 2 * (2 : ℝ) ^ d ≤ A * ε) (hsmall : SmallSetHypothesis f ε η)
    {K : Set (Space d)} (hK : IsCompact K) (hKE : K ⊆ {x | A * t < f x})
    (hballs : ∀ x ∈ K, ∃ r : ℝ, 0 < r ∧ 3 * r < 1 ∧
      2 * t * volume.real (ball x r) ≤ ∫ y in ball x r, f y ∧
      (∫ y in ball x (3 * r), f y) ≤ 2 * ((2 : ℝ) ^ d * t) * volume.real (ball x (3 * r)) ∧
      (∫ y in ball x (6 * r), f y) ≤ 2 * t * volume.real (ball x (6 * r))) :
    volume.withDensity (fun x => ENNReal.ofReal (f x)) K ≤
      ENNReal.ofReal (2 * (6 : ℝ) ^ d * η) *
        volume.withDensity (fun x => ENNReal.ofReal (f x)) {x | t < f x} := by
  classical
  let ν := volume.withDensity (fun x => ENNReal.ofReal (f x))
  let E := {x | A * t < f x}
  let S := {x | t < f x}
  have hE : MeasurableSet E := measurableSet_lt measurable_const hfm
  have hS : MeasurableSet S := measurableSet_lt measurable_const hfm
  have hν {U : Set (Space d)} (hU : MeasurableSet U) :
      ν U = ENNReal.ofReal (∫ x in U, f x) := sharp_density_measure_apply hf hf0 hU
  have hw (x : K) := hballs x x.property
  choose r hr0 hr4 hlo hup4 hup8 using hw
  obtain ⟨s, hKs⟩ := hK.elim_finite_subcover (fun x : K => ball (x : Space d) (r x))
    (fun _ => isOpen_ball) (fun x hx => mem_iUnion.mpr
      ⟨⟨x, hx⟩, mem_ball_self (hr0 ⟨x, hx⟩)⟩)
  obtain ⟨u, hus, hdisj, hcover⟩ := sharp_finite_disjoint_triple_cover s
    (fun x : K => (x : Space d)) r (fun i _ => hr0 i)
  have hKcover : K ⊆ ⋃ x ∈ u, E ∩ ball (x : Space d) (3 * r x) := by
    intro y hy
    obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp (hKs hy)
    obtain ⟨j, hj, hij⟩ := hcover i hi
    exact mem_iUnion₂.mpr ⟨j, hj, hKE hy, hij hyi⟩
  have hsmallball (i : K) :
      ν (E ∩ ball (i : Space d) (3 * r i)) ≤
        ENNReal.ofReal η * ν (ball (i : Space d) (6 * r i)) := by
    have hpow : 0 < (2 : ℝ) ^ d := by positivity
    have hAε' : 2 ≤ (A / (2 : ℝ) ^ d) * ε := by
      have h := (le_div_iff₀ hpow).mpr hAε
      convert h using 1
      ring
    have hvol' := sharp_high_level_small_volume hf hfm hf0 (div_pos hA hpow)
      (mul_pos hpow ht) hAε' (hup4 i)
    have hcut : (A / (2 : ℝ) ^ d) * ((2 : ℝ) ^ d * t) = A * t := by
      field_simp
    rw [hcut] at hvol'
    have hvol : volume (E ∩ ball (i : Space d) (3 * r i)) ≤
        ENNReal.ofReal ε * volume (ball (i : Space d) (3 * r i)) :=
      (measure_mono (show E ∩ ball (i : Space d) (3 * r i) ⊆
        {y | A * t ≤ f y} ∩ ball (i : Space d) (3 * r i) from
        fun y hy => ⟨(show A * t < f y from hy.1).le, hy.2⟩)).trans hvol'
    have h := hsmall (i : Space d) (3 * r i) (mul_pos (by norm_num) (hr0 i)) (hr4 i)
      (E ∩ ball (i : Space d) (3 * r i)) (hE.inter isOpen_ball.measurableSet)
      inter_subset_right hvol
    rw [show 2 * (3 * r i) = 6 * r i by ring] at h
    rw [hν (hE.inter isOpen_ball.measurableSet), hν isOpen_ball.measurableSet,
      ← ENNReal.ofReal_mul hη]
    exact ENNReal.ofReal_le_ofReal h
  have hlarge (i : K) : ν (ball (i : Space d) (6 * r i)) ≤
      ENNReal.ofReal (2 * t) * ENNReal.ofReal ((6 : ℝ) ^ d) *
        volume (ball (i : Space d) (r i)) := by
    have h := ENNReal.ofReal_le_ofReal (hup8 i)
    rw [ENNReal.ofReal_mul (by positivity), measureReal_def,
      ENNReal.ofReal_toReal measure_ball_ne_top,
      volume_ball_scale (i : Space d) (i : Space d) (by norm_num : (0 : ℝ) < 6),
      ← mul_assoc] at h
    rw [hν isOpen_ball.measurableSet]
    exact h
  have hlowmass (i : K) :
      ENNReal.ofReal t * volume (ball (i : Space d) (r i)) ≤
        ν (ball (i : Space d) (r i) ∩ S) := by
    have h := ENNReal.ofReal_le_ofReal
      (sharp_source_ball_lower_tail_integral hf hfm ht.le (hlo i))
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
  have hcoeff : ENNReal.ofReal (2 * (6 : ℝ) ^ d * η) * ENNReal.ofReal t =
      ENNReal.ofReal η * ENNReal.ofReal (2 * t) * ENNReal.ofReal ((6 : ℝ) ^ d) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hη,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  change ν K ≤ ENNReal.ofReal (2 * (6 : ℝ) ^ d * η) * ν S
  calc
    ν K ≤ ∑ i ∈ u, ν (E ∩ ball (i : Space d) (3 * r i)) :=
      (measure_mono hKcover).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ i ∈ u, ENNReal.ofReal η * ν (ball (i : Space d) (6 * r i)) :=
      Finset.sum_le_sum (fun i _ => hsmallball i)
    _ ≤ ∑ i ∈ u, ENNReal.ofReal η * (ENNReal.ofReal (2 * t) *
        ENNReal.ofReal ((6 : ℝ) ^ d) * volume (ball (i : Space d) (r i))) := by
      gcongr with i hi
      exact hlarge i
    _ = ENNReal.ofReal (2 * (6 : ℝ) ^ d * η) *
        (ENNReal.ofReal t * ∑ i ∈ u, volume (ball (i : Space d) (r i))) := by
      simp only [← Finset.mul_sum]
      conv_rhs => rw [← mul_assoc, hcoeff]
      ac_rfl
    _ ≤ ENNReal.ofReal (2 * (6 : ℝ) ^ d * η) * ν S := by gcongr

end LpSelfSimilar
