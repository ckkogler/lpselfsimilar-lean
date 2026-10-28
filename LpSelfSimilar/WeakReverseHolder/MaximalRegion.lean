module

public import LpSelfSimilar.WeakReverseHolder.WhitneyCovering
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.MeasureTheory.Measure.Regular

@[expose] public section

/-! Maximal regions of measurable sets and their explicit volume bound. -/

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

namespace LpSelfSimilar

/-- The open superlevel set of the uncentered maximal function of `1_E`.
The definition uses the witnessing balls directly, avoiding an extended-real supremum. -/
def maximalRegion {d : ℕ} (E : Set (Space d)) (θ : ℝ) : Set (Space d) :=
  {x | ∃ c r, 0 < r ∧ x ∈ ball c r ∧
    ENNReal.ofReal θ * volume (ball c r) < volume (E ∩ ball c r)}

lemma isOpen_maximalRegion {d : ℕ} (E : Set (Space d)) (θ : ℝ) :
    IsOpen (maximalRegion E θ) := by
  apply isOpen_iff_forall_mem_open.mpr
  rintro x ⟨c, r, hr, hx, havg⟩
  exact ⟨ball c r, (fun y hy ↦ ⟨c, r, hr, hy, havg⟩), isOpen_ball, hx⟩

lemma volume_inter_ball_le_of_notMem_maximalRegion {d : ℕ}
    {E : Set (Space d)} {θ : ℝ} {x c : Space d} {r : ℝ}
    (hx : x ∉ maximalRegion E θ) (hr : 0 < r) (hxc : x ∈ ball c r) :
    volume (E ∩ ball c r) ≤ ENNReal.ofReal θ * volume (ball c r) := by
  exact le_of_not_gt (fun h ↦ hx ⟨c, r, hr, hxc, h⟩)

/-- The weak maximal estimate on a compact subset of the maximal region. -/
lemma volume_compact_subset_maximalRegion_le {d : ℕ} {E K : Set (Space d)}
    (hE : MeasurableSet E) {θ : ℝ} (hθ : 0 < θ) (hK : IsCompact K)
    (hKΩ : K ⊆ maximalRegion E θ) :
    volume K ≤ ENNReal.ofReal ((4 : ℝ) ^ d / θ) * volume E := by
  classical
  let B := {b : Space d × ℝ // 0 < b.2 ∧
    ENNReal.ofReal θ * volume (ball b.1 b.2) < volume (E ∩ ball b.1 b.2)}
  let c : B → Space d := fun b ↦ b.1.1
  let r : B → ℝ := fun b ↦ b.1.2
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun b : B ↦ ball (c b) (r b))
    (fun _ ↦ isOpen_ball) (by
      intro x hx
      obtain ⟨y, t, ht, hxy, havg⟩ := hKΩ hx
      exact mem_iUnion.mpr ⟨⟨(y, t), ht, havg⟩, hxy⟩)
  obtain ⟨t, hts, hdisj, hcover⟩ := finite_disjoint_ball_cover s c r
  have hKcover : K ⊆ ⋃ b ∈ t, ball (c b) (4 * r b) := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs hx)
    obtain ⟨j, hj, hij⟩ := hcover i hi
    exact mem_iUnion₂.mpr ⟨j, hj, hij hxi⟩
  have hKvol : volume K ≤ ∑ b ∈ t, volume (ball (c b) (4 * r b)) :=
    (measure_mono hKcover).trans (measure_biUnion_finset_le _ _)
  have hsumE : (∑ b ∈ t, volume (E ∩ ball (c b) (r b))) ≤ volume E := by
    rw [← measure_biUnion_finset (hdisj.mono (fun _ ↦ inter_subset_right))
      (fun _ _ ↦ hE.inter isOpen_ball.measurableSet)]
    exact measure_mono (iUnion₂_subset (fun _ _ ↦ inter_subset_left))
  have hsum : ENNReal.ofReal θ * (∑ b ∈ t, volume (ball (c b) (r b))) ≤
      ∑ b ∈ t, volume (E ∩ ball (c b) (r b)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun b _ ↦ b.2.2.le)
  have hscale (b : B) : volume (ball (c b) (4 * r b)) =
      ENNReal.ofReal ((4 : ℝ) ^ d) * volume (ball (c b) (r b)) :=
    volume_ball_scale (c b) (c b) (by norm_num) (r b)
  have hcoeff : ENNReal.ofReal θ * ENNReal.ofReal ((4 : ℝ) ^ d / θ) =
      ENNReal.ofReal ((4 : ℝ) ^ d) := by
    rw [← ENNReal.ofReal_mul hθ.le]
    congr 1
    field_simp
  apply (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hθ).ne'
    ENNReal.ofReal_ne_top).mp
  rw [← mul_assoc, hcoeff]
  calc
    ENNReal.ofReal θ * volume K ≤
        ENNReal.ofReal θ * ∑ b ∈ t, volume (ball (c b) (4 * r b)) := by gcongr
    _ = ENNReal.ofReal ((4 : ℝ) ^ d) *
        (ENNReal.ofReal θ * ∑ b ∈ t, volume (ball (c b) (r b))) := by
      simp_rw [hscale, ← Finset.mul_sum]
      ac_rfl
    _ ≤ ENNReal.ofReal ((4 : ℝ) ^ d) *
        ∑ b ∈ t, volume (E ∩ ball (c b) (r b)) := by gcongr
    _ ≤ ENNReal.ofReal ((4 : ℝ) ^ d) * volume E := by gcongr

/-- The weak `(1,1)` bound for the maximal function of an indicator,
with the explicit constant `4^d`. -/
lemma volume_maximalRegion_le {d : ℕ} {E : Set (Space d)}
    (hE : MeasurableSet E) {θ : ℝ} (hθ : 0 < θ) :
    volume (maximalRegion E θ) ≤ ENNReal.ofReal ((4 : ℝ) ^ d / θ) * volume E := by
  rw [(isOpen_maximalRegion E θ).measure_eq_iSup_isCompact volume]
  exact iSup_le (fun K ↦ iSup_le (fun hKΩ ↦ iSup_le (fun hK ↦
    volume_compact_subset_maximalRegion_le hE hθ hK hKΩ)))

/-- Almost every point of `E` belongs to its maximal region at every level below one.
This is an application of Mathlib's proved Lebesgue density theorem. -/
lemma ae_mem_maximalRegion {d : ℕ} (E : Set (Space d)) {θ : ℝ} (hθ : θ < 1) :
    ∀ᵐ x ∂volume.restrict E, x ∈ maximalRegion E θ := by
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div volume E] with x hx
  have hlevel : ENNReal.ofReal θ < 1 := ENNReal.ofReal_lt_one.mpr hθ
  have hevent : ∀ᶠ r : ℝ in 𝓝[>] 0,
      ENNReal.ofReal θ < volume (E ∩ closedBall x r) / volume (closedBall x r) :=
    hx.eventually (eventually_gt_nhds hlevel)
  have hpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  obtain ⟨r, havg, hr⟩ := (hevent.and hpos).exists
  have havg' : ENNReal.ofReal θ * volume (closedBall x r) <
      volume (E ∩ closedBall x r) :=
    (ENNReal.lt_div_iff_mul_lt (Or.inl (measure_closedBall_pos volume x hr).ne')
      (Or.inl measure_closedBall_lt_top.ne)).mp havg
  have hb := ball_ae_eq_closedBall x hr
  have hi := measure_congr (Filter.EventuallyEqSet.inter (ae_eq_refl E) hb)
  rw [← measure_congr hb, ← hi] at havg'
  exact ⟨x, r, hr, mem_ball_self hr, havg'⟩

lemma volume_sdiff_maximalRegion_eq_zero {d : ℕ} (E : Set (Space d))
    {θ : ℝ} (hθ : θ < 1) : volume (E \ maximalRegion E θ) = 0 := by
  have h := ae_mem_maximalRegion E hθ
  rw [ae_iff] at h
  change (volume.restrict E) (maximalRegion E θ)ᶜ = 0 at h
  rw [Measure.restrict_apply (isOpen_maximalRegion E θ).measurableSet.compl] at h
  rw [inter_comm] at h
  exact h

end LpSelfSimilar
