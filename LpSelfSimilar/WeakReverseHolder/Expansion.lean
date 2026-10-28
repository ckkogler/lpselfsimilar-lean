module

public import LpSelfSimilar.WeakReverseHolder.Constants
public import LpSelfSimilar.WeakReverseHolder.MaximalRegion

@[expose] public section

/-! The weighted set-expansion inequality obtained from the small-set hypothesis. -/

open MeasureTheory Metric Set
open scoped ENNReal

namespace LpSelfSimilar

/-- The measure version of equation (2.1). -/
def MeasureSmallSetHypothesis {d : ℕ} (ν : Measure (Space d)) (ε η : ℝ) : Prop :=
  ∀ (x : Space d) (r : ℝ), 0 < r → r < 1 →
    ∀ E : Set (Space d), MeasurableSet E → E ⊆ ball x r →
      volume E ≤ ENNReal.ofReal ε * volume (ball x r) →
        ν E ≤ ENNReal.ofReal η * ν (ball x (2 * r))

/-- Whitney covering and the exact overlap constant give the weighted estimate
on every compact subset of the maximal region. -/
lemma measure_inter_compact_le {d : ℕ} (hd : 1 ≤ d) (ν : Measure (Space d))
    {ε η : ℝ} (hε : 0 < ε) (hsmall : MeasureSmallSetHypothesis ν ε η)
    {E K : Set (Space d)} (hE : MeasurableSet E)
    (hvol : volume (maximalRegion E (maximalThreshold d ε)) ≤ volume (ball (0 : Space d) 1))
    (hK : IsCompact K) (hKΩ : K ⊆ maximalRegion E (maximalThreshold d ε)) :
    ν (E ∩ K) ≤ ENNReal.ofReal (coveringConstant d * η) *
      ν (maximalRegion E (maximalThreshold d ε)) := by
  classical
  let Ω := maximalRegion E (maximalThreshold d ε)
  change volume Ω ≤ volume (ball (0 : Space d) 1) at hvol
  change K ⊆ Ω at hKΩ
  change ν (E ∩ K) ≤ ENNReal.ofReal (coveringConstant d * η) * ν Ω
  have hΩ : IsOpen Ω := isOpen_maximalRegion E (maximalThreshold d ε)
  have hne : Ωᶜ.Nonempty := compl_nonempty_of_volume_le_unitBall hd hvol
  have hρ (x : Space d) (hx : x ∈ Ω) : 0 < whitneyRadius Ω x :=
    whitneyRadius_pos hΩ hne hx
  obtain ⟨s, hsΩ, hsfin, hKs⟩ := hK.elim_finite_subcover_image
    (b := Ω) (c := fun x : Space d ↦ ball x (whitneyRadius Ω x))
    (fun _ _ ↦ isOpen_ball) (by
      intro x hx
      exact mem_iUnion₂.mpr ⟨x, hKΩ hx, mem_ball_self (hρ x (hKΩ hx))⟩)
  have hKs' : K ⊆ ⋃ x ∈ hsfin.toFinset, ball x (whitneyRadius Ω x) := by
    simpa using hKs
  obtain ⟨t, hts, hdisj, hcover⟩ :=
    finite_disjoint_ball_cover hsfin.toFinset id (whitneyRadius Ω)
  have htΩ (x : Space d) (hx : x ∈ t) : x ∈ Ω := hsΩ (by simpa using hts hx)
  have hρt (x : Space d) (hx : x ∈ t) : 0 < whitneyRadius Ω x := hρ x (htΩ x hx)
  have hK4 : K ⊆ ⋃ x ∈ t, ball x (4 * whitneyRadius Ω x) := by
    intro y hy
    obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp (hKs' hy)
    obtain ⟨j, hj, hij⟩ := hcover i hi
    exact mem_iUnion₂.mpr ⟨j, hj, hij hyi⟩
  have hball (x : Space d) (hx : x ∈ t) :
      ν (E ∩ ball x (4 * whitneyRadius Ω x)) ≤
        ENNReal.ofReal η * ν (ball x (8 * whitneyRadius Ω x)) := by
    have hr := hρt x hx
    have hr4 : 0 < 4 * whitneyRadius Ω x := by positivity
    have hr8 : 0 < 8 * whitneyRadius Ω x := by positivity
    have hvol8 : volume (ball x (8 * whitneyRadius Ω x)) ≤ volume (ball (0 : Space d) 1) :=
      (measure_mono (whitney_eight_ball_subset hr)).trans hvol
    have hrad8 := radius_le_one_of_volume_ball_le hd x hr8 hvol8
    have hr4lt : 4 * whitneyRadius Ω x < 1 := by linarith
    obtain ⟨y, hy, hy21⟩ := exists_compl_mem_whitney_ball hne hr
    have hscale : volume (ball x (21 * whitneyRadius Ω x)) =
        ENNReal.ofReal (((21 : ℝ) / 4) ^ d) * volume (ball x (4 * whitneyRadius Ω x)) := by
      rw [show 21 * whitneyRadius Ω x = ((21 : ℝ) / 4) * (4 * whitneyRadius Ω x) by ring]
      exact volume_ball_scale x x (by norm_num) _
    have hportion : volume (E ∩ ball x (4 * whitneyRadius Ω x)) ≤
        ENNReal.ofReal ε * volume (ball x (4 * whitneyRadius Ω x)) := by
      calc
        volume (E ∩ ball x (4 * whitneyRadius Ω x)) ≤
            volume (E ∩ ball x (21 * whitneyRadius Ω x)) :=
          measure_mono (inter_subset_inter_right E (ball_subset_ball (by linarith)))
        _ ≤ ENNReal.ofReal (maximalThreshold d ε) * volume (ball x (21 * whitneyRadius Ω x)) :=
          volume_inter_ball_le_of_notMem_maximalRegion hy (by positivity) hy21
        _ = ENNReal.ofReal ε * volume (ball x (4 * whitneyRadius Ω x)) := by
          rw [hscale, ← mul_assoc, ← ENNReal.ofReal_mul (maximalThreshold_pos hε).le,
            maximalThreshold_ball_ratio]
    have hp := hsmall x (4 * whitneyRadius Ω x) hr4 hr4lt
      (E ∩ ball x (4 * whitneyRadius Ω x)) (hE.inter isOpen_ball.measurableSet)
      inter_subset_right hportion
    simpa only [show 2 * (4 * whitneyRadius Ω x) = 8 * whitneyRadius Ω x by ring] using hp
  have hEK : E ∩ K ⊆ ⋃ x ∈ t, E ∩ ball x (4 * whitneyRadius Ω x) := by
    rintro y ⟨hyE, hyK⟩
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp (hK4 hyK)
    exact mem_iUnion₂.mpr ⟨x, hx, hyE, hyx⟩
  calc
    ν (E ∩ K) ≤ ∑ x ∈ t, ν (E ∩ ball x (4 * whitneyRadius Ω x)) :=
      (measure_mono hEK).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ x ∈ t, ENNReal.ofReal η * ν (ball x (8 * whitneyRadius Ω x)) :=
      Finset.sum_le_sum hball
    _ = ENNReal.ofReal η * ∑ x ∈ t, ν (ball x (8 * whitneyRadius Ω x)) := by
      rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal η * ((21 ^ d : ℝ≥0∞) * ν Ω) := by
      gcongr
      exact sum_measure_whitney_eight_le ν hΩ t hρt hdisj
    _ = ENNReal.ofReal (coveringConstant d * η) * ν Ω := by
      rw [ofReal_coveringConstant_mul, mul_assoc]

lemma measure_le_beta_maximalRegion {d : ℕ} (hd : 1 ≤ d)
    (ν : Measure (Space d)) [IsFiniteMeasure ν] (hac : ν ≪ volume)
    {ε η : ℝ} (hε : ε ∈ Ioo 0 1) (hsmall : MeasureSmallSetHypothesis ν ε η)
    {E : Set (Space d)} (hE : MeasurableSet E)
    (hvol : volume (maximalRegion E (maximalThreshold d ε)) ≤ volume (ball (0 : Space d) 1)) :
    ν E ≤ ENNReal.ofReal (coveringConstant d * η) *
      ν (maximalRegion E (maximalThreshold d ε)) := by
  let Ω := maximalRegion E (maximalThreshold d ε)
  have hΩ : IsOpen Ω := isOpen_maximalRegion E (maximalThreshold d ε)
  have hnull : ν (E \ Ω) = 0 :=
    hac (volume_sdiff_maximalRegion_eq_zero E (maximalThreshold_lt_one hε.1 hε.2))
  have hbound : (ν.restrict E) Ω ≤ ENNReal.ofReal (coveringConstant d * η) * ν Ω := by
    rw [hΩ.measure_eq_iSup_isCompact (ν.restrict E)]
    refine iSup_le fun K ↦ iSup_le fun hKΩ ↦ iSup_le fun hK ↦ ?_
    rw [Measure.restrict_apply hK.measurableSet, inter_comm]
    exact measure_inter_compact_le hd ν hε.1 hsmall hE hvol hK hKΩ
  rw [Measure.restrict_apply hΩ.measurableSet, inter_comm] at hbound
  have hsplit := measure_inter_add_sdiff (μ := ν) E hΩ.measurableSet
  rw [hnull, add_zero] at hsplit
  exact hsplit ▸ hbound

/-- One expansion step: volume grows by at most `C/ε`, while mass grows by
at least `1/(Cη)`. -/
lemma exists_measure_expansion {d : ℕ} (hd : 1 ≤ d)
    (ν : Measure (Space d)) [IsFiniteMeasure ν] (hac : ν ≪ volume)
    {ε η : ℝ} (hε : ε ∈ Ioo 0 1) (hsmall : MeasureSmallSetHypothesis ν ε η)
    {E : Set (Space d)} (hE : MeasurableSet E)
    (hvol : ENNReal.ofReal (coveringConstant d / ε) * volume E ≤ volume (ball (0 : Space d) 1)) :
    ∃ Ω : Set (Space d), IsOpen Ω ∧
      volume Ω ≤ ENNReal.ofReal (coveringConstant d / ε) * volume E ∧
      ν E ≤ ENNReal.ofReal (coveringConstant d * η) * ν Ω := by
  let Ω := maximalRegion E (maximalThreshold d ε)
  have hv : volume Ω ≤ ENNReal.ofReal (coveringConstant d / ε) * volume E := by
    simpa only [four_pow_div_maximalThreshold hε.1] using
      volume_maximalRegion_le hE (maximalThreshold_pos (d := d) hε.1)
  exact ⟨Ω, isOpen_maximalRegion E _, hv,
    measure_le_beta_maximalRegion hd ν hac hε hsmall hE (hv.trans hvol)⟩

end LpSelfSimilar
