module

public import LpSelfSimilar.WeakReverseHolder.SharpSourceStopping
public import LpSelfSimilar.WeakReverseHolder.SharpSourceConstants
public import LpSelfSimilar.WeakReverseHolder.SharpSourceCovering

/-!
# Contraction of the density superlevel mass

Lebesgue differentiation and stopping at powers of six give the compact-set estimate.
Inner regularity removes the compact restriction; absolute continuity removes
the null exceptional set of non-Lebesgue points.
-/

@[expose] public section

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

namespace LpSelfSimilar

theorem sharp_source_density_tail_contraction {d : ℕ} {f : Space d → ℝ}
    (hf : Integrable f volume) (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    {A ε η : ℝ} (hA : 2 < A) (hη : 0 ≤ η) (hAε : 2 * (2 : ℝ) ^ d ≤ A * ε)
    (hsmall : SmallSetHypothesis f ε η)
    {t : ℝ} (ht : sharpStoppingThreshold f ≤ t) :
    volume.withDensity (fun x => ENNReal.ofReal (f x)) {x | A * t < f x} ≤
      ENNReal.ofReal (2 * (6 : ℝ) ^ d * η) *
        volume.withDensity (fun x => ENNReal.ofReal (f x)) {x | t < f x} := by
  let ν := volume.withDensity (fun x => ENNReal.ofReal (f x))
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity hf.lintegral_lt_top.ne
  have hac : ν ≪ volume := withDensity_absolutelyContinuous _ _
  let P := fun x => Tendsto (sharpSourceAverage f x) atTop (𝓝 (f x))
  have hP : ∀ᵐ x ∂ν, P x := hac.ae_le (sharp_ae_source_differentiation hf)
  let N := toMeasurable ν {x | ¬ P x}
  let G := Nᶜ
  have hN : ν N = 0 := by
    rw [show N = toMeasurable ν {x | ¬ P x} from rfl, measure_toMeasurable]
    exact ae_iff.mp hP
  have hG : MeasurableSet G := (measurableSet_toMeasurable _ _).compl
  have hGae : ∀ᵐ x ∂ν, x ∈ G := by
    rw [ae_iff]
    simpa [G] using hN
  have hGP {x : Space d} (hx : x ∈ G) : P x := by
    by_contra h
    exact hx (subset_toMeasurable ν _ h)
  let E := {x | A * t < f x}
  have hE : MeasurableSet E := measurableSet_lt measurable_const hfm
  change ν E ≤ ENNReal.ofReal (2 * (6 : ℝ) ^ d * η) * ν {x | t < f x}
  rw [← ν.measure_inter_eq_of_ae (s := E) hGae, inter_comm G E,
    (hE.inter hG).measure_eq_iSup_isCompact ν]
  refine iSup_le fun K => iSup_le fun hKG => iSup_le fun hK => ?_
  apply sharp_source_compact_level_mass_bound hf hfm hf0 (by linarith)
    ((sharpStoppingThreshold_pos hf0).trans_le ht) hη hAε hsmall hK
    (fun x hx => (hKG hx).1)
  intro x hx
  have hxt := (hKG hx).1
  have ht0 := (sharpStoppingThreshold_pos hf0).trans_le ht
  exact sharp_source_stopping_ball hf hf0 ht (hGP (hKG hx).2) (by
    change A * t < f x at hxt
    nlinarith)

theorem weak_reverse_holder_level_recurrence_of_measurable {d : ℕ} (hd : 1 ≤ d)
    {f : Space d → ℝ} (hf_nonneg : ∀ x, 0 ≤ f x) (hf : Integrable f volume)
    (hfm : Measurable f) {ε η : ℝ} (hε : ε ∈ Ioo 0 1) (hη : 0 ≤ η)
    (hsmall : SmallSetHypothesis f ε η) {t : ℝ} (ht : sharpStoppingThreshold f ≤ t) :
    (∫ x in {x | (sharpCoveringConstant d / ε) * t < f x}, f x) ≤
      (2 * (6 : ℝ) ^ d * η) * ∫ x in {x | t < f x}, f x := by
  have hA2 : 2 < sharpCoveringConstant d / ε := by
    rw [lt_div_iff₀ hε.1]
    linarith [eighteen_le_sharpCoveringConstant hd, hε.2]
  have hcost : 2 * (2 : ℝ) ^ d ≤ sharpCoveringConstant d := by
    have h : 2 * (2 : ℝ) ^ d ≤ 2 * (8 : ℝ) ^ d := by gcongr; norm_num
    exact h.trans (dyadic_contraction_lt_sharp_constant hd).le
  have hAε : 2 * (2 : ℝ) ^ d ≤ (sharpCoveringConstant d / ε) * ε := by
    rwa [div_mul_cancel₀ _ hε.1.ne']
  have h := sharp_source_density_tail_contraction hf hfm hf_nonneg hA2 hη hAε hsmall ht
  rw [sharp_density_measure_apply hf hf_nonneg (measurableSet_lt measurable_const hfm),
    sharp_density_measure_apply hf hf_nonneg (measurableSet_lt measurable_const hfm),
    ← ENNReal.ofReal_mul (by positivity)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity)
    (integral_nonneg (fun x => hf_nonneg x)))).mp h

/-- The exact strict-superlevel recurrence (2.2) in the proof of Kittle–Kogler,
Lemma 2.1. Its constant is `2 * 6^d * η`, and its expansion is `18^d / ε`.
The explicit threshold is positive for every nonnegative integrable function. -/
theorem weak_reverse_holder_level_recurrence {d : ℕ} (hd : 1 ≤ d)
    {f : Space d → ℝ} (hf_nonneg : ∀ x, 0 ≤ f x) (hf : Integrable f volume)
    {ε η : ℝ} (hε : ε ∈ Ioo 0 1) (hη : 0 ≤ η)
    (hsmall : SmallSetHypothesis f ε η) {t : ℝ} (ht : sharpStoppingThreshold f ≤ t) :
    (∫ x in {x | (sharpCoveringConstant d / ε) * t < f x}, f x) ≤
      (2 * (6 : ℝ) ^ d * η) * ∫ x in {x | t < f x}, f x := by
  let g : Space d → ℝ := fun x => max 0 (hf.aestronglyMeasurable.mk f x)
  have hgm : Measurable g := measurable_const.max hf.aestronglyMeasurable.measurable_mk
  have hg0 (x : Space d) : 0 ≤ g x := le_max_left _ _
  have heq : f =ᵐ[volume] g := by
    filter_upwards [hf.aestronglyMeasurable.ae_eq_mk] with x hx
    simp only [g, ← hx, max_eq_right (hf_nonneg x)]
  have hgi : Integrable g volume := hf.congr heq
  have hset (E : Set (Space d)) : (∫ x in E, g x) = ∫ x in E, f x :=
    integral_congr_ae (ae_restrict_of_ae heq.symm)
  have hgsmall : SmallSetHypothesis g ε η := by
    intro x r hr hr1 E hE hsub hvol
    rw [hset, hset]
    exact hsmall x r hr hr1 E hE hsub hvol
  have hthreshold : sharpStoppingThreshold g = sharpStoppingThreshold f := by
    unfold sharpStoppingThreshold
    rw [integral_congr_ae heq]
  have hlevel (u : ℝ) : (∫ x in {x | u < g x}, g x) = ∫ x in {x | u < f x}, f x := by
    rw [hset]
    apply setIntegral_congr_set
    filter_upwards [heq] with x hx
    simp only [hx]
  have h := weak_reverse_holder_level_recurrence_of_measurable hd hg0 hgi hgm hε hη
    hgsmall (hthreshold.symm ▸ ht)
  simpa only [hlevel] using h

end LpSelfSimilar
