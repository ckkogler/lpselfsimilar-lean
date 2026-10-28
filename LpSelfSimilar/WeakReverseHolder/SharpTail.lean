module

public import LpSelfSimilar.WeakReverseHolder.SharpStopping
public import LpSelfSimilar.WeakReverseHolder.SharpCovering

/-!
# Contraction of the density superlevel mass

Lebesgue differentiation and dyadic stopping give the compact-set estimate.
Inner regularity removes the compact restriction; absolute continuity removes
the null exceptional set of non-Lebesgue points.
-/

@[expose] public section

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

namespace LpSelfSimilar

theorem sharp_density_tail_contraction {d : ℕ} {f : Space d → ℝ}
    (hf : Integrable f volume) (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    {A ε η : ℝ} (hA : 2 < A) (hη : 0 ≤ η) (hAε : 2 ≤ A * ε)
    (hsmall : SmallSetHypothesis f ε η)
    {t : ℝ} (ht : sharpStoppingThreshold f ≤ t) :
    volume.withDensity (fun x => ENNReal.ofReal (f x)) {x | A * t ≤ f x} ≤
      ENNReal.ofReal (2 * (8 : ℝ) ^ d * η) *
        volume.withDensity (fun x => ENNReal.ofReal (f x)) {x | t ≤ f x} := by
  let ν := volume.withDensity (fun x => ENNReal.ofReal (f x))
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity hf.lintegral_lt_top.ne
  have hac : ν ≪ volume := withDensity_absolutelyContinuous _ _
  let P := fun x => Tendsto (sharpDyadicAverage f x) atTop (𝓝 (f x))
  have hP : ∀ᵐ x ∂ν, P x := hac.ae_le (sharp_ae_dyadic_differentiation hf)
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
  let E := {x | A * t ≤ f x}
  have hE : MeasurableSet E := measurableSet_le measurable_const hfm
  change ν E ≤ ENNReal.ofReal (2 * (8 : ℝ) ^ d * η) * ν {x | t ≤ f x}
  rw [← ν.measure_inter_eq_of_ae (s := E) hGae, inter_comm G E,
    (hE.inter hG).measure_eq_iSup_isCompact ν]
  refine iSup_le fun K => iSup_le fun hKG => iSup_le fun hK => ?_
  apply sharp_compact_level_mass_bound hf hfm hf0 (by linarith)
    ((sharpStoppingThreshold_pos hf0).trans_le ht) hη hAε hsmall hK
    (fun x hx => (hKG hx).1)
  intro x hx
  have hxt := (hKG hx).1
  have ht0 := (sharpStoppingThreshold_pos hf0).trans_le ht
  exact sharp_exists_stopping_ball hf hf0 ht (hGP (hKG hx).2) (by
    change A * t ≤ f x at hxt
    nlinarith)

end LpSelfSimilar
