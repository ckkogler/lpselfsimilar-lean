module

public import LpSelfSimilar.SelfSimilar.SmallSetEstimate
public import LpSelfSimilar.WeakReverseHolder.MeasureForm

@[expose] public section

/-!
Theorem 1.1 of `the earlier version of the same work`. Compact support, stopping and (2.2) are derived
from stationarity and strict contraction. Uniform absolute continuity supplies
the small-set hypothesis for Lemma 2.1, whose exact exponent then gives `p > 1`.
The final public theorem has real nonnegative weights and the explicit
pushforward stationarity equation; no geometric or analytic hypotheses are hidden.
-/

open MeasureTheory Metric Set
open scoped ENNReal NNReal BigOperators

namespace LpSelfSimilar

namespace SelfSimilar.System

variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Absolute continuity and (2.2) provide the small-set criterion for every
positive target mass ratio. The compact set and its diameter are derived here. -/
lemma exists_small_set_hypothesis (S : System d ι) {ν : Measure (Space d)}
    [IsProbabilityMeasure ν] (hν : S.IsStationary ν) (hac : ν ≪ volume)
    {η : ℝ} (hη : 0 < η) :
    ∃ ε : ℝ, ε ∈ Ioo 0 1 ∧ MeasureSmallSetHypothesis ν ε η := by
  obtain ⟨K, _, hKnull, hKmass, D, hD, hdiam⟩ := S.exists_compact_full_measure hν
  obtain ⟨a, ha, ha1, hmin⟩ := S.exists_min_ratio
  have hC : 0 < smallSetConstant d a D :=
    smallSetConstant_pos ha (lt_of_lt_of_le zero_lt_one hD)
  obtain ⟨δ, hδ, hmass⟩ := exists_pos_smallSetMass_le ν volume hac hη
  obtain ⟨ε, hε0, hεbound⟩ := exists_between
    (lt_min zero_lt_one (div_pos hδ hC))
  have hε1 : ε < 1 := hεbound.trans_le (min_le_left _ _)
  have hCε : smallSetConstant d a D * ε ≤ δ := by
    have h := (lt_div_iff₀ hC).mp (hεbound.trans_le (min_le_right _ _))
    nlinarith
  refine ⟨ε, ⟨hε0, hε1⟩, ?_⟩
  intro x r hr hr1 E hE hsub hvol
  have harg : ENNReal.ofReal (smallSetConstant d a D) *
      (volume E / volume (ball x r)) ≤ ENNReal.ofReal δ := by
    calc
      ENNReal.ofReal (smallSetConstant d a D) * (volume E / volume (ball x r)) ≤
          ENNReal.ofReal (smallSetConstant d a D) * ENNReal.ofReal ε :=
        mul_le_mul' le_rfl ((ENNReal.div_le_iff (measure_ball_pos volume x hr).ne'
          measure_ball_ne_top).mpr hvol)
      _ = ENNReal.ofReal (smallSetConstant d a D * ε) := (ENNReal.ofReal_mul hC.le).symm
      _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hCε
  exact (S.small_set_estimate hν hKnull hKmass ha ha1 hmin hD hdiam x hr hr1 hE hsub).trans
    (mul_le_mul' ((smallSetMass_mono ν volume harg).trans hmass) le_rfl)

/-- Higher integrability of the canonical Radon–Nikodym density of a stationary measure. -/
theorem higher_integrability (S : System d ι) (hd : 1 ≤ d) {ν : Measure (Space d)}
    [IsProbabilityMeasure ν] (hν : S.IsStationary ν) (hac : ν ≪ volume) :
    ∃ p : ℝ, 1 < p ∧ MemLp (density ν volume) (ENNReal.ofReal p) volume := by
  obtain ⟨η, hη0, hη1⟩ := exists_between (inv_pos.mpr (coveringConstant_pos d))
  obtain ⟨ε, hε, hsmall⟩ := S.exists_small_set_hypothesis hν hac hη0
  exact ⟨lemmaExponent d ε η, weak_reverse_holder_measure hd hac hε ⟨hη0, hη1⟩ hsmall⟩

end SelfSimilar.System

/-- **Theorem 1.1.** Every absolutely continuous stationary probability measure
for a finite nonempty system of contracting Euclidean similarities has an
everywhere nonnegative integrable density in `L^p` for some real `p > 1`.

The real weights may vanish. Ratios are positive by the definition of
`Similarity`; strict contraction is the only additional condition on the maps.
Compact support and the small-set estimate are proved from these hypotheses.
-/
theorem self_similar_higher_integrability {d : ℕ} (hd : 1 ≤ d)
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (g : ι → Similarity d) (hg : ∀ i, (g i).ratio < 1)
    (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i) (hsum : ∑ i, weight i = 1)
    (ν : Measure (Space d)) [IsProbabilityMeasure ν]
    (hstationary : ν = ∑ i, ENNReal.ofReal (weight i) • ν.map (g i))
    (hac : ν ≪ volume) :
    ∃ f : Space d → ℝ, (∀ x, 0 ≤ f x) ∧ Integrable f volume ∧
      ν = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) ∧
      ∃ p : ℝ, 1 < p ∧ MemLp f (ENNReal.ofReal p) volume := by
  let S : SelfSimilar.System d ι := {
    map := g
    contracting := hg
    weight := fun i ↦ NNReal.mk (weight i) (hweight i)
    weight_sum := by
      apply NNReal.eq
      simpa using hsum }
  have hν : S.IsStationary ν := by
    change ν = ∑ i, (NNReal.mk (weight i) (hweight i) : ℝ≥0∞) • ν.map (g i)
    simpa only [ENNReal.ofReal_eq_coe_nnreal (hweight _)] using hstationary
  exact ⟨density ν volume, density_nonneg ν volume, integrable_density ν volume,
    (withDensity_density ν volume hac).symm, S.higher_integrability hd hν hac⟩

end LpSelfSimilar
