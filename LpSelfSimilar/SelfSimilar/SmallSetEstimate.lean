module

public import LpSelfSimilar.SelfSimilar.CompactSupport
public import LpSelfSimilar.SelfSimilar.StoppingWords
public import LpSelfSimilar.Geometry.SimilarityVolume
public import LpSelfSimilar.Analysis.SmallSetMass

@[expose] public section

/-!
Equation (2.2). A stopped image of the full-measure compact set either misses
the testing ball, contributing zero mass, or lies entirely in the doubled
ball, contributing its full probability there. The inverse-image volume
estimate bounds each such contribution by the absolute-continuity modulus.
-/

open MeasureTheory Metric Set
open scoped ENNReal NNReal BigOperators

namespace LpSelfSimilar

/-- The geometric contribution of one stopped similarity to (2.2). -/
lemma Similarity.preimage_mass_le {d : ℕ} (g : Similarity d) (ν : Measure (Space d))
    [IsProbabilityMeasure ν] {K : Set (Space d)} (hKnull : ν Kᶜ = 0) (hKmass : ν K = 1)
    {a D r : ℝ} (ha : 0 < a) (hD : 0 < D) (hr : 0 < r)
    (hdiam : ∀ y ∈ K, ∀ z ∈ K, dist y z ≤ D)
    (hlower : a * (r / D) ≤ g.ratio) (hupper : g.ratio ≤ r / D)
    (x : Space d) {E : Set (Space d)} (hE : MeasurableSet E) (hsub : E ⊆ ball x r) :
    ν (g ⁻¹' E) ≤ smallSetMass ν volume
      (ENNReal.ofReal (smallSetConstant d a D) * (volume E / volume (ball x r))) *
        ν (g ⁻¹' ball x (2 * r)) := by
  classical
  by_cases hhit : ∃ y ∈ K, g y ∈ ball x r
  · obtain ⟨y, hyK, hyB⟩ := hhit
    have hcontain : K ⊆ g ⁻¹' ball x (2 * r) := by
      intro z hz
      change dist (g z) x < 2 * r
      have htri := dist_triangle (g z) (g y) x
      rw [g.dist_eq] at htri
      have hdist := mul_le_mul_of_nonneg_left (hdiam z hz y hyK) g.ratio_pos.le
      have hscale := (le_div_iff₀ hD).mp hupper
      have hy := mem_ball.mp hyB
      linarith
    have hfull : ν (g ⁻¹' ball x (2 * r)) = 1 := by
      apply le_antisymm ((measure_mono (subset_univ _)).trans_eq measure_univ)
      rw [← hKmass]
      exact measure_mono hcontain
    rw [hfull, mul_one]
    exact measure_le_smallSetMass ν volume (hE.preimage g.measurable)
      (g.volume_preimage_le ha hD hr hlower x hE)
  · have hcontain : g ⁻¹' E ⊆ Kᶜ := by
      intro y hy hyK
      exact hhit ⟨y, hyK, hsub hy⟩
    rw [measure_mono_null hcontain hKnull]
    exact zero_le

namespace SelfSimilar.System

variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Equation (2.2), with the paper's diameter normalization replaced by the
explicit bound `D ≥ 1`. For `D = 1` its constant is `v_d * a⁻ᵈ`. -/
lemma small_set_estimate (S : System d ι) {ν : Measure (Space d)}
    [IsProbabilityMeasure ν] (hν : S.IsStationary ν)
    {K : Set (Space d)} (hKnull : ν Kᶜ = 0) (hKmass : ν K = 1)
    {a D : ℝ} (ha : 0 < a) (ha1 : a < 1) (hmin : ∀ i, a ≤ (S.map i).ratio)
    (hD : 1 ≤ D) (hdiam : ∀ y ∈ K, ∀ z ∈ K, dist y z ≤ D)
    (x : Space d) {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {E : Set (Space d)} (hE : MeasurableSet E) (hsub : E ⊆ ball x r) :
    ν E ≤ smallSetMass ν volume
      (ENNReal.ofReal (smallSetConstant d a D) * (volume E / volume (ball x r))) *
        ν (ball x (2 * r)) := by
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have ht : r / D ∈ Ioo 0 1 :=
    ⟨div_pos hr hD0, (div_lt_one hD0).mpr (hr1.trans_le hD)⟩
  obtain ⟨n, q, hdecomp, hscale⟩ := S.exists_stopped_decomposition hν ha ha1 hmin ht
  let b := smallSetMass ν volume
    (ENNReal.ofReal (smallSetConstant d a D) * (volume E / volume (ball x r)))
  change ν E ≤ b * ν (ball x (2 * r))
  calc
    ν E = ∑ w, S.wordWeight n w * ν ((q w) ⁻¹' E) := hdecomp E hE
    _ ≤ ∑ w, S.wordWeight n w * (b * ν ((q w) ⁻¹' ball x (2 * r))) := by
      apply Finset.sum_le_sum
      intro w _
      exact mul_le_mul' le_rfl ((q w).preimage_mass_le ν hKnull hKmass ha hD0 hr hdiam
        (hscale w).1.le (hscale w).2 x hE hsub)
    _ = b * ν (ball x (2 * r)) := by
      rw [hdecomp _ isOpen_ball.measurableSet, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      ac_rfl

end SelfSimilar.System
end LpSelfSimilar
