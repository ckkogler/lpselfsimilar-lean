module

public import LpSelfSimilar.Probability.MapProbability

public import LpSelfSimilar.Gaussian.SmallSummandsGeneral

@[expose] public section

/-!
The small-summand estimate for summands lying in arbitrary short intervals.
Translating by known centers changes neither variance nor detail, and the
variance bound is the sharp interval-radius bound from Popoviciu's inequality.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real Set

namespace LpSelfSimilar.Gaussian

lemma variance_le_radius_sq (μ : Measure ℝ) [IsProbabilityMeasure μ] {c R : ℝ}
    (hb : ∀ᵐ u ∂μ, |u - c| ≤ R) : variance (fun u : ℝ ↦ u) μ ≤ R ^ 2 := by
  have h : ∀ᵐ u ∂μ, u ∈ Icc (c - R) (c + R) := hb.mono (fun u hu ↦ by
    have h := abs_le.mp hu
    constructor <;> linarith)
  have hv := variance_le_sq_of_bounded h (by fun_prop)
  convert hv using 1 <;> try rfl
  ring

/-- Lemma 3.2 after subtracting arbitrary known centers. -/
theorem small_summands_intervals {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (c : Fin n → ℝ) {ε r : ℝ}
    (hε : 0 ≤ ε) (hr : 0 < r)
    (hb : ∀ i, ∀ᵐ u ∂μ i, |u - c i| ≤ ε * r) :
    detail (finiteConvolution μ) r ≤
      r ^ 2 / (r ^ 2 + ∑ i, variance (fun u : ℝ ↦ u) (μ i)) +
        generalSmallSummandConstant * ε := by
  let ν (i : Fin n) := (μ i).map (fun u ↦ u + -c i)
  haveI (i : Fin n) : IsProbabilityMeasure (ν i) := LpSelfSimilar.Probability.isProbabilityMeasure_map (by fun_prop)
  have hbound (i : Fin n) : ∀ᵐ u ∂ν i, |u| ≤ ε * r := by
    dsimp only [ν]
    rw [ae_map_iff (by fun_prop) ((isClosed_le continuous_abs continuous_const).measurableSet)]
    simpa only [sub_eq_add_neg] using hb i
  have hv (i : Fin n) : variance (fun u : ℝ ↦ u) (ν i) = variance (fun u : ℝ ↦ u) (μ i) := by
    dsimp only [ν]
    rw [variance_map (by fun_prop) (by fun_prop)]
    change variance (fun u : ℝ ↦ u + -c i) (μ i) = _
    exact variance_add_const (by fun_prop) (-c i)
  have h := small_summands ν hε hr hbound
  dsimp only [ν] at h
  rw [finiteConvolution_translate, detail_map_add] at h
  simp_rw [show ∀ i, variance (fun u : ℝ ↦ u) ((μ i).map (fun u ↦ u + -c i)) =
      variance (fun u : ℝ ↦ u) (μ i) from hv] at h
  exact h

end LpSelfSimilar.Gaussian
