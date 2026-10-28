module

public import LpSelfSimilar.Probability.MapProbability

public import LpSelfSimilar.Gaussian.SharpSmallSummands

@[expose] public section

/-!
Revised Lemma 3.2 for arbitrary deterministic centers, preserving the exact
error 30 epsilon. Translation changes neither variance nor Gaussian detail.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real Set

namespace LpSelfSimilar.Gaussian

/-- Lemma 3.2 after subtracting arbitrary known centers. -/
theorem small_summands_intervals_explicit {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (c : Fin n → ℝ) {ε r : ℝ}
    (hε : 0 ≤ ε) (hr : 0 < r)
    (hb : ∀ i, ∀ᵐ u ∂μ i, |u - c i| ≤ ε * r) :
    detail (finiteConvolution μ) r ≤
      r ^ 2 / (r ^ 2 + ∑ i, variance (fun u : ℝ ↦ u) (μ i)) +
        30 * ε := by
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
  have h := small_summands_explicit ν hε hr hbound
  dsimp only [ν] at h
  rw [finiteConvolution_translate, detail_map_add] at h
  simp_rw [show ∀ i, variance (fun u : ℝ ↦ u) ((μ i).map (fun u ↦ u + -c i)) =
      variance (fun u : ℝ ↦ u) (μ i) from hv] at h
  exact h


end LpSelfSimilar.Gaussian
