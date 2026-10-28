module

public import LpSelfSimilar.Analysis.OpenSetMassRecurrence
public import LpSelfSimilar.Analysis.SmallSetMassContinuity

@[expose] public section

/-!
# Preserving the exact multiplier in an open-set mass recurrence

For an absolutely continuous finite real measure, the small-set mass modulus
is continuous. First let the enlarged cover multiplier decrease to its stated
value. Then let the volume budget increase to its endpoint. Both limits are
proved here, so neither a constant loss nor a strict endpoint remains.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace LpSelfSimilar.Analysis

/-- The open-set recurrence extends with its exact constant and its closed upper endpoint. -/
theorem smallSetMass_exact_recurrence_of_open_sets (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hac : μ ≪ volume) {r D : ℝ} (hD : 0 < D) (β : ℝ≥0∞) (hβ : β ≠ ∞)
    (hopen : ∀ U : Set ℝ, IsOpen U → volume U ≤ ENNReal.ofReal r →
      μ U ≤ β * smallSetMass μ volume (ENNReal.ofReal D * volume U))
    {t : ℝ} (ht : 0 < t) (htr : t ≤ r) :
    smallSetMass μ volume (ENNReal.ofReal t) ≤
      β * smallSetMass μ volume (ENNReal.ofReal (D * t)) := by
  have hc {s : ℝ} (hs : 0 < s) :
      ContinuousAt (fun u : ℝ => smallSetMass μ volume (ENNReal.ofReal u)) s :=
    (continuousOn_smallSetMass μ hac s hs.le).continuousAt (Ici_mem_nhds hs)
  have hstrict {s : ℝ} (hs : 0 < s) (hsr : s < r) :
      smallSetMass μ volume (ENNReal.ofReal s) ≤
        β * smallSetMass μ volume (ENNReal.ofReal (D * s)) := by
    have hlim : Tendsto
        (fun A : ℝ => β * smallSetMass μ volume (ENNReal.ofReal (A * s)))
        (𝓝[>] D) (𝓝 (β * smallSetMass μ volume (ENNReal.ofReal (D * s)))) :=
      (ENNReal.Tendsto.const_mul
        (Filter.Tendsto.comp (hc (mul_pos hD hs))
          ((continuous_id.mul_const s).tendsto D))
        (Or.inr hβ)).mono_left nhdsWithin_le_nhds
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with A hA
    exact smallSetMass_recurrence_of_open_sets μ hD hA β hopen hs hsr
  rcases htr.lt_or_eq with hlt | heq
  · exact hstrict ht hlt
  subst t
  have hleft : Tendsto (fun s : ℝ => smallSetMass μ volume (ENNReal.ofReal s))
      (𝓝[<] r) (𝓝 (smallSetMass μ volume (ENNReal.ofReal r))) :=
    (hc ht).mono_left nhdsWithin_le_nhds
  have hright : Tendsto
      (fun s : ℝ => β * smallSetMass μ volume (ENNReal.ofReal (D * s)))
      (𝓝[<] r) (𝓝 (β * smallSetMass μ volume (ENNReal.ofReal (D * r)))) :=
    (ENNReal.Tendsto.const_mul
      (Filter.Tendsto.comp (hc (mul_pos hD ht))
        ((continuous_const.mul continuous_id).tendsto r))
      (Or.inr hβ)).mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ht)] with s hsr hs
  exact hstrict hs hsr

end LpSelfSimilar.Analysis
