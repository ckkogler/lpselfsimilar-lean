module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Vanishing integral tails at scale zero

A decreasing sequence of scale intervals (0,r_n] with r_n tending to zero
has empty intersection. Integrability on the initial interval therefore makes
the actual tail integrals tend to zero by dominated convergence.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace LpSelfSimilar.Analysis

/-- Integrable tails vanish along decreasing scales tending to zero. -/
theorem tendsto_integral_Ioc_zero_of_antitone_scale {g : ℝ → ℝ} {r : ℕ → ℝ}
    (hr : Antitone r) (hrlim : Tendsto r atTop (𝓝 0))
    (hi : IntegrableOn g (Ioc 0 (r 0))) :
    Tendsto (fun n => ∫ x in Ioc 0 (r n), g x) atTop (𝓝 0) := by
  have hs : Antitone (fun n => Ioc 0 (r n)) := by
    intro n m hnm
    exact Ioc_subset_Ioc le_rfl (hr hnm)
  have he : (⋂ n, Ioc 0 (r n)) = ∅ := by
    ext x
    simp only [mem_iInter, mem_Ioc, mem_empty_iff_false, iff_false]
    intro hx
    have hp : 0 < x := (hx 0).1
    have hev : ∀ᶠ n in atTop, r n < x := (tendsto_order.1 hrlim).2 x hp
    obtain ⟨n, hn⟩ := hev.exists
    exact (not_lt_of_ge (hx n).2) hn
  simpa only [he, setIntegral_empty] using
    Antitone.tendsto_setIntegral (fun n => measurableSet_Ioc) hs hi

end LpSelfSimilar.Analysis
