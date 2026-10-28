module

public import LpSelfSimilar.Analysis.SupportedDensity
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-!
A continuous density of a measure carried by a compact set is compactly
supported. Positivity of Lebesgue measure on open sets upgrades the almost-
everywhere vanishing to pointwise vanishing off the closed support set.
-/

open MeasureTheory Set

namespace LpSelfSimilar

lemma hasCompactSupport_of_density {μ : Measure ℝ} {f : ℝ → ℝ}
    (hf : Integrable f volume) (hn : ∀ x, 0 ≤ f x) (hc : Continuous f)
    (hμ : μ = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)))
    {K : Set ℝ} (hK : IsCompact K) (hnull : μ Kᶜ = 0) : HasCompactSupport f := by
  have hclosed := hK.isClosed
  have heq := density_indicator_ae_eq hf hn hμ hclosed.measurableSet hnull
  have hzero : f =ᵐ[volume.restrict Kᶜ] (fun _ ↦ 0) := by
    apply (ae_restrict_iff' hclosed.measurableSet.compl).mpr
    filter_upwards [heq] with x hx hxK
    simpa only [indicator_of_notMem hxK f] using hx.symm
  have hz := MeasureTheory.Measure.eqOn_open_of_ae_eq hzero hclosed.isOpen_compl hc.continuousOn
    continuous_const.continuousOn
  apply hK.of_isClosed_subset (isClosed_tsupport f)
  apply closure_minimal _ hclosed
  intro x hx
  by_contra hxK
  exact hx (hz hxK)

end LpSelfSimilar
