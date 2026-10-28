module

public import LpSelfSimilar.Analysis.DensityUniqueness
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Topology.Algebra.Support

@[expose] public section

/-!
A measure carried by a measurable set has a density representative vanishing
pointwise off that set. This permits a decrease of the integrability exponent
on a finite-volume support while retaining the exact measure identity.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LpSelfSimilar

lemma density_indicator_ae_eq {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} {f : X → ℝ} (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x)
    (hrep : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (f x)))
    {K : Set X} (hK : MeasurableSet K) (hnull : ν Kᶜ = 0) : K.indicator f =ᵐ[μ] f := by
  rw [hrep] at hnull
  have hz := (withDensity_apply_eq_zero' hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal).mp hnull
  have hzAE : ∀ᵐ x ∂μ, x ∉ {x | ENNReal.ofReal (f x) ≠ 0} ∩ Kᶜ := by
    apply ae_iff.mpr
    convert hz using 1
    congr 1
    ext x
    simp
  filter_upwards [hzAE] with x hx
  by_cases hxK : x ∈ K
  · simp [hxK]
  · have hx0 : ENNReal.ofReal (f x) = 0 := by
      by_contra hh
      exact hx ⟨hh, hxK⟩
    have hfz : f x = 0 := le_antisymm (ENNReal.ofReal_eq_zero.mp hx0) (hf0 x)
    simp [hxK, hfz]

/-- Choose a pointwise supported density at any smaller exponent. -/
theorem exists_supported_density_memLp {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} {f : X → ℝ} (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x)
    (hrep : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (f x)))
    {K : Set X} (hK : MeasurableSet K) (hnull : ν Kᶜ = 0) (hfinite : μ K ≠ ⊤)
    {p q : ℝ≥0∞} (hLp : MemLp f q μ) (hpq : p ≤ q) :
    ∃ g : X → ℝ, (∀ x, 0 ≤ g x) ∧ Integrable g μ ∧
      ν = μ.withDensity (fun x ↦ ENNReal.ofReal (g x)) ∧
      MemLp g p μ ∧ (∀ x, x ∉ K → g x = 0) := by
  let g := K.indicator f
  have heq : g =ᵐ[μ] f := density_indicator_ae_eq hf hf0 hrep hK hnull
  have hgLp : MemLp g q μ := (memLp_congr_ae heq).mpr hLp
  have hgzero : ∀ x, x ∉ K → g x = 0 := fun x hx ↦ indicator_of_notMem hx _
  refine ⟨g, (fun x ↦ indicator_nonneg (fun x _ ↦ hf0 x) x),
    hf.congr heq.symm, ?_, hgLp.mono_exponent_of_measure_support_ne_top hgzero hfinite hpq, hgzero⟩
  rw [hrep]
  exact withDensity_congr_ae (heq.symm.fun_comp ENNReal.ofReal)

end LpSelfSimilar
