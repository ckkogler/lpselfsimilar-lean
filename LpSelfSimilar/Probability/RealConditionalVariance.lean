module

public import LpSelfSimilar.Probability.RealConditionalLaw
public import LpSelfSimilar.Probability.KernelVariance

@[expose] public section

/-!
The variance of a regular conditional law agrees with Mathlib's conditional
variance. Both the ambient almost-everywhere identity and its trimmed-space form
are proved; the latter supports independent product sampling of conditional laws.
-/

open MeasureTheory ProbabilityTheory

namespace LpSelfSimilar

lemma condVar_eq_variance_realConditionalLaw {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] (hm : m ≤ mΩ) {P : Measure[mΩ] Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : MemLp X 2 P) :
    condVar m X P =ᵐ[P] fun ω ↦ variance (fun x : ℝ ↦ x) (realConditionalLaw m X P ω) := by
  have hfirst := condExp_eq_integral_realConditionalLaw hm hX.aemeasurable
    stronglyMeasurable_id (hX.integrable one_le_two)
  have hsecond := condExp_eq_integral_realConditionalLaw hm hX.aemeasurable
    (show StronglyMeasurable (fun x : ℝ ↦ x ^ 2) by fun_prop) hX.integrable_sq
  simp only [id_eq] at hfirst
  filter_upwards [condVar_ae_eq_condExp_sq_sub_sq_condExp hm hX, hfirst, hsecond,
    ae_of_ae_trim hm (realConditionalLaw_ae_memLp_two hm hX)] with ω hv h1 h2 hLp
  simp only [Pi.sub_apply, Pi.pow_def] at hv
  rw [hv, h1, h2, variance_eq_sub hLp]
  rfl

lemma condVar_eq_variance_realConditionalLaw_trim {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] (hm : m ≤ mΩ) {P : Measure[mΩ] Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : MemLp X 2 P) :
    condVar m X P =ᵐ[P.trim hm]
      fun ω ↦ variance (fun x : ℝ ↦ x) (realConditionalLaw m X P ω) := by
  have he := condVar_eq_variance_realConditionalLaw hm hX
  have hv := @stronglyMeasurable_variance_kernel Ω m (realConditionalLaw m X P) _
  exact ae_eq_trim_of_measurable hm stronglyMeasurable_condVar.measurable hv.measurable he

lemma integral_condVar_eq_integral_variance_realConditionalLaw {Ω : Type*}
    {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] (hm : m ≤ mΩ)
    {P : Measure[mΩ] Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : MemLp X 2 P) :
    (∫ ω, condVar m X P ω ∂P) =
      ∫ ω, variance (fun x : ℝ ↦ x) (realConditionalLaw m X P ω) ∂P.trim hm := by
  calc
    _ = ∫ ω, variance (fun x : ℝ ↦ x) (realConditionalLaw m X P ω) ∂P :=
      integral_congr_ae (condVar_eq_variance_realConditionalLaw hm hX)
    _ = _ := integral_trim hm (@stronglyMeasurable_variance_kernel Ω m (realConditionalLaw m X P) _)

end LpSelfSimilar
