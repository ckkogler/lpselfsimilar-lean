module

public import LpSelfSimilar.Probability.ConditionalVarianceLaw
public import LpSelfSimilar.Probability.DiscreteConditionalLaw
public import LpSelfSimilar.Probability.ConditionalMoments

@[expose] public section

/-!
The canonical conditional variance for an independent parameter and a discrete
observation. For a finite real law, integrating this variance gives exactly the
parameter-average of the finite conditional-moment formula. Fubini's theorem
uses the integrability of the actual conditional variance, proved by Mathlib.
-/

open MeasureTheory ProbabilityTheory

namespace LpSelfSimilar

variable {T : Type*} [MeasurableSpace T]

lemma condVar_eq_variance_parameterizedConditionalLaw
    (ν : Measure T) [IsProbabilityMeasure ν] (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : T × ℝ → ℤ) (hf : Measurable f) (hX : MemLp (fun x : ℝ ↦ x) 2 μ) :
    condVar ((inferInstance : MeasurableSpace (T × ℤ)).comap (fun z ↦ (z.1, f z)))
      (fun z : T × ℝ ↦ z.2) (ν.prod μ) =ᵐ[ν.prod μ]
      fun z ↦ variance (fun x : ℝ ↦ x) (parameterizedConditionalLaw μ f hf (z.1, f z)) := by
  have hXp : MemLp (fun z : T × ℝ ↦ z.2) 2 (ν.prod μ) :=
    hX.comp_measurePreserving measurePreserving_snd
  apply (condVar_eq_variance_condDistrib (measurable_fst.prodMk hf) hXp).trans
  filter_upwards [ae_of_ae_map (measurable_fst.prodMk hf).aemeasurable
    (condDistrib_eq_parameterizedConditionalLaw ν μ f hf)] with z hz
  exact congrArg (variance (fun x : ℝ ↦ x)) hz

/-- Integrating over a discrete statistic uses precisely the finite fiber variance. -/
lemma integral_variance_parameterizedConditionalLaw (p : PMF ℝ) (hp : p.support.Finite)
    (f : T × ℝ → ℤ) (hf : Measurable f) (t : T) :
    (∫ x, variance (fun y : ℝ ↦ y)
      (parameterizedConditionalLaw p.toMeasure f hf (t, f (t, x))) ∂p.toMeasure) =
      FiniteProbability.meanConditionalVariance p hp (fun x ↦ f (t, x)) id := by
  classical
  rw [← FiniteProbability.expectation_eq_integral p hp]
  unfold FiniteProbability.meanConditionalVariance FiniteProbability.expectation
  apply Finset.sum_congr rfl
  intro x hx
  have hxb : f (t, x) ∈ (p.map (fun x ↦ f (t, x))).support := by
    rw [PMF.support_map]
    exact ⟨x, by simpa using hx, rfl⟩
  let b : (p.map (fun x ↦ f (t, x))).support := ⟨f (t, x), hxb⟩
  have hv : variance (fun y : ℝ ↦ y)
      (parameterizedConditionalLaw p.toMeasure f hf (t, f (t, x))) =
      FiniteProbability.fiberVariance p hp (fun x ↦ f (t, x)) id (f (t, x)) := by
    rw [parameterizedConditionalLaw_eq_conditionalPMF p f hf t b,
      FiniteProbability.fiberVariance_eq_conditional p hp (fun x ↦ f (t, x)) id b]
    exact (FiniteProbability.variance_eq_measure_variance _
      (Entropy.conditionalPMF_support_finite p hp (fun x ↦ f (t, x)) b) id).symm
  exact congrArg (fun v ↦ (p x).toReal * v) hv

/-- The expected canonical conditional variance equals the parameter-average
of the finite conditional variance formula. -/
theorem integral_condVar_parameterized_finite (ν : Measure T) [IsProbabilityMeasure ν]
    (p : PMF ℝ) (hp : p.support.Finite) (f : T × ℝ → ℤ) (hf : Measurable f) :
    (∫ z, condVar
      ((inferInstance : MeasurableSpace (T × ℤ)).comap (fun z ↦ (z.1, f z)))
      (fun z : T × ℝ ↦ z.2) (ν.prod p.toMeasure) z ∂ν.prod p.toMeasure) =
      ∫ t, FiniteProbability.meanConditionalVariance p hp (fun x ↦ f (t, x)) id ∂ν := by
  have hX : MemLp (fun x : ℝ ↦ x) 2 p.toMeasure :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2
      (FiniteProbability.integrable_of_finite_support p hp (fun x ↦ x ^ 2))
  have he := condVar_eq_variance_parameterizedConditionalLaw ν p.toMeasure f hf hX
  have hi : Integrable (fun z : T × ℝ ↦ variance (fun x : ℝ ↦ x)
      (parameterizedConditionalLaw p.toMeasure f hf (z.1, f z))) (ν.prod p.toMeasure) :=
    integrable_condVar.congr he
  rw [integral_congr_ae he, integral_prod _ hi]
  apply integral_congr_ae
  exact ae_of_all ν (integral_variance_parameterizedConditionalLaw p hp f hf)

end LpSelfSimilar
