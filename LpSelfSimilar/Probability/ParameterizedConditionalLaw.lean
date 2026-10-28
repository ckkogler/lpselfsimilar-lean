module

public import Mathlib.Probability.Kernel.CondDistrib

@[expose] public section

/-!
Conditioning an independent real variable on a parameter and a discrete statistic.

Disintegrating a kernel makes the conditional laws jointly measurable in the
parameter and recorded statistic. Associativity of disintegration then proves
that these are the actual conditional laws on the product probability space.
This supplies the random-shift interface for the grid observations of Section 3,
without assuming a conditional-law formula or a finite parameter space.
-/

open MeasureTheory ProbabilityTheory

namespace LpSelfSimilar

variable {T : Type*} [MeasurableSpace T]

/-- The joint law of a discrete statistic and a real variable, for each parameter. -/
noncomputable def parameterizedJointLaw (μ : Measure ℝ) (f : T × ℝ → ℤ)
    (_hf : Measurable f) : Kernel T (ℤ × ℝ) :=
  ((Kernel.id : Kernel T T).prod (Kernel.const T μ)).map
    (fun z : T × ℝ ↦ (f z, z.2))

instance (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : T × ℝ → ℤ)
    (hf : Measurable f) : IsMarkovKernel (parameterizedJointLaw μ f hf) := by
  unfold parameterizedJointLaw
  exact Kernel.IsMarkovKernel.map _ (hf.prodMk measurable_snd)

lemma parameterizedJointLaw_apply (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : T × ℝ → ℤ) (hf : Measurable f) (t : T) :
    parameterizedJointLaw μ f hf t = μ.map (fun x ↦ (f (t, x), x)) := by
  rw [parameterizedJointLaw, Kernel.map_apply _ (hf.prodMk measurable_snd),
    Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (hf.prodMk measurable_snd) measurable_prodMk_left]
  rfl

/-- The jointly measurable conditional law after recording the parameter and statistic. -/
noncomputable def parameterizedConditionalLaw (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : T × ℝ → ℤ) (hf : Measurable f) : Kernel (T × ℤ) ℝ :=
  (parameterizedJointLaw μ f hf).condKernel

instance (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : T × ℝ → ℤ)
    (hf : Measurable f) : IsMarkovKernel (parameterizedConditionalLaw μ f hf) := by
  unfold parameterizedConditionalLaw
  infer_instance

lemma compProd_parameterizedJointLaw (ν : Measure T) [IsProbabilityMeasure ν]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : T × ℝ → ℤ) (hf : Measurable f) :
    ν ⊗ₘ parameterizedJointLaw μ f hf =
      (ν.prod μ).map (fun z ↦ (z.1, (f z, z.2))) := by
  have hm : Measurable (fun z : T × ℝ ↦ (z.1, (f z, z.2))) :=
    measurable_fst.prodMk (hf.prodMk measurable_snd)
  ext s hs
  rw [Measure.compProd_apply hs, Measure.map_apply hm hs, Measure.prod_apply (hm hs)]
  apply lintegral_congr
  intro t
  have ht : Measurable (fun x : ℝ ↦ (f (t, x), x)) :=
    (hf.comp measurable_prodMk_left).prodMk measurable_id
  rw [parameterizedJointLaw_apply, Measure.map_apply ht (measurable_prodMk_left hs)]
  rfl

/-- The observation and original variable have the reconstructed joint law. -/
theorem parameterizedConditionalLaw_disintegrate (ν : Measure T) [IsProbabilityMeasure ν]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : T × ℝ → ℤ) (hf : Measurable f) :
    (ν.prod μ).map (fun z ↦ ((z.1, f z), z.2)) =
      (ν.prod μ).map (fun z ↦ (z.1, f z)) ⊗ₘ parameterizedConditionalLaw μ f hf := by
  let κ := parameterizedJointLaw μ f hf
  have hj : (ν ⊗ₘ κ.fst) ⊗ₘ κ.condKernel =
      (ν.prod μ).map (fun z ↦ ((z.1, f z), z.2)) := by
    rw [← Measure.compProd_assoc, Kernel.disintegrate,
      compProd_parameterizedJointLaw,
      Measure.map_map (by fun_prop) (measurable_fst.prodMk (hf.prodMk measurable_snd))]
    rfl
  have hm : ν ⊗ₘ κ.fst = (ν.prod μ).map (fun z ↦ (z.1, f z)) := by
    have h := congrArg Measure.fst hj
    rw [Measure.fst_compProd] at h
    simpa only [Measure.fst, Measure.map_map measurable_fst
      ((measurable_fst.prodMk hf).prodMk measurable_snd), Function.comp_def] using h
  rw [← hm]
  exact hj.symm

/-- These kernels agree with Mathlib's actual regular conditional distribution. -/
theorem condDistrib_eq_parameterizedConditionalLaw (ν : Measure T) [IsProbabilityMeasure ν]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : T × ℝ → ℤ) (hf : Measurable f) :
    condDistrib (fun z : T × ℝ ↦ z.2) (fun z ↦ (z.1, f z)) (ν.prod μ) =ᵐ[
      (ν.prod μ).map (fun z ↦ (z.1, f z))] parameterizedConditionalLaw μ f hf := by
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (measurable_fst.prodMk hf) measurable_snd
  exact parameterizedConditionalLaw_disintegrate ν μ f hf

end LpSelfSimilar
