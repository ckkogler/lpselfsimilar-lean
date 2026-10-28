module

public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.CondVar

@[expose] public section

/-!
Regular conditional laws of real variables given arbitrary sub-sigma-algebras.
Only the output space R is required to be standard Borel. Conditioning uses the
identity into the original sample space equipped with the smaller sigma-algebra,
so no countable-generation assumption is introduced.
-/

open MeasureTheory ProbabilityTheory

namespace LpSelfSimilar

/-- The actual regular conditional distribution of a real variable given `m`. -/
noncomputable def realConditionalLaw {Ω : Type*} (m : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (X : Ω → ℝ) (P : Measure[mΩ] Ω) [IsFiniteMeasure P] :
    @Kernel Ω ℝ m inferInstance :=
  @condDistrib Ω Ω ℝ _ _ _ mΩ m X id P _

instance {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (X : Ω → ℝ) (P : Measure[mΩ] Ω) [IsFiniteMeasure P] :
    IsMarkovKernel (realConditionalLaw m X P) := by
  unfold realConditionalLaw
  infer_instance

lemma realConditionalLaw_comp_trim {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] (hm : m ≤ mΩ) {P : Measure[mΩ] Ω} [IsFiniteMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P) :
    realConditionalLaw m X P ∘ₘ P.trim hm = P.map X := by
  rw [realConditionalLaw, trim_eq_map hm]
  exact condDistrib_comp_map (mβ := m)
    (@Measurable.aemeasurable Ω Ω mΩ m id P (measurable_id'' hm)) hX

lemma compProd_trim_realConditionalLaw {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] (hm : m ≤ mΩ) {P : Measure[mΩ] Ω} [IsFiniteMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P) :
    P.trim hm ⊗ₘ realConditionalLaw m X P =
      @Measure.map Ω (Ω × ℝ) mΩ (m.prod inferInstance) (fun ω ↦ (ω, X ω)) P := by
  rw [realConditionalLaw, trim_eq_map hm]
  exact compProd_map_condDistrib (mβ := m)
    (@Measurable.aemeasurable Ω Ω mΩ m id P (measurable_id'' hm)) hX

/-- Conditional expectations of functions of X are integrals of the conditional law. -/
lemma condExp_eq_integral_realConditionalLaw {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] (hm : m ≤ mΩ) {P : Measure[mΩ] Ω} [IsFiniteMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P) {f : ℝ → ℝ}
    (hf : StronglyMeasurable f) (hi : Integrable (fun ω ↦ f (X ω)) P) :
    P[fun ω ↦ f (X ω) | m] =ᵐ[P] fun ω ↦ ∫ x, f x ∂realConditionalLaw m X P ω := by
  simpa only [realConditionalLaw, MeasurableSpace.comap_id, id_eq] using
    condExp_ae_eq_integral_condDistrib (measurable_id'' hm) hX hf hi

/-- Almost-everywhere conditional support, including a dependence on the recorded outcome. -/
lemma realConditionalLaw_ae_support {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] (hm : m ≤ mΩ) {P : Measure[mΩ] Ω} [IsFiniteMeasure P]
    {X : Ω → ℝ} (hX : Measurable[mΩ] X) {s : Set (Ω × ℝ)}
    (hs : MeasurableSet[m.prod inferInstance] s) (hb : ∀ᵐ ω ∂P, (ω, X ω) ∈ s) :
    ∀ᵐ ω ∂P.trim hm, ∀ᵐ x ∂realConditionalLaw m X P ω, (ω, x) ∈ s := by
  apply Measure.ae_ae_of_ae_compProd
  rw [compProd_trim_realConditionalLaw (m := m) hm hX.aemeasurable]
  exact (ae_map_iff (mβ := m.prod inferInstance)
    (@Measurable.aemeasurable Ω (Ω × ℝ) mΩ (m.prod inferInstance)
      (fun ω ↦ (ω, X ω)) P ((measurable_id'' hm).prodMk hX)) hs).mpr hb

/-- Integrability passes to almost every conditional law. -/
lemma realConditionalLaw_ae_integrable {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] (hm : m ≤ mΩ) {P : Measure[mΩ] Ω} [IsFiniteMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P) {f : ℝ → ℝ}
    (hf : StronglyMeasurable f) (hi : Integrable (fun ω ↦ f (X ω)) P) :
    ∀ᵐ ω ∂P.trim hm, Integrable f (realConditionalLaw m X P ω) := by
  apply Measure.ae_integrable_of_integrable_comp
  rw [realConditionalLaw_comp_trim hm hX]
  exact (integrable_map_measure hf.aestronglyMeasurable hX).2 hi

/-- Square integrability passes to almost every conditional law. -/
lemma realConditionalLaw_ae_memLp_two {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] (hm : m ≤ mΩ) {P : Measure[mΩ] Ω} [IsFiniteMeasure P]
    {X : Ω → ℝ} (hX : MemLp X 2 P) :
    ∀ᵐ ω ∂P.trim hm, MemLp (fun x : ℝ ↦ x) 2 (realConditionalLaw m X P ω) := by
  filter_upwards [realConditionalLaw_ae_integrable hm hX.aemeasurable
    (show StronglyMeasurable (fun x : ℝ ↦ x ^ 2) by fun_prop) hX.integrable_sq]
    with ω hω
  exact (memLp_two_iff_integrable_sq (by fun_prop)).2 hω

/-- A measurable random center gives an almost surely short conditional support. -/
lemma realConditionalLaw_ae_abs_sub_le {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] (hm : m ≤ mΩ) {P : Measure[mΩ] Ω} [IsFiniteMeasure P]
    {X C : Ω → ℝ} (hX : Measurable X) (hC : Measurable[m] C) {R : ℝ}
    (hb : ∀ᵐ ω ∂P, |X ω - C ω| ≤ R) :
    ∀ᵐ ω ∂P.trim hm, ∀ᵐ x ∂realConditionalLaw m X P ω, |x - C ω| ≤ R := by
  apply realConditionalLaw_ae_support hm hX (s := {p | |p.2 - C p.1| ≤ R})
  · let : MeasurableSpace (Ω × ℝ) := m.prod inferInstance
    have hsnd : @Measurable (Ω × ℝ) ℝ (m.prod inferInstance) _ Prod.snd :=
      @measurable_snd Ω ℝ m inferInstance
    have hfst : @Measurable (Ω × ℝ) Ω (m.prod inferInstance) m Prod.fst :=
      @measurable_fst Ω ℝ m inferInstance
    have hf : Measurable[m.prod inferInstance] (fun p : Ω × ℝ ↦ p.2 - C p.1) :=
      hsnd.sub (hC.comp hfst)
    simpa only [Real.norm_eq_abs] using measurableSet_le hf.norm measurable_const
  · exact hb

end LpSelfSimilar
