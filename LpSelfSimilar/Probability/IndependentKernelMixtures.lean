module

public import LpSelfSimilar.Probability.KernelConvolution
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section

/-!
Independent products of arbitrary conditioning spaces. Mixing coordinate kernels
against the product of their base laws reconstructs the finite convolution of
marginal mixtures. This is a measure identity, with no finite-support hypothesis.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory

namespace LpSelfSimilar

lemma comapKernel_comp {Ω Ξ A : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    [MeasurableSpace A] (κ : Kernel Ω A) (P : Measure Ξ)
    {f : Ξ → Ω} (hf : Measurable f) :
    κ.comap f hf ∘ₘ P = κ ∘ₘ P.map f := by
  rw [← Kernel.comp_deterministic_eq_comap, ← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map]

lemma convolveKernel_coordinates_comp_prod {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] (P : Measure Ω) (Q : Measure Ξ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (κ : Kernel Ω ℝ) (η : Kernel Ξ ℝ) [IsMarkovKernel κ] [IsMarkovKernel η] :
    convolveKernel (κ.comap Prod.fst measurable_fst) (η.comap Prod.snd measurable_snd) ∘ₘ
      P.prod Q = (κ ∘ₘ P) ∗ (η ∘ₘ Q) := by
  have he : (κ.comap Prod.fst measurable_fst) ×ₖ (η.comap Prod.snd measurable_snd) =
      κ ∥ₖ η := by
    ext ω : 1
    simp only [Kernel.prod_apply, Kernel.comap_apply, Kernel.parallelComp_apply]
  rw [convolveKernel, he, ← Measure.map_comp _ _ (by fun_prop), parallelKernel_comp_prod]
  rfl

/-- A conditional convolution whose i-th law depends only on coordinate i. -/
noncomputable def independentConvolutionKernel {n : ℕ} {Ω : Fin n → Type*}
    [∀ i, MeasurableSpace (Ω i)] (κ : (i : Fin n) → Kernel (Ω i) ℝ) :
    Kernel ((i : Fin n) → Ω i) ℝ :=
  finiteConvolutionKernel (fun i ↦ (κ i).comap (Function.eval i) (measurable_pi_apply i))

instance {n : ℕ} {Ω : Fin n → Type*} [∀ i, MeasurableSpace (Ω i)]
    (κ : (i : Fin n) → Kernel (Ω i) ℝ) [∀ i, IsMarkovKernel (κ i)] :
    IsMarkovKernel (independentConvolutionKernel κ) := by
  unfold independentConvolutionKernel
  infer_instance

lemma independentConvolutionKernel_apply {n : ℕ} {Ω : Fin n → Type*}
    [∀ i, MeasurableSpace (Ω i)] (κ : (i : Fin n) → Kernel (Ω i) ℝ)
    [∀ i, IsMarkovKernel (κ i)] (ω : (i : Fin n) → Ω i) :
    independentConvolutionKernel κ ω = finiteConvolution (fun i ↦ κ i (ω i)) := by
  simp only [independentConvolutionKernel, finiteConvolutionKernel_apply, Kernel.comap_apply]

/-- Product mixing reconstructs the convolution of the marginal mixtures. -/
theorem independentConvolutionKernel_comp_pi {n : ℕ} {Ω : Fin n → Type*}
    [∀ i, MeasurableSpace (Ω i)] (P : (i : Fin n) → Measure (Ω i))
    [∀ i, IsProbabilityMeasure (P i)] (κ : (i : Fin n) → Kernel (Ω i) ℝ)
    [∀ i, IsMarkovKernel (κ i)] :
    independentConvolutionKernel κ ∘ₘ Measure.pi P =
      finiteConvolution (fun i ↦ κ i ∘ₘ P i) := by
  induction n with
  | zero =>
    simp only [independentConvolutionKernel, finiteConvolutionKernel, finiteConvolution,
      Measure.const_comp, measure_univ, one_smul]
  | succ n ih =>
    let η := independentConvolutionKernel (fun j : Fin n ↦ κ j.succ)
    let split (ω : (i : Fin (n + 1)) → Ω i) := (ω 0, fun j : Fin n ↦ ω j.succ)
    have hsplit : Measurable split := by fun_prop
    have hmap : (Measure.pi P).map split = (P 0).prod (Measure.pi (fun j : Fin n ↦ P j.succ)) := by
      have hfun : ⇑(MeasurableEquiv.piFinSuccAbove Ω (0 : Fin (n + 1))) = split := by
        funext ω
        rfl
      rw [← hfun]
      exact (measurePreserving_piFinSuccAbove P (0 : Fin (n + 1))).map_eq
    let K := convolveKernel ((κ 0).comap Prod.fst measurable_fst)
      (η.comap Prod.snd measurable_snd)
    have he : independentConvolutionKernel κ = K.comap split hsplit := by
      ext ω : 1
      rw [independentConvolutionKernel_apply, Kernel.comap_apply, convolveKernel_apply,
        Kernel.comap_apply, Kernel.comap_apply, independentConvolutionKernel_apply,
        finiteConvolution]
    rw [he, comapKernel_comp, hmap]
    rw [convolveKernel_coordinates_comp_prod]
    rw [ih (fun j : Fin n ↦ P j.succ) (fun j : Fin n ↦ κ j.succ)]
    rfl

end LpSelfSimilar
