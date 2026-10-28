module

public import LpSelfSimilar.Probability.FiniteConvolutionLaws
public import Mathlib.Probability.Kernel.Composition.Lemmas

@[expose] public section

/-!
Convolution of probability kernels and independent mixing. Pointwise evaluation
agrees with the existing measure convolution. Mixing a parallel product over
independent base measures gives the product of the marginal mixtures, as follows
from the proved kernel composition identities.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory

namespace LpSelfSimilar

/-- Pointwise convolution of two kernels with the same conditioning space. -/
noncomputable def convolveKernel {Ω : Type*} [MeasurableSpace Ω]
    (κ η : Kernel Ω ℝ) : Kernel Ω ℝ :=
  (κ ×ₖ η).map (fun p : ℝ × ℝ ↦ p.1 + p.2)

instance {Ω : Type*} [MeasurableSpace Ω] (κ η : Kernel Ω ℝ)
    [IsMarkovKernel κ] [IsMarkovKernel η] : IsMarkovKernel (convolveKernel κ η) := by
  unfold convolveKernel
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

lemma convolveKernel_apply {Ω : Type*} [MeasurableSpace Ω]
    (κ η : Kernel Ω ℝ) [IsSFiniteKernel κ] [IsSFiniteKernel η] (ω : Ω) :
    convolveKernel κ η ω = κ ω ∗ η ω := by
  rw [convolveKernel, Kernel.map_apply _ (by fun_prop), Kernel.prod_apply]
  rfl

/-- Finite pointwise kernel convolution, including the empty sum law. -/
noncomputable def finiteConvolutionKernel {Ω : Type*} [MeasurableSpace Ω] :
    {n : ℕ} → (Fin n → Kernel Ω ℝ) → Kernel Ω ℝ
  | 0, _ => Kernel.const Ω (dirac 0)
  | n + 1, κ => convolveKernel (κ 0) (finiteConvolutionKernel (fun j : Fin n ↦ κ j.succ))

instance {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (κ : Fin n → Kernel Ω ℝ)
    [∀ i, IsMarkovKernel (κ i)] : IsMarkovKernel (finiteConvolutionKernel κ) := by
  induction n with
  | zero => simp only [finiteConvolutionKernel]; infer_instance
  | succ n ih =>
    haveI : IsMarkovKernel (finiteConvolutionKernel (fun j : Fin n ↦ κ j.succ)) := ih _
    unfold finiteConvolutionKernel
    infer_instance

lemma finiteConvolutionKernel_apply {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (κ : Fin n → Kernel Ω ℝ) [∀ i, IsMarkovKernel (κ i)] (ω : Ω) :
    finiteConvolutionKernel κ ω = finiteConvolution (fun i ↦ κ i ω) := by
  induction n with
  | zero => simp only [finiteConvolutionKernel, Kernel.const_apply, finiteConvolution]
  | succ n ih =>
    rw [finiteConvolutionKernel, convolveKernel_apply, ih, finiteConvolution]

/-- General independent-mixture reconstruction for a pair of kernels. -/
lemma parallelKernel_comp_prod {Ω Ξ A B : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure Ω) (Q : Measure Ξ) [SFinite P] [SFinite Q]
    (κ : Kernel Ω A) (η : Kernel Ξ B) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    (κ ∥ₖ η) ∘ₘ (P.prod Q) = (κ ∘ₘ P).prod (η ∘ₘ Q) := by
  rw [Measure.comp_eq_comp_const_apply, ← Kernel.prod_const,
    Kernel.parallelComp_comp_prod, Kernel.comp_const, Kernel.comp_const,
    Kernel.prod_const, Kernel.const_apply]

end LpSelfSimilar
