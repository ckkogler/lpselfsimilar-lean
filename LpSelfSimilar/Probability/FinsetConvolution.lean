module

public import LpSelfSimilar.Probability.FiniteConvolutionLaws
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

@[expose] public section

/-!
Order-independent convolution of a finite set of probability laws. A local
commutative monoid on bundled probability measures makes regrouping rigorous;
the exported operation is an ordinary measure and agrees with finiteConvolution.
-/

open MeasureTheory MeasureTheory.Measure

namespace LpSelfSimilar

/-- Convolution gives bundled probability laws a commutative monoid structure.
The instance is installed locally for the finite convolution construction. -/
@[instance_reducible] noncomputable def probabilityConvolutionMonoid : CommMonoid (ProbabilityMeasure ℝ) where
  mul μ ν := ⟨(μ : Measure ℝ) ∗ (ν : Measure ℝ), inferInstance⟩
  one := ⟨dirac 0, inferInstance⟩
  mul_assoc μ ν ρ := Subtype.ext (conv_assoc _ _ _)
  one_mul μ := Subtype.ext (dirac_zero_conv _)
  mul_one μ := Subtype.ext (conv_dirac_zero _)
  mul_comm μ ν := Subtype.ext (conv_comm _ _)

attribute [local instance] probabilityConvolutionMonoid

/-- Bundle a probability law for the finite convolution construction. -/
def asProbability (μ : Measure ℝ) [IsProbabilityMeasure μ] : ProbabilityMeasure ℝ :=
  ⟨μ, inferInstance⟩

noncomputable def finsetConvolution {I : Type*} (s : Finset I) (μ : I → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] : Measure ℝ :=
  ((∏ i ∈ s, asProbability (μ i)) : ProbabilityMeasure ℝ)

instance finsetConvolution_probability {I : Type*} (s : Finset I) (μ : I → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] : IsProbabilityMeasure (finsetConvolution s μ) :=
  by unfold finsetConvolution; infer_instance

@[simp] lemma finsetConvolution_empty {I : Type*} (μ : I → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] : finsetConvolution ∅ μ = dirac 0 := rfl

lemma finsetConvolution_insert {I : Type*} [DecidableEq I] (s : Finset I) (μ : I → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] {i : I} (hi : i ∉ s) :
    finsetConvolution (insert i s) μ = μ i ∗ finsetConvolution s μ := by
  unfold finsetConvolution
  rw [Finset.prod_insert hi]
  rfl

lemma finsetConvolution_split {I : Type*} [DecidableEq I] (s t : Finset I) (μ : I → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (ht : t ⊆ s) :
    finsetConvolution s μ = finsetConvolution t μ ∗ finsetConvolution (s \ t) μ := by
  unfold finsetConvolution
  have h := Finset.prod_sdiff ht (f := fun i ↦ asProbability (μ i))
  rw [← h, mul_comm]
  rfl

lemma finsetConvolution_univ_fin {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] : finsetConvolution Finset.univ μ = finiteConvolution μ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold finsetConvolution
    rw [Fin.prod_univ_succ]
    change μ 0 ∗ finsetConvolution Finset.univ (fun i : Fin n ↦ μ i.succ) = _
    rw [ih]
    rfl

lemma finsetConvolution_eq_finiteConvolution {I : Type*} (s : Finset I) (μ : I → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] :
    finsetConvolution s μ =
      finiteConvolution (fun j ↦ μ ((Fintype.equivFin s).symm j)) := by
  classical
  rw [← finsetConvolution_univ_fin]
  unfold finsetConvolution
  congr 1
  rw [← Finset.prod_attach]
  exact Fintype.prod_equiv (Fintype.equivFin s) _ _ (fun i ↦ by simp)

end LpSelfSimilar
