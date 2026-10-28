module

public import LpSelfSimilar.Probability.FiniteMixture
public import LpSelfSimilar.Probability.FiniteConvolutionLaws

@[expose] public section

/-!
Exact distribution of a finite convolution over finite mixtures. The product of
conditional weights is proved by finite bilinearity and reindexing; this is the
joint reconstruction step behind finite conditioning of independent summands.
-/

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal

namespace LpSelfSimilar

lemma finsetSum_conv {I : Type*} (s : Finset I) (μ : I → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] (ν : Measure ℝ) [IsFiniteMeasure ν] :
    (∑ i ∈ s, μ i) ∗ ν = ∑ i ∈ s, μ i ∗ ν := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih => rw [Finset.sum_insert his, add_conv, ih, Finset.sum_insert his]

lemma conv_finsetSum {I : Type*} (s : Finset I) (μ : I → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] (ν : Measure ℝ) [IsFiniteMeasure ν] :
    ν ∗ (∑ i ∈ s, μ i) = ∑ i ∈ s, ν ∗ μ i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih => rw [Finset.sum_insert his, conv_add, ih, Finset.sum_insert his]

lemma finiteMixture_conv_finiteMixture {I J : Type*} [Fintype I] [Fintype J]
    (w : I → ℝ≥0) (v : J → ℝ≥0) (μ : I → Measure ℝ) (ν : J → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ j, IsFiniteMeasure (ν j)] :
    finiteMixture w μ ∗ finiteMixture v ν =
      finiteMixture (fun ij : I × J ↦ w ij.1 * v ij.2) (fun ij ↦ μ ij.1 ∗ ν ij.2) := by
  haveI (i : I) : IsFiniteMeasure ((w i : ℝ≥0∞) • μ i) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (by simp) (measure_lt_top _ _)⟩
  haveI (j : J) : IsFiniteMeasure ((v j : ℝ≥0∞) • ν j) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (by simp) (measure_lt_top _ _)⟩
  haveI : IsFiniteMeasure (∑ j, (v j : ℝ≥0∞) • ν j) := finiteMixture_finite v ν
  unfold finiteMixture
  rw [finsetSum_conv]
  simp_rw [conv_smul_left, conv_finsetSum, Finset.smul_sum, conv_smul_right, smul_smul]
  rw [Fintype.sum_prod_type]
  simp only [ENNReal.coe_mul]

/-- Independent mixture choices give the product of their weights, including
zero-weight states and the empty convolution. -/
theorem finiteConvolution_finiteMixture {n : ℕ} {Ω : Fin n → Type*}
    [∀ i, Fintype (Ω i)] (w : (i : Fin n) → Ω i → ℝ≥0)
    (μ : (i : Fin n) → Ω i → Measure ℝ) [∀ i ω, IsProbabilityMeasure (μ i ω)]
    (hw : ∀ i, ∑ ω, w i ω = 1) :
    finiteConvolution (fun i ↦ finiteMixture (w i) (μ i)) =
      finiteMixture (fun ω : (i : Fin n) → Ω i ↦ ∏ i, w i (ω i))
        (fun ω ↦ finiteConvolution (fun i ↦ μ i (ω i))) := by
  classical
  haveI (i : Fin n) : IsProbabilityMeasure (finiteMixture (w i) (μ i)) :=
    finiteMixture_isProbabilityMeasure (w i) (hw i) (μ i)
  induction n with
  | zero => simp [finiteConvolution, finiteMixture]
  | succ n ih =>
    rw [finiteConvolution, ih (fun i ↦ w i.succ) (fun i ↦ μ i.succ) (fun i ↦ hw i.succ) (fun i ↦ this i.succ)]
    rw [finiteMixture_conv_finiteMixture]
    unfold finiteMixture
    apply Fintype.sum_equiv (Fin.consEquiv Ω)
    intro ω
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
      finiteConvolution, ENNReal.coe_mul]

end LpSelfSimilar
