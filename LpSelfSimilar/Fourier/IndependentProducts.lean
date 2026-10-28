module

public import LpSelfSimilar.Probability.FiniteConvolutionLaws
public import LpSelfSimilar.Probability.ProductPMF
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-!
# Characteristic functions of independently conditioned finite products

Finite convolution gives the product of the actual characteristic functions.
Averaging its norm under the actual product PMF of labels factors the expectation.
Thus additive attenuation bounds give exponential decay without an assumed
independence identity. The empty convolution and zero-probability labels are included.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace LpSelfSimilar.Fourier

/-- The characteristic function of an actual finite convolution is the product of its factors. -/
theorem charFun_finiteConvolution {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (s : ℝ) :
    charFun (finiteConvolution μ) s = ∏ i, charFun (μ i) s := by
  induction n with
  | zero => simp [finiteConvolution, charFun_dirac]
  | succ n ih =>
    rw [finiteConvolution, charFun_conv, Fin.prod_univ_succ, ih]

/-- The norm of the characteristic function factors over the finite convolution. -/
theorem norm_charFun_finiteConvolution {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (s : ℝ) :
    ‖charFun (finiteConvolution μ) s‖ = ∏ i, ‖charFun (μ i) s‖ := by
  rw [charFun_finiteConvolution, norm_prod]

/-- Averaging over the actual product label law factors the expected characteristic-function norm. -/
theorem integral_norm_charFun_independent_product {n : ℕ} {Ω : Fin n → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, MeasurableSpace (Ω i)] [∀ i, MeasurableSingletonClass (Ω i)]
    (p : (i : Fin n) → PMF (Ω i)) (μ : (i : Fin n) → Ω i → Measure ℝ)
    [∀ i ω, IsProbabilityMeasure (μ i ω)] (s : ℝ) :
    (∫ ω, ‖charFun (finiteConvolution (fun i ↦ μ i (ω i))) s‖ ∂(productPMF p).toMeasure) =
      ∏ i, ∫ ω, ‖charFun (μ i ω) s‖ ∂(p i).toMeasure := by
  rw [PMF.integral_eq_sum]
  simp_rw [PMF.integral_eq_sum, norm_charFun_finiteConvolution, productPMF_apply,
    ENNReal.toReal_prod, smul_eq_mul, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (i : Fin n) (ω : Ω i) ↦
    (p i ω).toReal * ‖charFun (μ i ω) s‖)).symm

/-- One-minus-attenuation bounds give exponential decay for the actual independently conditioned law. -/
theorem integral_norm_charFun_independent_product_le_exp {n : ℕ} {Ω : Fin n → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, MeasurableSpace (Ω i)] [∀ i, MeasurableSingletonClass (Ω i)]
    (p : (i : Fin n) → PMF (Ω i)) (μ : (i : Fin n) → Ω i → Measure ℝ)
    [∀ i ω, IsProbabilityMeasure (μ i ω)] (b : Fin n → ℝ) (s : ℝ)
    (hb : ∀ i, (∫ ω, ‖charFun (μ i ω) s‖ ∂(p i).toMeasure) ≤ 1 - b i) :
    (∫ ω, ‖charFun (finiteConvolution (fun i ↦ μ i (ω i))) s‖ ∂(productPMF p).toMeasure) ≤
      Real.exp (-∑ i, b i) := by
  rw [integral_norm_charFun_independent_product]
  calc
    _ ≤ ∏ i, Real.exp (-b i) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact integral_nonneg (fun ω ↦ norm_nonneg _)
      · intro i hi
        exact (hb i).trans (by linarith [Real.add_one_le_exp (-b i)])
    _ = _ := by rw [← Real.exp_sum]; simp only [Finset.sum_neg_distrib]

end LpSelfSimilar.Fourier
