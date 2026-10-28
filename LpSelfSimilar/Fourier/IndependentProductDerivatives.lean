module

public import LpSelfSimilar.Analysis.IndependentProductDerivatives
public import LpSelfSimilar.Fourier.IndependentProducts
public import LpSelfSimilar.Fourier.BoundedCharacteristicDerivatives

@[expose] public section

/-!
# Characteristic derivatives averaged over actual independent labels

The finite weighted Leibniz estimate is applied to the proved product PMF.
Consequently the hypotheses concern the marginal mean derivative norms, with
no pointwise attenuation assumption. The finite convolution is identified with
the product of its actual characteristic functions before differentiation.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace LpSelfSimilar.Fourier

/-- Marginal mean derivative bounds combine under the actual product label PMF. -/
theorem integral_norm_iteratedDeriv_independent_product_le
    {m : ℕ} {Ω : Fin m → Type*} [∀ i, Fintype (Ω i)]
    [∀ i, MeasurableSpace (Ω i)] [∀ i, MeasurableSingletonClass (Ω i)]
    (p : (i : Fin m) → PMF (Ω i)) (f : (i : Fin m) → Ω i → ℝ → ℂ)
    (v w : Fin m → ℝ) (hv : ∀ i, 0 ≤ v i) (hw : ∀ i, 0 ≤ w i)
    (n : ℕ) (x : ℝ) (hf : ∀ i a, ContDiffAt ℝ n (f i a) x)
    (hb : ∀ i, ∀ k ≤ n,
      (∫ a, ‖iteratedDeriv k (f i a) x‖ ∂(p i).toMeasure) ≤ w i ^ k * v i)
    (k : ℕ) (hk : k ≤ n) :
    (∫ ω, ‖iteratedDeriv k (fun y ↦ ∏ i, f i (ω i) y) x‖
      ∂(productPMF p).toMeasure) ≤ (∑ i, w i) ^ k * ∏ i, v i := by
  simp_rw [PMF.integral_eq_sum, smul_eq_mul] at hb ⊢
  simp only [productPMF_apply, ENNReal.toReal_prod]
  exact Analysis.sum_norm_iteratedDeriv_independent_prod_le m n x
    (fun i a ↦ (p i a).toReal) f v w (fun i a ↦ ENNReal.toReal_nonneg) hv hw hf hb k hk

/-- The same mean derivative bound holds for the actual finite convolution of conditional laws. -/
theorem integral_norm_iteratedDeriv_charFun_independent_product_le
    {m : ℕ} {Ω : Fin m → Type*} [∀ i, Fintype (Ω i)]
    [∀ i, MeasurableSpace (Ω i)] [∀ i, MeasurableSingletonClass (Ω i)]
    (p : (i : Fin m) → PMF (Ω i)) (μ : (i : Fin m) → Ω i → Measure ℝ)
    [∀ i a, IsProbabilityMeasure (μ i a)] (v w : Fin m → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hw : ∀ i, 0 ≤ w i) (n : ℕ) (x : ℝ)
    (hf : ∀ i a, ContDiffAt ℝ n (charFun (μ i a)) x)
    (hb : ∀ i, ∀ k ≤ n,
      (∫ a, ‖iteratedDeriv k (charFun (μ i a)) x‖ ∂(p i).toMeasure) ≤ w i ^ k * v i)
    (k : ℕ) (hk : k ≤ n) :
    (∫ ω, ‖iteratedDeriv k (charFun (finiteConvolution (fun i ↦ μ i (ω i)))) x‖
      ∂(productPMF p).toMeasure) ≤ (∑ i, w i) ^ k * ∏ i, v i := by
  have he (ω : (i : Fin m) → Ω i) :
      charFun (finiteConvolution (fun i ↦ μ i (ω i))) = fun y ↦ ∏ i, charFun (μ i (ω i)) y := by
    funext y
    exact charFun_finiteConvolution _ y
  simp_rw [he]
  exact integral_norm_iteratedDeriv_independent_product_le p (fun i a ↦ charFun (μ i a))
    v w hv hw n x hf hb k hk

end LpSelfSimilar.Fourier
