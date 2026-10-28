module

public import LpSelfSimilar.Fourier.IndependentProductDerivatives

@[expose] public section

/-!
# Derivative majorants from conditional support and mean attenuation

A common support radius bounds all positive-order derivatives. A marginal mean
bound at order zero pays for the undifferentiated factor. The cost inequality
`D <= C*v`, with `v <= 1`, pays for the first two derivative orders without
assuming a pointwise bound by `v`. The actual product label law then yields
exponential attenuation for the finite convolution.
-/

open MeasureTheory Set
open scoped BigOperators

namespace LpSelfSimilar.Fourier

/-- Support and zeroth-order mean attenuation imply the first two mean derivative majorants. -/
theorem integral_norm_iteratedDeriv_charFun_le_majorant
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Ω → Measure ℝ) [∀ a, IsProbabilityMeasure (μ a)]
    {D C v : ℝ} (hD : 0 ≤ D) (hC : 0 ≤ C) (hv : v ≤ 1) (hcost : D ≤ C * v)
    (hs : ∀ a, ∀ᵐ y ∂μ a, |y| ≤ D) (x : ℝ)
    (hb : (∫ a, ‖charFun (μ a) x‖ ∂P) ≤ v) (k : ℕ) (hk : k ≤ 2) :
    (∫ a, ‖iteratedDeriv k (charFun (μ a)) x‖ ∂P) ≤ C ^ k * v := by
  have hd (j : ℕ) : (∫ a, ‖iteratedDeriv j (charFun (μ a)) x‖ ∂P) ≤ D ^ j := by
    have h := integral_mono_of_nonneg (μ := P) (ae_of_all _ (fun a ↦ norm_nonneg _))
      (integrable_const (D ^ j)) (ae_of_all _ (fun a ↦
        norm_iteratedDeriv_charFun_le_of_ae_abs_le (μ a) (hs a) j x))
    simpa using h
  have hDC : D ≤ C := hcost.trans (mul_le_of_le_one_right hC hv)
  interval_cases k
  · simpa only [iteratedDeriv_zero, pow_zero, one_mul] using hb
  · exact (hd 1).trans (by simpa only [pow_one] using hcost)
  · apply (hd 2).trans
    have h1 := mul_le_mul_of_nonneg_right hDC hD
    have h2 := mul_le_mul_of_nonneg_left hcost hC
    nlinarith

/-- Actual independently conditioned convolutions retain attenuation through two derivatives. -/
theorem integral_norm_iteratedDeriv_charFun_product_le_exp
    {m : ℕ} {Ω : Fin m → Type*} [∀ i, Fintype (Ω i)]
    [∀ i, MeasurableSpace (Ω i)] [∀ i, MeasurableSingletonClass (Ω i)]
    (p : (i : Fin m) → PMF (Ω i)) (μ : (i : Fin m) → Ω i → Measure ℝ)
    [∀ i a, IsProbabilityMeasure (μ i a)] (b : Fin m → ℝ)
    {D C : ℝ} (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hb0 : ∀ i, 0 ≤ b i) (hb1 : ∀ i, b i < 1)
    (hcost : ∀ i, D ≤ C * (1 - b i))
    (hs : ∀ i a, ∀ᵐ y ∂μ i a, |y| ≤ D) (x : ℝ)
    (hb : ∀ i, (∫ a, ‖charFun (μ i a) x‖ ∂(p i).toMeasure) ≤ 1 - b i)
    (k : ℕ) (hk : k ≤ 2) :
    (∫ ω, ‖iteratedDeriv k (charFun (finiteConvolution (fun i ↦ μ i (ω i)))) x‖
      ∂(productPMF p).toMeasure) ≤ (C * m) ^ k * Real.exp (-∑ i, b i) := by
  have h := integral_norm_iteratedDeriv_charFun_independent_product_le p μ
    (fun i ↦ 1 - b i) (fun _ ↦ C) (fun i ↦ sub_nonneg.mpr (hb1 i).le)
    (fun _ ↦ hC) 2 x
    (fun i a ↦ (contDiff_charFun_of_ae_abs_le (μ i a) (hs i a) 2).contDiffAt)
    (fun i j hj ↦ integral_norm_iteratedDeriv_charFun_le_majorant (p i).toMeasure
      (μ i) hD hC (by linarith [hb0 i]) (hcost i) (hs i) x (hb i) j hj) k hk
  have hp : (∏ i, (1 - b i)) ≤ Real.exp (-∑ i, b i) := by
    calc
      _ ≤ ∏ i, Real.exp (-b i) := by
        apply Finset.prod_le_prod
        · intro i hi
          exact sub_nonneg.mpr (hb1 i).le
        · intro i hi
          linarith [Real.add_one_le_exp (-b i)]
      _ = _ := by rw [← Real.exp_sum]; simp only [Finset.sum_neg_distrib]
  have hsum : (∑ _ : Fin m, C) = C * m := by simp [mul_comm]
  rw [hsum] at h
  exact h.trans (mul_le_mul_of_nonneg_left hp (pow_nonneg (mul_nonneg hC (by positivity)) k))

end LpSelfSimilar.Fourier
