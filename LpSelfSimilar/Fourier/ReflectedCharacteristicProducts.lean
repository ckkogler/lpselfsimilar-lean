module

public import LpSelfSimilar.Fourier.IndependentProductDerivatives
public import LpSelfSimilar.Fourier.QuinticMeanInversion

@[expose] public section

/-!
# Smooth characteristic products and reflected derivative means

Bounded probability factors give globally smooth finite convolution
characteristic functions. Reflection multiplies the j-th derivative by
`(-1)^j`, preserving its norm and the symmetric frequency band.
-/

open MeasureTheory
open scoped BigOperators

namespace LpSelfSimilar.Fourier

/-- Bounded actual probability factors have a globally smooth convolution characteristic function. -/
theorem contDiff_charFun_finiteConvolution_of_ae_abs_le {m : ℕ}
    (μ : Fin m → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (D : Fin m → ℝ)
    (hb : ∀ i, ∀ᵐ y ∂μ i, |y| ≤ D i) (n : ℕ) :
    ContDiff ℝ n (charFun (finiteConvolution μ)) := by
  have he : charFun (finiteConvolution μ) = fun ξ ↦ ∏ i, charFun (μ i) ξ :=
    funext (charFun_finiteConvolution μ)
  rw [he]
  exact contDiff_prod (fun i hi ↦ contDiff_charFun_of_ae_abs_le (μ i) (hb i) n)

/-- Reflection preserves each actual iterated derivative norm. -/
theorem norm_iteratedDeriv_comp_neg (n : ℕ) (f : ℝ → ℂ) (ξ : ℝ) :
    ‖iteratedDeriv n (fun x ↦ f (-x)) ξ‖ = ‖iteratedDeriv n f (-ξ)‖ := by
  rw [iteratedDeriv_comp_neg, norm_smul, norm_pow]
  simp

/-- The original finite label mean derivative bounds hold on the reflected symmetric band. -/
theorem integral_norm_iteratedDeriv_reflect_band_le
    {Ω : Type*} [MeasurableSpace Ω] (p : Measure Ω) (P : Ω → ℝ → ℂ)
    {ε D B : ℝ} (n : ℕ)
    (hb : ∀ ξ, |(|ξ| - 1)| ≤ ε → ∀ j ≤ n,
      (∫ a, ‖iteratedDeriv j (P a) ξ‖ ∂p) ≤ D ^ j * B)
    (ξ : ℝ) (hξ : |(|ξ| - 1)| ≤ ε) (j : ℕ) (hj : j ≤ n) :
    (∫ a, ‖iteratedDeriv j (fun x ↦ P a (-x)) ξ‖ ∂p) ≤ D ^ j * B := by
  simp_rw [norm_iteratedDeriv_comp_neg]
  exact hb (-ξ) (by simpa only [abs_neg] using hξ) j hj

end LpSelfSimilar.Fourier
