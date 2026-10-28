module

public import LpSelfSimilar.Fourier.QuinticBandInversion
public import LpSelfSimilar.Fourier.QuinticDetailCurvatureIntegrals
public import LpSelfSimilar.Fourier.AngularTransformReflection

@[expose] public section

/-!
# The actual full detail multiplier times a smooth amplitude

The positive and negative bands keep their original amplitude values. Reflection
changes the sign of the first amplitude derivative and preserves its second.
The curvature formula is proved equal to the actual second derivative almost
everywhere, so later inverse estimates concern the real product function.
-/

open MeasureTheory

namespace LpSelfSimilar.Fourier

/-- The actual full detail multiplier times a complex amplitude. -/
noncomputable def quinticDetailProduct (ε : ℝ) (P : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  (quinticFourierDetail ε ξ : ℂ) * P ξ

/-- The first derivative formula for the full detail product. -/
noncomputable def quinticDetailProductSlope (ε : ℝ) (P P₁ : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  (quinticFourierDetailSlope ε ξ : ℂ) * P ξ + (quinticFourierDetail ε ξ : ℂ) * P₁ ξ

/-- The almost-everywhere second derivative formula for the full detail product. -/
noncomputable def quinticDetailProductCurvature (ε : ℝ) (P P₁ P₂ : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  (quinticFourierDetailCurvature ε ξ : ℂ) * P ξ +
    2 * (quinticFourierDetailSlope ε ξ : ℂ) * P₁ ξ + (quinticFourierDetail ε ξ : ℂ) * P₂ ξ

/-- Decomposition into positive and reflected bands with the correct amplitude. -/
theorem quinticDetailProduct_eq_bands (ε : ℝ) (P : ℝ → ℂ) (ξ : ℝ) :
    quinticDetailProduct ε P ξ = quinticBandProduct ε P ξ +
      quinticBandProduct ε (fun t ↦ P (-t)) (-ξ) := by
  unfold quinticDetailProduct quinticBandProduct
  rw [quinticFourierDetail_eq_bands]
  push_cast
  ring

/-- Curvature decomposition includes the sign change of the reflected amplitude slope. -/
theorem quinticDetailProductCurvature_eq_bands (ε : ℝ) (P P₁ P₂ : ℝ → ℂ) (ξ : ℝ) :
    quinticDetailProductCurvature ε P P₁ P₂ ξ = quinticBandProductCurvature ε P P₁ P₂ ξ +
      quinticBandProductCurvature ε (fun t ↦ P (-t)) (fun t ↦ -P₁ (-t)) (fun t ↦ P₂ (-t)) (-ξ) := by
  unfold quinticDetailProductCurvature quinticBandProductCurvature
  rw [quinticFourierDetailSlope_eq_bands, quinticFourierDetail_eq_bands]
  unfold quinticFourierDetailCurvature
  push_cast
  ring

/-- The displayed first derivative is the actual derivative of the full product everywhere. -/
theorem hasDerivAt_quinticDetailProduct {ε ξ : ℝ} (hε : 0 < ε) {P P₁ : ℝ → ℂ}
    (hP : HasDerivAt P (P₁ ξ) ξ) :
    HasDerivAt (quinticDetailProduct ε P) (quinticDetailProductSlope ε P P₁ ξ) ξ := by
  convert! (hasDerivAt_quinticFourierDetail (ne_of_gt hε) ξ).ofReal_comp.mul hP using 1 <;>
    simp only [quinticDetailProduct, quinticDetailProductSlope] <;> ring

/-- The product curvature equals the actual second derivative almost everywhere. -/
theorem ae_deriv_deriv_quinticDetailProduct {ε : ℝ} (hε : 0 < ε)
    {P P₁ P₂ : ℝ → ℂ} (hP : ∀ ξ, HasDerivAt P (P₁ ξ) ξ)
    (hP₁ : ∀ ξ, HasDerivAt P₁ (P₂ ξ) ξ) :
    deriv (deriv (quinticDetailProduct ε P)) =ᵐ[volume] quinticDetailProductCurvature ε P P₁ P₂ := by
  have he : deriv (quinticDetailProduct ε P) = quinticDetailProductSlope ε P P₁ :=
    funext (fun ξ ↦ (hasDerivAt_quinticDetailProduct hε (hP ξ)).deriv)
  have hψ : deriv (quinticFourierDetail ε) = quinticFourierDetailSlope ε :=
    funext (fun ξ ↦ (hasDerivAt_quinticFourierDetail (ne_of_gt hε) ξ).deriv)
  rw [he]
  have hd := ae_hasDerivAt_deriv_quinticFourierDetail hε
  rw [hψ] at hd
  filter_upwards [hd] with ξ hξ
  have hprod : HasDerivAt (quinticDetailProductSlope ε P P₁)
      (quinticDetailProductCurvature ε P P₁ P₂ ξ) ξ := by
    convert! (hξ.ofReal_comp.mul (hP ξ)).add
      ((hasDerivAt_quinticFourierDetail (ne_of_gt hε) ξ).ofReal_comp.mul (hP₁ ξ)) using 1 <;>
      simp only [quinticDetailProductSlope, quinticDetailProductCurvature] <;> ring
  exact hprod.deriv

/-- The actual full product is integrable for every continuous amplitude. -/
theorem integrable_quinticDetailProduct {ε : ℝ} (hε : 0 < ε) {P : ℝ → ℂ} (hP : Continuous P) :
    Integrable (quinticDetailProduct ε P) := by
  have he : quinticDetailProduct ε P = fun ξ ↦ quinticBandProduct ε P ξ +
      quinticBandProduct ε (fun t ↦ P (-t)) (-ξ) := funext (quinticDetailProduct_eq_bands ε P)
  rw [he]
  exact (integrable_quinticBandProduct hε hP).add
    (integrable_quinticBandProduct hε (hP.comp continuous_neg)).comp_neg

/-- The full curvature formula is integrable for continuous amplitude derivative data. -/
theorem integrable_quinticDetailProductCurvature {ε : ℝ} (hε : 0 < ε)
    {P P₁ P₂ : ℝ → ℂ} (hP : Continuous P) (hP₁ : Continuous P₁) (hP₂ : Continuous P₂) :
    Integrable (quinticDetailProductCurvature ε P P₁ P₂) := by
  have he : quinticDetailProductCurvature ε P P₁ P₂ = fun ξ ↦
      quinticBandProductCurvature ε P P₁ P₂ ξ +
      quinticBandProductCurvature ε (fun t ↦ P (-t)) (fun t ↦ -P₁ (-t)) (fun t ↦ P₂ (-t)) (-ξ) :=
    funext (quinticDetailProductCurvature_eq_bands ε P P₁ P₂)
  rw [he]
  exact (integrable_quinticBandProductCurvature hε hP hP₁ hP₂).add
    (integrable_quinticBandProductCurvature hε (hP.comp continuous_neg)
      (hP₁.comp continuous_neg).neg (hP₂.comp continuous_neg)).comp_neg

end LpSelfSimilar.Fourier
