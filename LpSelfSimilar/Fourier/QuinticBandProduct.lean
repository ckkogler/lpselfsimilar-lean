module

public import LpSelfSimilar.Fourier.QuinticDetailBandCurvature
public import LpSelfSimilar.Fourier.SupportedIntervalTransform
public import Mathlib.Analysis.Complex.RealDeriv

@[expose] public section

/-!
# Multiplying one quintic detail band by a smooth amplitude

The first derivative is valid at every point. The second derivative is proved
inside the active band and recorded by an integrable zero extension. Endpoint
vanishing follows from the cutoff itself; no decay of the amplitude is needed.
-/

open Set MeasureTheory Filter
open scoped Topology

namespace LpSelfSimilar.Fourier

/-- One detail band multiplied by a complex amplitude. -/
noncomputable def quinticBandProduct (ε : ℝ) (P : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  (quinticDetailBand ε ξ : ℂ) * P ξ

/-- Explicit first derivative with a specified amplitude derivative. -/
noncomputable def quinticBandProductSlope (ε : ℝ) (P P₁ : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  (quinticDetailBandSlope ε ξ : ℂ) * P ξ + (quinticDetailBand ε ξ : ℂ) * P₁ ξ

/-- Explicit second derivative away from the band endpoints. -/
noncomputable def quinticBandProductCurvature (ε : ℝ) (P P₁ P₂ : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  (quinticDetailBandCurvature ε ξ : ℂ) * P ξ +
    2 * (quinticDetailBandSlope ε ξ : ℂ) * P₁ ξ + (quinticDetailBand ε ξ : ℂ) * P₂ ξ

/-- The band slope has the specified curvature at every interior point. -/
theorem hasDerivAt_quinticDetailBandSlope_of_mem {ε ξ : ℝ} (hε : 0 < ε)
    (hξ : ξ ∈ Ioo (1 - ε) (1 + ε)) :
    HasDerivAt (quinticDetailBandSlope ε) (quinticDetailBandCurvature ε ξ) ξ := by
  rw [quinticDetailBandCurvature_eq_profile hξ]
  apply (hasDerivAt_quinticDetailBandSlopeProfile (ne_of_gt hε) ξ).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hξ] with y hy
  exact quinticDetailBandSlope_eq_profile hε ⟨hy.1.le, hy.2.le⟩

/-- The band product's actual first derivative, including the joins. -/
theorem hasDerivAt_quinticBandProduct {ε ξ : ℝ} (hε : 0 < ε) {P P₁ : ℝ → ℂ}
    (hP : HasDerivAt P (P₁ ξ) ξ) :
    HasDerivAt (quinticBandProduct ε P) (quinticBandProductSlope ε P P₁ ξ) ξ := by
  convert! (hasDerivAt_quinticDetailBand (ne_of_gt hε) ξ).ofReal_comp.mul hP using 1 <;>
    simp only [quinticBandProduct, quinticBandProductSlope] <;> ring

/-- The band product slope's actual derivative throughout the open band. -/
theorem hasDerivAt_quinticBandProductSlope_of_mem {ε ξ : ℝ} (hε : 0 < ε)
    (hξ : ξ ∈ Ioo (1 - ε) (1 + ε)) {P P₁ P₂ : ℝ → ℂ}
    (hP : HasDerivAt P (P₁ ξ) ξ) (hP₁ : HasDerivAt P₁ (P₂ ξ) ξ) :
    HasDerivAt (quinticBandProductSlope ε P P₁)
      (quinticBandProductCurvature ε P P₁ P₂ ξ) ξ := by
  have hq := (hasDerivAt_quinticDetailBand (ne_of_gt hε) ξ).ofReal_comp
  have hq₁ := (hasDerivAt_quinticDetailBandSlope_of_mem hε hξ).ofReal_comp
  convert! (hq₁.mul hP).add (hq.mul hP₁) using 1 <;>
    simp only [quinticBandProductSlope, quinticBandProductCurvature] <;> ring

/-- All three product formulas vanish at and beyond the band endpoints. -/
theorem quinticBandProduct_zero_off {ε ξ : ℝ} (hε : 0 < ε)
    (hξ : ξ ≤ 1 - ε ∨ 1 + ε ≤ ξ) (P P₁ P₂ : ℝ → ℂ) :
    quinticBandProduct ε P ξ = 0 ∧ quinticBandProductSlope ε P P₁ ξ = 0 ∧
      quinticBandProductCurvature ε P P₁ P₂ ξ = 0 := by
  have hq := quinticDetailBand_eq_zero hε hξ
  simp [quinticBandProduct, quinticBandProductSlope, quinticBandProductCurvature,
    hq.1, hq.2, quinticDetailBandCurvature_eq_zero hξ]

/-- Continuity of a band product with continuous amplitude. -/
theorem continuous_quinticBandProduct {ε : ℝ} (hε : 0 < ε) {P : ℝ → ℂ} (hP : Continuous P) :
    Continuous (quinticBandProduct ε P) := by
  have hq : Continuous (quinticDetailBand ε) := continuous_iff_continuousAt.mpr
    (fun ξ ↦ (hasDerivAt_quinticDetailBand (ne_of_gt hε) ξ).continuousAt)
  exact (Complex.continuous_ofReal.comp hq).mul hP

/-- Continuity of the product slope when the amplitude and its slope are continuous. -/
theorem continuous_quinticBandProductSlope {ε : ℝ} (hε : 0 < ε) {P P₁ : ℝ → ℂ}
    (hP : Continuous P) (hP₁ : Continuous P₁) : Continuous (quinticBandProductSlope ε P P₁) := by
  have hq : Continuous (quinticDetailBand ε) := continuous_iff_continuousAt.mpr
    (fun ξ ↦ (hasDerivAt_quinticDetailBand (ne_of_gt hε) ξ).continuousAt)
  exact ((Complex.continuous_ofReal.comp (continuous_quinticDetailBandSlope ε)).mul hP).add ((Complex.continuous_ofReal.comp hq).mul hP₁)

/-- The curvature formula is integrable on the band even though it may jump at the endpoints. -/
theorem intervalIntegrable_quinticBandProductCurvature {ε : ℝ} (hε : 0 < ε)
    {P P₁ P₂ : ℝ → ℂ} (hP : Continuous P) (hP₁ : Continuous P₁) (hP₂ : Continuous P₂) :
    IntervalIntegrable (quinticBandProductCurvature ε P P₁ P₂) volume (1 - ε) (1 + ε) := by
  have hq : IntervalIntegrable (fun ξ ↦ (quinticDetailBand ε ξ : ℂ)) volume (1 - ε) (1 + ε) :=
    (integrable_quinticDetailBand hε).ofReal.intervalIntegrable
  have hq₁ : IntervalIntegrable (fun ξ ↦ (quinticDetailBandSlope ε ξ : ℂ)) volume (1 - ε) (1 + ε) :=
    (integrable_quinticDetailBandSlope hε).ofReal.intervalIntegrable
  have hq₂ : IntervalIntegrable (fun ξ ↦ (quinticDetailBandCurvature ε ξ : ℂ)) volume (1 - ε) (1 + ε) :=
    (integrable_quinticDetailBandCurvature ε).ofReal.intervalIntegrable
  exact ((hq₂.mul_continuousOn hP.continuousOn).add
    ((hq₁.const_mul 2).mul_continuousOn hP₁.continuousOn)).add
      (hq.mul_continuousOn hP₂.continuousOn)

end LpSelfSimilar.Fourier
