module

public import LpSelfSimilar.Fourier.AngularInverseTransform
public import LpSelfSimilar.Analysis.VectorMeasureConvolution
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

@[expose] public section

/-!
# Angular inverse integrals and actual measure convolution

The inverse phase is positive. Therefore convolution by a measure multiplies
the amplitude by its characteristic function at the negative frequency.
The equality is proved by Fubini for the actual integral, with joint
integrability derived from the L1 amplitude and finite total measure.
-/

open MeasureTheory MeasureTheory.Measure

namespace LpSelfSimilar.Fourier

/-- Translating the spatial argument gives the negative spatial phase factor. -/
theorem angularFourierPhase_sub (x y ξ : ℝ) :
    angularFourierPhase (x - y) ξ = angularFourierPhase x ξ * angularFourierPhase (-y) ξ := by
  unfold angularFourierPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Mathlib's positive characteristic convention requires negative frequency here. -/
theorem charFun_neg_eq_integral_angularFourierPhase (μ : Measure ℝ) (ξ : ℝ) :
    charFun μ (-ξ) = ∫ y, angularFourierPhase (-y) ξ ∂μ := by
  rw [charFun_apply_real]
  congr 1
  ext y
  unfold angularFourierPhase
  congr 1
  push_cast
  ring

/-- Joint integrability needed to interchange frequency integration and measure averaging. -/
theorem integrable_angularFourierPhase_translation_product
    (μ : Measure ℝ) [IsFiniteMeasure μ] {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    Integrable (fun p : ℝ × ℝ ↦ angularFourierPhase (x - p.1) p.2 * f p.2) (μ.prod volume) := by
  have hc : Continuous (fun p : ℝ × ℝ ↦ angularFourierPhase (x - p.1) p.2) :=
    continuous_angularFourierPhase.comp ((continuous_const.sub continuous_fst).prodMk continuous_snd)
  apply ((integrable_const (1 : ℝ) (μ := μ)).mul_prod hf.norm).mono'
    (hc.aestronglyMeasurable.mul hf.aestronglyMeasurable.comp_snd)
  exact ae_of_all _ (fun p ↦ by
    simp only [Pi.mul_apply, norm_angularFourierPhase_mul, one_mul, le_refl])

/-- Actual measure convolution equals the inverse of the multiplier with negative charFun phase. -/
theorem measureFunctionConvolution_angularInverseFourier
    (μ : Measure ℝ) [IsFiniteMeasure μ] {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    Analysis.measureFunctionConvolution μ (angularInverseFourier f) x =
      angularInverseFourier (fun ξ ↦ f ξ * charFun μ (-ξ)) x := by
  have hi := integrable_angularFourierPhase_translation_product μ hf x
  unfold Analysis.measureFunctionConvolution angularInverseFourier
  rw [integral_smul, integral_integral_swap hi]
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro ξ
  simp_rw [angularFourierPhase_sub]
  rw [integral_mul_const, integral_const_mul, ← charFun_neg_eq_integral_angularFourierPhase]
  ring

/-- Multiplication by the characteristic factor contracts the actual inverse L1 norm. -/
theorem angularInverseFourier_mul_charFun_neg_L1
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {f : ℝ → ℂ}
    (hf : Integrable f) (hk : Integrable (angularInverseFourier f)) :
    Integrable (angularInverseFourier (fun ξ ↦ f ξ * charFun μ (-ξ))) ∧
      (∫ x, ‖angularInverseFourier (fun ξ ↦ f ξ * charFun μ (-ξ)) x‖) ≤
        ∫ x, ‖angularInverseFourier f x‖ := by
  have he : angularInverseFourier (fun ξ ↦ f ξ * charFun μ (-ξ)) =
      Analysis.measureFunctionConvolution μ (angularInverseFourier f) :=
    funext (fun x ↦ (measureFunctionConvolution_angularInverseFourier μ hf x).symm)
  rw [he]
  have hc := continuous_angularInverseFourier hf
  exact ⟨Analysis.integrable_measureFunctionConvolution μ hc hk,
    Analysis.integral_norm_measureFunctionConvolution_probability_le μ hc hk⟩

end LpSelfSimilar.Fourier
