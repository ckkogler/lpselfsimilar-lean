module

public import LpSelfSimilar.Fourier.QuinticSlopeBand
public import LpSelfSimilar.Fourier.SupportedIntervalTransform
public import LpSelfSimilar.Fourier.AngularTransformReflection
public import LpSelfSimilar.Fourier.AngularInverseRescaling
public import LpSelfSimilar.Analysis.RescaledKernelIntegrability
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

@[expose] public section

/-!
# Integrable inverse transforms of cutoff-slope products

Twice integrating by parts on one transition interval is legitimate because
the slope band and its derivative vanish at its endpoints. Reflection and
subtraction recover the full cutoff slope. Positive frequency scaling then
handles the normalized smoothing width, with the exact inverse Jacobian.
-/

open MeasureTheory Set
open LpSelfSimilar.Analysis

namespace LpSelfSimilar.Fourier

/-- One cutoff-slope band times a C2 amplitude and its actual inverse are integrable. -/
theorem quinticSlopeBand_mul_integrable_and_inverse {ε : ℝ} (hε : 0 < ε)
    {P : ℝ → ℂ} (hP : ContDiff ℝ 2 P) :
    Integrable (fun ξ => (quinticSlopeBand ε ξ : ℂ) * P ξ) ∧
      Integrable (angularInverseFourier (fun ξ => (quinticSlopeBand ε ξ : ℂ) * P ξ)) := by
  let B : ℝ → ℂ := fun ξ => (quinticSlopeBand ε ξ : ℂ)
  let D : ℝ → ℂ := fun ξ => (quinticSlopeBandDerivative ε ξ : ℂ)
  let T : ℝ → ℂ := fun ξ => (quinticSlopeBandSecond ε ξ : ℂ)
  have hB : ∀ ξ, HasDerivAt B (D ξ) ξ :=
    fun ξ => (hasDerivAt_quinticSlopeBand hε.ne' ξ).ofReal_comp
  have hD : ∀ ξ ∈ Ioo (1 - ε) (1 + ε), HasDerivAt D (T ξ) ξ :=
    fun ξ hξ => (hasDerivAt_quinticSlopeBandDerivative_of_mem hε hξ).ofReal_comp
  have hcB : Continuous B := continuous_iff_continuousAt.mpr (fun ξ => (hB ξ).continuousAt)
  have hcD : Continuous D := Complex.continuous_ofReal.comp (continuous_quinticSlopeBandDerivative ε)
  have hP' : ContDiff ℝ 1 (deriv P) := hP.deriv'
  have hdP : ∀ ξ, HasDerivAt P (deriv P ξ) ξ :=
    fun ξ => (hP.differentiable (by norm_num) ξ).hasDerivAt
  have hdP' : ∀ ξ, HasDerivAt (deriv P) (deriv (deriv P) ξ) ξ :=
    fun ξ => (hP'.differentiable (by norm_num) ξ).hasDerivAt
  let g : ℝ → ℂ := fun ξ => B ξ * P ξ
  let g' : ℝ → ℂ := fun ξ => D ξ * P ξ + B ξ * deriv P ξ
  let g'' : ℝ → ℂ := fun ξ => T ξ * P ξ + 2 * D ξ * deriv P ξ + B ξ * deriv (deriv P) ξ
  have hcg : Continuous g := hcB.mul hP.continuous
  have hcg' : Continuous g' := (hcD.mul hP.continuous).add (hcB.mul hP'.continuous)
  have hdg : ∀ ξ, HasDerivAt g (g' ξ) ξ := fun ξ => (hB ξ).mul (hdP ξ)
  have hdg' : ∀ ξ ∈ Ioo (1 - ε) (1 + ε), HasDerivAt g' (g'' ξ) ξ := by
    intro ξ hξ
    convert! ((hD ξ hξ).mul (hdP ξ)).add ((hB ξ).mul (hdP' ξ)) using 1 <;>
      simp only [g', g''] <;> ring
  have hig'' : IntervalIntegrable g'' volume (1 - ε) (1 + ε) := by
    have hT : IntervalIntegrable T volume (1 - ε) (1 + ε) :=
      (integrable_quinticSlopeBandSecond ε).ofReal.intervalIntegrable
    exact ((hT.mul_continuousOn hP.continuous.continuousOn).add
      (((hcD.const_mul 2).mul hP'.continuous).intervalIntegrable _ _)).add
        ((hcB.mul hP'.continuous_deriv_one).intervalIntegrable _ _)
  have hz (ξ : ℝ) (hξ : ξ ≤ 1 - ε ∨ 1 + ε ≤ ξ) :
      g ξ = 0 ∧ g' ξ = 0 ∧ g'' ξ = 0 := by
    have hzero := quinticSlopeBand_zero_off hε hξ
    simp only [g, g', g'', B, D, T, hzero.1, hzero.2,
      quinticSlopeBandSecond_zero_off hξ, Complex.ofReal_zero, zero_mul, mul_zero,
      zero_add, and_self]
  have hi : Integrable g := integrable_of_intervalIntegrable_zero_off_Ioo
    (hcg.intervalIntegrable _ _) (fun ξ hξ => (hz ξ hξ).1)
  have hinv := angularInverseFourier_interval_L1_bound (a := 1 - ε) (b := 1 + ε)
    (by linarith) hcg.continuousOn hcg'.continuousOn
    (fun ξ hξ => hdg ξ) hdg' hig'' (fun ξ hξ => (hz ξ hξ).1)
    (fun ξ hξ => (hz ξ hξ).2.2)
    (hz (1 - ε) (Or.inl le_rfl)).2.1 (hz (1 + ε) (Or.inr le_rfl)).2.1
  exact ⟨hi, hinv.1⟩

/-- The full cutoff slope times a C2 amplitude has an integrable inverse, including both bands. -/
theorem quinticCutoffSlope_mul_integrable_and_inverse {ε : ℝ} (hε : 0 < ε)
    {P : ℝ → ℂ} (hP : ContDiff ℝ 2 P) :
    Integrable (fun ξ => (quinticFourierCutoffSlope ε ξ : ℂ) * P ξ) ∧
      Integrable (angularInverseFourier (fun ξ => (quinticFourierCutoffSlope ε ξ : ℂ) * P ξ)) := by
  let p : ℝ → ℂ := fun ξ => (quinticSlopeBand ε ξ : ℂ) * P ξ
  let n : ℝ → ℂ := fun ξ => (quinticSlopeBand ε ξ : ℂ) * P (-ξ)
  have hp : Integrable p ∧ Integrable (angularInverseFourier p) :=
    quinticSlopeBand_mul_integrable_and_inverse hε hP
  have hn : Integrable n ∧ Integrable (angularInverseFourier n) :=
    quinticSlopeBand_mul_integrable_and_inverse hε (hP.comp (by fun_prop))
  have he : (fun ξ => (quinticFourierCutoffSlope ε ξ : ℂ) * P ξ) =
      (fun ξ => p ξ - n (-ξ)) := by
    funext ξ
    simp only [p, n, neg_neg, quinticFourierCutoffSlope_eq_slopeBands, Complex.ofReal_sub]
    ring
  rw [he]
  refine ⟨hp.1.sub hn.1.comp_neg, ?_⟩
  have hi : angularInverseFourier (fun ξ => p ξ - n (-ξ)) =
      (fun x => angularInverseFourier p x - angularInverseFourier n (-x)) := by
    funext x
    rw [angularInverseFourier_sub hp.1 hn.1.comp_neg, angularInverseFourier_reflect]
  rw [hi]
  exact hp.2.sub hn.2.comp_neg

/-- Scaling the cutoff slope preserves inverse integrability with every C2 amplitude. -/
theorem scaled_quinticCutoffSlope_mul_integrable_and_inverse {ε r : ℝ}
    (hε : 0 < ε) (hr : 0 < r) {P : ℝ → ℂ} (hP : ContDiff ℝ 2 P) :
    Integrable (fun ξ => (quinticFourierCutoffSlope ε (r * ξ) : ℂ) * P ξ) ∧
      Integrable (angularInverseFourier (fun ξ => (quinticFourierCutoffSlope ε (r * ξ) : ℂ) * P ξ)) := by
  let f : ℝ → ℂ := fun ξ => (quinticFourierCutoffSlope ε ξ : ℂ) * P (ξ / r)
  have hf : Integrable f ∧ Integrable (angularInverseFourier f) :=
    quinticCutoffSlope_mul_integrable_and_inverse hε (hP.comp (by fun_prop))
  have he : (fun ξ => (quinticFourierCutoffSlope ε (r * ξ) : ℂ) * P ξ) =
      (fun ξ => f (r * ξ)) := by
    funext ξ
    simp only [f, mul_div_cancel_left₀ _ hr.ne']
  rw [he]
  refine ⟨hf.1.comp_mul_left' hr.ne', ?_⟩
  have hi : angularInverseFourier (fun ξ => f (r * ξ)) = rescaledKernel r (angularInverseFourier f) :=
    funext (fun x => by simpa only [rescaledKernel] using! angularInverseFourier_comp_mul f hr x)
  rw [hi]
  exact integrable_rescaledKernel hf.2 hr.ne'

end LpSelfSimilar.Fourier
