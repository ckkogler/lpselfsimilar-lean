module

public import LpSelfSimilar.Fourier.QuinticSmoothingProduct
public import LpSelfSimilar.Fourier.QuinticSlopeInversion

@[expose] public section

/-!
# The inverse of the actual derivative of a smoothed amplitude

The product derivative splits into the cutoff slope times the amplitude and
the cutoff times the amplitude derivative. The first term uses the proved
piecewise-band estimate; the second uses compact C2 inversion. Consequently a
C3 amplitude supplies inverse-derivative L1 without any C3 claim for the cutoff.
-/

open MeasureTheory

namespace LpSelfSimilar.Fourier

/-- The actual frequency derivative has an integrable inverse for every C3 amplitude. -/
theorem integrable_angularInverseFourier_deriv_scaled_quinticCutoff_mul {ε r : ℝ}
    (hε : 0 < ε) (hr : 0 < r) {P : ℝ → ℂ} (hP : ContDiff ℝ 3 P) :
    Integrable (angularInverseFourier
      (deriv (fun ξ => (quinticFourierCutoff ε (r * ξ) : ℂ) * P ξ))) := by
  let s : ℝ → ℂ := fun ξ => (quinticFourierCutoffSlope ε (r * ξ) : ℂ) * P ξ
  let t : ℝ → ℂ := fun ξ => (quinticFourierCutoff ε (r * ξ) : ℂ) * deriv P ξ
  have hP' : ContDiff ℝ 2 (deriv P) := hP.deriv'
  have hs : Integrable s ∧ Integrable (angularInverseFourier s) :=
    scaled_quinticCutoffSlope_mul_integrable_and_inverse hε hr (hP.of_le (by norm_num))
  have ht : Integrable t :=
    (integrable_scaled_quinticCutoff_mul_and_deriv hε hr (hP'.of_le (by norm_num))).1
  have hti : Integrable (angularInverseFourier t) :=
    integrable_angularInverseFourier_scaled_quinticCutoff_mul hε hr hP'
  have he : deriv (fun ξ => (quinticFourierCutoff ε (r * ξ) : ℂ) * P ξ) =
      (fun ξ => (r : ℂ) * s ξ + t ξ) := by
    funext ξ
    rw [(hasDerivAt_scaled_quinticCutoff_mul ε r ξ
      ((hP.differentiable (by norm_num) ξ).hasDerivAt)).deriv]
    dsimp only [s, t]
    ring
  have hi : angularInverseFourier
      (deriv (fun ξ => (quinticFourierCutoff ε (r * ξ) : ℂ) * P ξ)) =
      (fun x => (r : ℂ) * angularInverseFourier s x + angularInverseFourier t x) := by
    rw [he]
    funext x
    rw [angularInverseFourier_add (hs.1.const_mul (r : ℂ)) ht, angularInverseFourier_const_mul]
  rw [hi]
  exact (hs.2.const_mul (r : ℂ)).add hti

/-- The actual product derivative has exactly the spatial multiplier required by weighted Plancherel. -/
theorem angularInverseFourier_deriv_scaled_quinticCutoff_mul {ε r : ℝ}
    (hε : 0 < ε) (hr : 0 < r) {P : ℝ → ℂ} (hP : ContDiff ℝ 1 P) (x : ℝ) :
    angularInverseFourier (deriv (fun ξ => (quinticFourierCutoff ε (r * ξ) : ℂ) * P ξ)) x =
      -Complex.I * (x : ℂ) *
        angularInverseFourier (fun ξ => (quinticFourierCutoff ε (r * ξ) : ℂ) * P ξ) x := by
  have hq : ContDiff ℝ 1 (fun ξ => (quinticFourierCutoff ε (r * ξ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_one_quinticFourierCutoff hε).comp (by fun_prop))
  exact angularInverseFourier_deriv_of_compact_support (hq.mul hP)
    (hasCompactSupport_scaled_quinticCutoff_mul hε hr P) x

end LpSelfSimilar.Fourier
