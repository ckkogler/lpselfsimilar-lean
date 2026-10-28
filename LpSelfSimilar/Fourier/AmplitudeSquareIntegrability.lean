module

public import LpSelfSimilar.Fourier.AngularParseval

@[expose] public section

/-!
# Square integrability of an amplitude with an integrable inverse

Pointwise Fourier inversion bounds the continuous amplitude by the L1 norm
of its actual inverse. Multiplying this uniform bound by the amplitude's
L1 norm supplies the square integrability needed to split energy integrals.
-/

open MeasureTheory

namespace LpSelfSimilar.Fourier

/-- An L1 amplitude with a continuous representative and L1 inverse has an integrable squared norm. -/
theorem integrable_sq_norm_of_integrable_angularInverseFourier {f : ℝ → ℂ}
    (hc : Continuous f) (hf : Integrable f) (hi : Integrable (angularInverseFourier f)) :
    Integrable (fun u : ℝ => ‖f u‖ ^ 2) := by
  have hb : ∀ u : ℝ, ‖f u‖ ≤ ∫ x : ℝ, ‖angularInverseFourier f x‖ := by
    intro u
    rw [← angularFourier_angularInverseFourier hc hf hi u]
    exact norm_integral_angularFourierPhase_mul_le (angularInverseFourier f) (-u)
  simpa only [sq] using hf.norm.bdd_mul hc.norm.aestronglyMeasurable
    (ae_of_all _ (fun u => by simpa only [norm_norm] using hb u))

end LpSelfSimilar.Fourier
