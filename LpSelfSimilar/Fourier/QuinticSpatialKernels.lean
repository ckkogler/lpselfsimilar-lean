module

public import LpSelfSimilar.Fourier.AngularInverseReality
public import LpSelfSimilar.Fourier.QuinticCutoffInversion
public import LpSelfSimilar.Fourier.QuinticDetailKernel

@[expose] public section

/-!
# The actual real quintic smoothing and detail kernels

Both frequency multipliers are real and even, so their inverse integrals equal
the complex embeddings of their real parts. These definitions therefore retain
the previously proved integral kernels exactly. Their continuity and L1
integrability are inherited from the actual inverse-transform estimates.
-/

open MeasureTheory

namespace LpSelfSimilar.Fourier

/-- The explicit derivative of the even cutoff is odd, including the totalized zero width. -/
theorem quinticFourierCutoffSlope_neg (ε x : ℝ) :
    quinticFourierCutoffSlope ε (-x) = -quinticFourierCutoffSlope ε x := by
  unfold quinticFourierCutoffSlope
  rw [neg_neg]
  ring

/-- The actual detail multiplier is even. -/
theorem quinticFourierDetail_neg (ε x : ℝ) :
    quinticFourierDetail ε (-x) = quinticFourierDetail ε x := by
  unfold quinticFourierDetail
  rw [(hasDerivAt_quinticFourierCutoff ε (-x)).deriv,
    (hasDerivAt_quinticFourierCutoff ε x).deriv, quinticFourierCutoffSlope_neg]
  ring

/-- The real smoothing kernel defined by the actual angular inverse cutoff integral. -/
noncomputable def quinticSmoothingKernel (ε x : ℝ) : ℝ :=
  (angularInverseFourier (fun ξ => (quinticFourierCutoff ε ξ : ℂ)) x).re

/-- The real detail kernel defined by the actual angular inverse detail integral. -/
noncomputable def quinticDetailKernel (ε x : ℝ) : ℝ :=
  (angularInverseFourier (fun ξ => (quinticFourierDetail ε ξ : ℂ)) x).re

/-- The smoothing kernel's complex embedding is the exact previously constructed inverse. -/
theorem ofReal_quinticSmoothingKernel (ε x : ℝ) :
    (quinticSmoothingKernel ε x : ℂ) =
      angularInverseFourier (fun ξ => (quinticFourierCutoff ε ξ : ℂ)) x :=
  ofReal_re_angularInverseFourier_of_even _ (quinticFourierCutoff_neg ε) x

/-- The detail kernel's complex embedding is the exact previously constructed inverse. -/
theorem ofReal_quinticDetailKernel (ε x : ℝ) :
    (quinticDetailKernel ε x : ℂ) =
      angularInverseFourier (fun ξ => (quinticFourierDetail ε ξ : ℂ)) x :=
  ofReal_re_angularInverseFourier_of_even _ (quinticFourierDetail_neg ε) x

/-- The actual real smoothing kernel is integrable. -/
theorem integrable_quinticSmoothingKernel {ε : ℝ} (hε : 0 < ε) :
    Integrable (quinticSmoothingKernel ε) :=
  (integrable_continuous_angularInverseFourier_quinticCutoff hε).1.re

/-- The actual real smoothing kernel is continuous. -/
theorem continuous_quinticSmoothingKernel {ε : ℝ} (hε : 0 < ε) :
    Continuous (quinticSmoothingKernel ε) :=
  Complex.continuous_re.comp (integrable_continuous_angularInverseFourier_quinticCutoff hε).2

/-- The actual real detail kernel is integrable. -/
theorem integrable_quinticDetailKernel {ε : ℝ} (hε : 0 < ε) :
    Integrable (quinticDetailKernel ε) :=
  (integrable_continuous_angularInverseFourier_quinticDetail hε).1.re

/-- The actual real detail kernel is continuous. -/
theorem continuous_quinticDetailKernel {ε : ℝ} (hε : 0 < ε) :
    Continuous (quinticDetailKernel ε) :=
  Complex.continuous_re.comp (integrable_continuous_angularInverseFourier_quinticDetail hε).2

end LpSelfSimilar.Fourier
