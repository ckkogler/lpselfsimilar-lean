module

public import LpSelfSimilar.Gaussian.TailMoments
public import LpSelfSimilar.Gaussian.StandardFourierDerivative
public import LpSelfSimilar.Analysis.EvenTailIntegral

@[expose] public section

/-!
# The integrated Fourier energy of a Gaussian tail

The actual Gaussian amplitude and its derivative give (1+u^2) exp(-u^2).
Reflection and the exact half-line moment estimates retain the coefficient
b/2 + 3/(4*b), including the one-half weight of the Fourier energy.
-/

open MeasureTheory Set

namespace LpSelfSimilar.Gaussian

/-- The squared norm of the standard Gaussian amplitude. -/
theorem sq_norm_standardGaussianAmplitude (u : ℝ) :
    ‖standardGaussianAmplitude u‖ ^ 2 = Real.exp (-(u ^ 2)) := by
  simp only [standardGaussianAmplitude, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- The actual amplitude and derivative have their exact scalar energy density. -/
theorem standardGaussian_fourier_energy (u : ℝ) :
    ‖standardGaussianAmplitude u‖ ^ 2 + ‖deriv standardGaussianAmplitude u‖ ^ 2 =
      (1 + u ^ 2) * Real.exp (-(u ^ 2)) := by
  rw [(hasDerivAt_standardGaussianAmplitude u).deriv, norm_mul, norm_neg,
    Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
    sq_norm_standardGaussianAmplitude]
  ring

/-- Both parts of the actual Gaussian Fourier energy are integrable. -/
theorem integrable_standardGaussian_fourier_energy :
    Integrable (fun u : ℝ =>
      ‖standardGaussianAmplitude u‖ ^ 2 + ‖deriv standardGaussianAmplitude u‖ ^ 2) := by
  have h0 : Integrable (fun u : ℝ => Real.exp (-(u ^ 2))) := by
    simpa only [Nat.mul_zero, pow_zero, one_mul] using integrable_gaussian_even_moment 0
  have h2 : Integrable (fun u : ℝ => u ^ 2 * Real.exp (-(u ^ 2))) := by
    simpa only [Nat.mul_one] using integrable_gaussian_even_moment 1
  convert! h0.add h2 using 1
  funext u
  rw [standardGaussian_fourier_energy]
  simp only [Pi.add_apply]
  ring

/-- Half the two-sided actual Gaussian tail energy has the exact elementary upper bound. -/
theorem half_integral_standardGaussian_tail_energy_le {b : ℝ} (hb : 0 < b) :
    (1 / 2 : ℝ) * (∫ u : ℝ in {u | b < |u|},
      ‖standardGaussianAmplitude u‖ ^ 2 + ‖deriv standardGaussianAmplitude u‖ ^ 2) ≤
      (b / 2 + 3 / (4 * b)) * Real.exp (-(b ^ 2)) := by
  have h0 : Integrable (fun u : ℝ => Real.exp (-(u ^ 2))) := by
    simpa only [Nat.mul_zero, pow_zero, one_mul] using integrable_gaussian_even_moment 0
  have h2 : Integrable (fun u : ℝ => u ^ 2 * Real.exp (-(u ^ 2))) := by
    simpa only [Nat.mul_one] using integrable_gaussian_even_moment 1
  rw [LpSelfSimilar.Analysis.integral_abs_tail_eq_twice_Ioi hb.le
    integrable_standardGaussian_fourier_energy (fun u => by
      rw [standardGaussian_fourier_energy, standardGaussian_fourier_energy, neg_sq])]
  have he : (∫ u : ℝ in Ioi b,
      ‖standardGaussianAmplitude u‖ ^ 2 + ‖deriv standardGaussianAmplitude u‖ ^ 2) =
      (∫ u : ℝ in Ioi b, Real.exp (-(u ^ 2))) +
      ∫ u : ℝ in Ioi b, u ^ 2 * Real.exp (-(u ^ 2)) := by
    rw [← integral_add h0.integrableOn h2.integrableOn]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp only
    rw [standardGaussian_fourier_energy]
    ring
  rw [he]
  have hz := integral_Ioi_exp_neg_sq_le hb
  have hs := integral_Ioi_sq_mul_exp_neg_sq_le hb
  calc
    _ = (∫ u : ℝ in Ioi b, Real.exp (-(u ^ 2))) +
        ∫ u : ℝ in Ioi b, u ^ 2 * Real.exp (-(u ^ 2)) := by ring
    _ ≤ Real.exp (-(b ^ 2)) / (2 * b) +
        (b / 2 + 1 / (4 * b)) * Real.exp (-(b ^ 2)) := add_le_add hz hs
    _ = _ := by ring

end LpSelfSimilar.Gaussian
