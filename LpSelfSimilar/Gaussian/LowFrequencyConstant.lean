module

public import LpSelfSimilar.Gaussian.EvenMoments
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-!
# The exact low-frequency Gaussian error constant

Squaring the zeroth and first derivative error bounds gives the polynomial
u^10 + 9*u^8 + 16*u^6 against exp(-u^2). Its integral is computed exactly
from Gaussian even moments. The resulting weighted Fourier constant is
strictly less than 1.709, using a proved rational upper bound for pi.
-/

open MeasureTheory

namespace LpSelfSimilar.Gaussian

/-- The polynomial Gaussian majorant for both squared Fourier errors is integrable. -/
theorem integrable_lowFrequencyGaussianEnergy :
    Integrable (fun u : ℝ => (u ^ 10 + 9 * u ^ 8 + 16 * u ^ 6) * Real.exp (-(u ^ 2))) := by
  have h := ((integrable_gaussian_even_moment 5).add
    ((integrable_gaussian_even_moment 4).const_mul 9)).add
    ((integrable_gaussian_even_moment 3).const_mul 16)
  convert! h using 1
  funext u
  simp only [Pi.add_apply]
  ring

/-- Exact integral of the low-frequency polynomial Gaussian majorant. -/
theorem integral_lowFrequencyGaussianEnergy :
    (∫ u : ℝ, (u ^ 10 + 9 * u ^ 8 + 16 * u ^ 6) * Real.exp (-(u ^ 2))) =
      (3795 / 32 : ℝ) * Real.sqrt Real.pi := by
  have he (u : ℝ) : (u ^ 10 + 9 * u ^ 8 + 16 * u ^ 6) * Real.exp (-(u ^ 2)) =
      (u ^ (2 * 5) * Real.exp (-(u ^ 2)) + 9 * (u ^ (2 * 4) * Real.exp (-(u ^ 2)))) +
        16 * (u ^ (2 * 3) * Real.exp (-(u ^ 2))) := by ring
  simp_rw [he]
  have hsum : Integrable (fun u : ℝ => u ^ (2 * 5) * Real.exp (-(u ^ 2)) +
      9 * (u ^ (2 * 4) * Real.exp (-(u ^ 2)))) := by
    simpa only [Pi.add_apply] using!
      (integrable_gaussian_even_moment 5).add ((integrable_gaussian_even_moment 4).const_mul 9)
  rw [integral_add hsum ((integrable_gaussian_even_moment 3).const_mul 16),
    integral_add (integrable_gaussian_even_moment 5)
      ((integrable_gaussian_even_moment 4).const_mul 9),
    integral_const_mul, integral_const_mul,
    integral_gaussian_even_moment, integral_gaussian_even_moment,
    integral_gaussian_even_moment,
    Real.Gamma_nat_add_half, Real.Gamma_nat_add_half, Real.Gamma_nat_add_half]
  norm_num [Nat.doubleFactorial]
  <;> ring

/-- The exact constant multiplying chi in the low-frequency square-root energy. -/
noncomputable def lowFrequencyGaussianConstant : ℝ :=
  Real.sqrt ((Real.Gamma (11 / 2) + 9 * Real.Gamma (9 / 2) + 16 * Real.Gamma (7 / 2)) / 72)

/-- The Gamma expression for the square of the constant reduces to a rational multiple of sqrt(pi). -/
theorem lowFrequencyGaussianConstant_eq :
    lowFrequencyGaussianConstant = Real.sqrt ((1265 / 768 : ℝ) * Real.sqrt Real.pi) := by
  unfold lowFrequencyGaussianConstant
  congr 1
  have h5 := Real.Gamma_nat_add_half 5
  have h4 := Real.Gamma_nat_add_half 4
  have h3 := Real.Gamma_nat_add_half 3
  norm_num [Nat.doubleFactorial] at h5 h4 h3
  rw [h5, h4, h3]
  ring

/-- A rational upper bound for sqrt(pi), proved from Mathlib's bound for pi. -/
theorem sqrt_pi_lt_1773_div_1000 : Real.sqrt Real.pi < (1773 / 1000 : ℝ) := by
  have hsq := Real.sq_sqrt Real.pi_pos.le
  have hpi := Real.pi_lt_d4
  have hnonneg := Real.sqrt_nonneg Real.pi
  nlinarith

/-- The exact low-frequency constant is strictly below the source's decimal bound. -/
theorem lowFrequencyGaussianConstant_lt_1709_div_1000 :
    lowFrequencyGaussianConstant < (1709 / 1000 : ℝ) := by
  rw [lowFrequencyGaussianConstant_eq]
  have harg : 0 ≤ (1265 / 768 : ℝ) * Real.sqrt Real.pi := by positivity
  have hsq := Real.sq_sqrt harg
  have hpi := sqrt_pi_lt_1773_div_1000
  have hn := Real.sqrt_nonneg ((1265 / 768 : ℝ) * Real.sqrt Real.pi)
  nlinarith

/-- The convenient seven-fourths upper bound follows with room to spare. -/
theorem lowFrequencyGaussianConstant_lt_seven_fourths :
    lowFrequencyGaussianConstant < (7 / 4 : ℝ) := by
  exact lowFrequencyGaussianConstant_lt_1709_div_1000.trans (by norm_num)

end LpSelfSimilar.Gaussian
