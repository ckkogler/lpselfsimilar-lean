module

public import LpSelfSimilar.Analysis.PolynomialGaussianEnvelope
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

/-!
# Comparing the scale-integral coefficient with its Gaussian envelope

The constraints t>=6 and 2*t^2<=u^2 absorb every logarithmic-cost factor into
an explicit Gaussian profile in u. The proof separately checks the cubic cost,
the rational correction and the exponential correction before multiplying them.
-/

namespace LpSelfSimilar.Analysis

/-- The logarithmic-cost coefficient is bounded by the exact Gaussian profile. -/
theorem integrated_coefficient_le_gaussian_profile {t u : ℝ}
    (ht : 6 ≤ t) (hu : 0 ≤ u) (hsmall : 2 * t ^ 2 ≤ u ^ 2) :
    (Real.exp t / 150) ^ 4 * t ^ 3 * u ^ 4 *
      (1 + u ^ 2 / (1000 * t)) ^ 2 * Real.exp (-u ^ 2 / 2) ≤
        1 / ((150 : ℝ) ^ 4 * 2 * Real.sqrt 2) *
          polynomialGaussianEnvelope 6000 (2 * Real.sqrt 2) u := by
  have ht0 : 0 < t := by linarith
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hts : t * Real.sqrt 2 ≤ u := by
    have he : (t * Real.sqrt 2) ^ 2 = 2 * t ^ 2 := by rw [mul_pow, hs2]; ring
    nlinarith [mul_nonneg ht0.le hs.le]
  have htd : t ≤ u / Real.sqrt 2 := (le_div_iff₀ hs).mpr hts
  have hs3 : (Real.sqrt 2) ^ 3 = 2 * Real.sqrt 2 := by
    calc
      _ = (Real.sqrt 2) ^ 2 * Real.sqrt 2 := by ring
      _ = _ := by rw [hs2]
  have ht3 : t ^ 3 ≤ u ^ 3 / (2 * Real.sqrt 2) := by
    have hh := pow_le_pow_left₀ ht0.le htd 3
    simpa only [div_pow, hs3] using hh
  have hcorr : (1 + u ^ 2 / (1000 * t)) ^ 2 ≤ (1 + u ^ 2 / 6000) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    have hf : u ^ 2 / (1000 * t) ≤ u ^ 2 / 6000 :=
      div_le_div_of_nonneg_left (sq_nonneg u) (by norm_num) (by linarith)
    linarith
  have h4 : 4 * t ≤ 2 * Real.sqrt 2 * u := by
    calc
      _ = (2 * Real.sqrt 2) * (t * Real.sqrt 2) := by
        ring_nf
        rw [hs2]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hts (by positivity)
  have he : (Real.exp t) ^ 4 * Real.exp (-u ^ 2 / 2) = Real.exp (4 * t - u ^ 2 / 2) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = 1 / (150 : ℝ) ^ 4 * t ^ 3 * u ^ 4 * (1 + u ^ 2 / (1000 * t)) ^ 2 *
        Real.exp (4 * t - u ^ 2 / 2) := by
      rw [← he, div_pow]
      ring
    _ ≤ 1 / (150 : ℝ) ^ 4 * (u ^ 3 / (2 * Real.sqrt 2)) * u ^ 4 *
        (1 + u ^ 2 / 6000) ^ 2 * Real.exp (2 * Real.sqrt 2 * u - u ^ 2 / 2) := by
      gcongr
    _ = _ := by
      unfold polynomialGaussianEnvelope
      have hx : 2 * Real.sqrt 2 * u - u ^ 2 / 2 = -u ^ 2 / 2 + (2 * Real.sqrt 2) * u := by ring
      rw [hx]
      ring

end LpSelfSimilar.Analysis
