module

public import LpSelfSimilar.Bernoulli.NormalizedFourierBounds

@[expose] public section

/-!
# The actual infinite logarithmic Gaussian remainder

Strict positivity of the actual Fourier transform on the closed unit-angle
interval makes its logarithm legitimate. The Gaussian upper and quartic lower
bounds give the exact remainder bounds. Actual finite logarithmic remainders
converge to this function, and their nonnegativity upgrades that limit to an
unconditional HasSum statement.
-/

open Filter
open LpSelfSimilar.Analysis
open scoped Topology

namespace LpSelfSimilar.Bernoulli

/-- The actual logarithmic remainder of the variance-scaled Bernoulli characteristic function. -/
noncomputable def varianceNormalizedLogRemainder (θ u : ℝ) : ℝ :=
  -Real.log (varianceNormalizedFourier θ u) - u ^ 2 / 2

/-- The logarithmic remainder has its actual quotient-rule derivative wherever Phi is nonzero. -/
theorem hasDerivAt_varianceNormalizedLogRemainder {θ u : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hΦ : varianceNormalizedFourier θ u ≠ 0) :
    HasDerivAt (varianceNormalizedLogRemainder θ)
      (-(deriv (varianceNormalizedFourier θ) u) / varianceNormalizedFourier θ u - u) u := by
  have hd := (hasDerivAt_varianceNormalizedFourier hθ0 hθ1 u).differentiableAt.hasDerivAt
  unfold varianceNormalizedLogRemainder
  convert! ((hd.log hΦ).neg).sub (((hasDerivAt_id u).pow 2).div_const 2)
    using 1 <;> (try simp only [id_eq]) <;> ring

/-- The actual infinite transform is exactly its Gaussian times the exponential remainder. -/
theorem varianceNormalizedFourier_eq_gaussian_remainder {θ u : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hu : |Real.sqrt (1 - θ ^ 2) * u| ≤ 1) :
    varianceNormalizedFourier θ u =
      Real.exp (-(u ^ 2) / 2 - varianceNormalizedLogRemainder θ u) := by
  have he : -(u ^ 2) / 2 - varianceNormalizedLogRemainder θ u =
      Real.log (varianceNormalizedFourier θ u) := by
    unfold varianceNormalizedLogRemainder
    ring
  rw [he, Real.exp_log (varianceNormalizedFourier_pos hθ0 hθ1 hu)]

/-- The actual infinite remainder lies between zero and chi*u^4/6. -/
theorem varianceNormalizedLogRemainder_bounds {θ u : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hu : |Real.sqrt (1 - θ ^ 2) * u| ≤ 1) :
    0 ≤ varianceNormalizedLogRemainder θ u ∧
      varianceNormalizedLogRemainder θ u ≤ (-Real.log θ) * u ^ 4 / 6 := by
  have h := varianceNormalizedFourier_bounds hθ0 hθ1 hu
  have hp := varianceNormalizedFourier_pos hθ0 hθ1 hu
  have hlo := (Real.le_log_iff_exp_le hp).mpr h.1
  have hhi := (Real.log_le_iff_le_exp hp).mpr h.2
  unfold varianceNormalizedLogRemainder
  constructor <;> linarith

/-- Finite sums of actual log-cosine errors converge to the infinite logarithmic remainder. -/
theorem tendsto_sum_logCosineRemainder {θ u : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hu : |Real.sqrt (1 - θ ^ 2) * u| ≤ 1) :
    Tendsto (fun n : ℕ => ∑ j : Fin n,
      logCosineRemainder (varianceNormalizedCoefficient θ j * u)) atTop
      (𝓝 (varianceNormalizedLogRemainder θ u)) := by
  have hp := tendsto_real_varianceNormalized_cosine_products hθ0.le hθ1 u
  have hs := tendsto_sum_sq_varianceNormalizedCoefficient hθ0.le hθ1
  have ht := (hs.const_mul (-(u ^ 2) / 2)).sub
    (hp.log (varianceNormalizedFourier_pos hθ0 hθ1 hu).ne')
  have hv : -(u ^ 2) / 2 * 1 - Real.log (varianceNormalizedFourier θ u) =
      varianceNormalizedLogRemainder θ u := by
    unfold varianceNormalizedLogRemainder
    ring
  rw [hv] at ht
  have he (n : ℕ) : (∑ j : Fin n, logCosineRemainder (varianceNormalizedCoefficient θ j * u)) =
      -(u ^ 2) / 2 * (∑ j : Fin n, varianceNormalizedCoefficient θ j ^ 2) -
        Real.log (∏ j : Fin n, Real.cos (varianceNormalizedCoefficient θ j * u)) := by
    apply sum_logCosineRemainder_eq_log_prod
    intro j hj
    have h := half_le_cos_of_abs_le_one
      (abs_varianceNormalizedCoefficient_mul_le_one hθ0.le hθ1.le hu j)
    linarith
  exact Tendsto.congr' (Eventually.of_forall (fun n => (he n).symm)) ht

/-- The actual infinite logarithmic remainder is the sum of the nonnegative digit remainders. -/
theorem hasSum_logCosineRemainder {θ u : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hu : |Real.sqrt (1 - θ ^ 2) * u| ≤ 1) :
    HasSum (fun n => logCosineRemainder (varianceNormalizedCoefficient θ n * u))
      (varianceNormalizedLogRemainder θ u) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg
    (fun n => (logCosineRemainder_bounds
      (abs_varianceNormalizedCoefficient_mul_le_one hθ0.le hθ1.le hu n)).1) _).mpr
  have h := tendsto_sum_logCosineRemainder hθ0 hθ1 hu
  have he : (fun n : ℕ => ∑ j : Fin n, logCosineRemainder (varianceNormalizedCoefficient θ j * u)) =
      (fun n : ℕ => ∑ j ∈ Finset.range n, logCosineRemainder (varianceNormalizedCoefficient θ j * u)) := by
    funext n
    exact Fin.sum_univ_eq_sum_range
      (fun j : ℕ => logCosineRemainder (varianceNormalizedCoefficient θ j * u)) n
  rwa [he] at h

/-- The actual logarithmic remainder is even. -/
theorem varianceNormalizedLogRemainder_neg {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (u : ℝ) :
    varianceNormalizedLogRemainder θ (-u) = varianceNormalizedLogRemainder θ u := by
  simp only [varianceNormalizedLogRemainder, varianceNormalizedFourier_neg hθ0 hθ1, neg_sq]

/-- The actual logarithmic remainder vanishes at zero. -/
theorem varianceNormalizedLogRemainder_zero {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    varianceNormalizedLogRemainder θ 0 = 0 := by
  simp [varianceNormalizedLogRemainder, varianceNormalizedFourier_zero hθ0 hθ1]

end LpSelfSimilar.Bernoulli
