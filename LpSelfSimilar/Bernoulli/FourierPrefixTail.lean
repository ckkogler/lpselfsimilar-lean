module

public import LpSelfSimilar.Probability.MapProbability

public import LpSelfSimilar.Bernoulli.CosineProducts
public import LpSelfSimilar.Analysis.CosineFirstDerivativeBounds
public import Mathlib.Algebra.Field.GeomSum

@[expose] public section

/-!
# Actual Fourier factorization into a finite prefix and infinite tail

The probability decomposition at a natural digit index gives a pointwise
identity of characteristic functions. The finite cosine prefix has norm at
most one, and its derivative costs precisely the finite coefficient sum.
Keeping the factor 1-theta^n is necessary when adding the tail derivative cost.
-/

open MeasureTheory
open scoped BigOperators
open LpSelfSimilar.Analysis

namespace LpSelfSimilar.Bernoulli

/-- The actual scaled Bernoulli transform splits at every natural digit index. -/
theorem charFun_scaled_convolution_prefix_tail {θ : ℝ} (hθ : |θ| < 1)
    (a u : ℝ) (n : ℕ) :
    charFun ((convolution θ).map (fun x => a * x)) u =
      (∏ j : Fin n, (Real.cos ((a * θ ^ (j : ℕ)) * u) : ℂ)) *
        charFun ((convolution θ).map (fun x => (a * θ ^ n) * x)) u := by
  have : IsProbabilityMeasure ((convolution θ).map (fun x => θ ^ n * x)) :=
    LpSelfSimilar.Probability.isProbabilityMeasure_map (by fun_prop)
  rw [charFun_map_mul]
  conv_lhs => rw [convolution_prefix_tail hθ n]
  rw [charFun_conv, charFun_map_mul, ← digitSum_law θ n]
  have hp := charFun_scaled_prefix 1 θ (a * u) n
  simp only [one_mul] at hp
  rw [hp, charFun_map_mul, Complex.ofReal_prod]
  congr 1
  · apply Finset.prod_congr rfl
    intro j hj
    congr 2
    ring
  · congr 1
    ring

/-- Discarding the finite prefix loses no Fourier norm. -/
theorem norm_cosine_prefix_le_one (a θ u : ℝ) (n : ℕ) :
    ‖∏ j : Fin n, (Real.cos ((a * θ ^ (j : ℕ)) * u) : ℂ)‖ ≤ 1 := by
  rw [norm_prod]
  apply Finset.prod_le_one₀
  · intro j hj
    exact norm_nonneg _
  · intro j hj
    simpa only [Complex.norm_real, Real.norm_eq_abs] using Real.abs_cos_le_one ((a * θ ^ (j : ℕ)) * u)

/-- The prefix derivative is bounded by its exact finite coefficient sum. -/
theorem norm_deriv_cosine_prefix_le {θ a : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (ha : 0 ≤ a) (u : ℝ) (n : ℕ) :
    ‖deriv (fun v : ℝ => ∏ j : Fin n, (Real.cos ((a * θ ^ (j : ℕ)) * v) : ℂ)) u‖ ≤
      a * (1 - θ ^ n) / (1 - θ) := by
  have hb := norm_deriv_cosine_prod_le_sum Finset.univ (fun j : Fin n => a * θ ^ (j : ℕ))
    u (fun j hj => mul_nonneg ha (pow_nonneg hθ0 _))
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range] at hb
  have hs : (∑ j ∈ Finset.range n, θ ^ j) = (1 - θ ^ n) / (1 - θ) :=
    (eq_div_iff (sub_pos.mpr hθ1).ne').mpr (geom_sum_mul_neg θ n)
  rw [hs] at hb
  simpa only [mul_div_assoc] using hb

end LpSelfSimilar.Bernoulli
