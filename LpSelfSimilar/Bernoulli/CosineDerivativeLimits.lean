module

public import LpSelfSimilar.Bernoulli.CosineProducts
public import LpSelfSimilar.Bernoulli.FiniteBounds
public import LpSelfSimilar.Fourier.CharacteristicDerivativeLimits

@[expose] public section

/-!
# Derivative limits for the actual Bernoulli cosine products

Finite prefixes and the infinite fair-sign series share a geometric absolute
bound. Thus their actual laws have every moment, and their characteristic
functions converge together with every derivative at each frequency. The cosine
identities identify the finite functions before differentiating them.
-/

open MeasureTheory Filter
open scoped BigOperators Topology ENNReal

namespace LpSelfSimilar.Bernoulli

/-- Every scaled Bernoulli law in the contracting nonnegative range has all moments. -/
theorem memLp_id_scaled_convolution {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (a : ℝ) (p : ℝ≥0∞) : MemLp id p ((convolution θ).map (fun x ↦ a * x)) := by
  rw [convolution, Measure.map_map (by fun_prop) (measurable_series θ)]
  apply Fourier.memLp_id_map_of_ae_abs_le digitSpace (by fun_prop)
    (S := |a| * (1 - θ)⁻¹) _ p
  exact ae_of_all _ (fun w ↦ by
    simp only [Function.comp_apply, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_series_le hθ0 hθ1 w) (abs_nonneg a))

/-- Scaled finite-prefix characteristic derivatives converge to those of the actual infinite law. -/
theorem tendsto_iteratedDeriv_scaled_prefix {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (a : ℝ) (k : ℕ) (s : ℝ) :
    Tendsto (fun n : ℕ ↦ iteratedDeriv k
      (charFun (digitSpace.map (fun w ↦ a * digitSum θ (fun j : Fin n ↦ w j)))) s)
      atTop (𝓝 (iteratedDeriv k (charFun ((convolution θ).map (fun x ↦ a * x))) s)) := by
  have hθ : |θ| < 1 := by rwa [abs_of_nonneg hθ0]
  rw [convolution, Measure.map_map (by fun_prop) (measurable_series θ)]
  apply Fourier.tendsto_iteratedDeriv_charFun_map_of_ae_tendsto digitSpace
    (S := |a| * (1 - θ)⁻¹)
  · intro n
    unfold digitSum
    fun_prop
  · fun_prop
  · intro n
    exact ae_of_all _ (fun w ↦ by
      simp only [Function.comp_apply, abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_digitSum_le hθ0 hθ1 _) (abs_nonneg a))
  · exact ae_of_all _ (fun w ↦ by
      simp only [Function.comp_apply, abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_series_le hθ0 hθ1 w) (abs_nonneg a))
  · exact ae_of_all _ (fun w ↦ tendsto_const_nhds.mul (tendsto_digitSum hθ w))

/-- The differentiated finite cosine products converge to actual Bernoulli characteristic derivatives. -/
theorem tendsto_iteratedDeriv_cosine_products {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (a : ℝ) (k : ℕ) (s : ℝ) :
    Tendsto (fun n : ℕ ↦ iteratedDeriv k
      (fun y : ℝ ↦ ∏ j : Fin n, (Real.cos ((a * θ ^ (j : ℕ)) * y) : ℂ)) s)
      atTop (𝓝 (iteratedDeriv k (charFun ((convolution θ).map (fun x ↦ a * x))) s)) := by
  have he (n : ℕ) :
      charFun (digitSpace.map (fun w ↦ a * digitSum θ (fun j : Fin n ↦ w j))) =
        fun y : ℝ ↦ ∏ j : Fin n, (Real.cos ((a * θ ^ (j : ℕ)) * y) : ℂ) := by
    funext y
    rw [charFun_scaled_prefix, Complex.ofReal_prod]
    congr 1
    funext j
    rw [mul_comm y]
  have h := tendsto_iteratedDeriv_scaled_prefix hθ0 hθ1 a k s
  simp_rw [he] at h
  exact h

end LpSelfSimilar.Bernoulli
