module

public import LpSelfSimilar.Gaussian.DetailCauchy
public import LpSelfSimilar.Analysis.BoundedTestLimit

@[expose] public section

/-!
The quantitative L1 cost of removing Gaussian smoothing. Inverse-square detail
controls the small radii, while a uniform weak-detail bound controls the finite
logarithmic interval up to radius one. Identification of the limit measure is
kept separate from this norm estimate.
-/

open MeasureTheory MeasureTheory.Measure Real Set Filter
open scoped Topology

namespace LpSelfSimilar.Gaussian

lemma smoothing_difference_le_weak_detail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {A δ : ℝ} (hA : 0 ≤ A)
    (h : ∀ r : ℝ, 0 < r → r ≤ 1 → detail μ r ≤ δ) :
    (∫ x, |smooth μ ((exp (-A)) ^ 2) x - smooth μ 1 x|) ≤
      (2 / detailNormalization) * (δ * A) := by
  have hc := smoothing_difference_le_logarithmic_detail μ hA
  simp only [neg_zero, exp_zero, one_pow] at hc
  apply hc.trans
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) detailNormalization_pos.le)
  have hh : (∫ R in (0 : ℝ)..A, detail μ (exp (-R))) ≤ ∫ _R in (0 : ℝ)..A, δ := by
    rw [intervalIntegral.integral_of_le hA, intervalIntegral.integral_of_le hA]
    apply integral_mono_ae (integrableOn_detail_logarithmic μ 0 A) (integrable_const δ)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with R hR
    exact h _ (exp_pos _) (exp_le_one_iff.mpr (by linarith [hR.1]))
  exact hh.trans_eq (by simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]; ring)

/-- A limit supplied by inverse-square detail satisfies the quantitative
bounded-approximation estimate, without a density assumption. -/
theorem smoothing_L1_limit_approximation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {A δ : ℝ} (hA : 0 < A)
    (hdecay : ∀ R : ℝ, A ≤ R → detail μ (exp (-R)) ≤ 1 / R ^ 2)
    (hweak : ∀ r : ℝ, 0 < r → r ≤ 1 → detail μ r ≤ δ)
    {f : ℝ → ℝ} (hf : Integrable f volume)
    (hlim : Tendsto (fun n : ℕ ↦ ∫ x,
      |smooth μ ((exp (-(A + n))) ^ 2) x - f x|) atTop (𝓝 0)) :
    (∫ x, |f x - smooth μ 1 x|) ≤ (2 / detailNormalization) * (1 / A + δ * A) := by
  apply integral_abs_sub_le_of_L1_limit
    (fun n : ℕ ↦ integrable_smooth μ (by positivity : 0 < (exp (-(A + n))) ^ 2))
    hf (integrable_smooth μ (by norm_num : (0 : ℝ) < 1)) hlim
  intro n
  have hab : A ≤ A + (n : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg n)
  have htail := smoothing_difference_le_inverse_logarithmic μ hA hab
    (fun R hR ↦ hdecay R hR.1)
  have hstart := smoothing_difference_le_weak_detail μ hA.le hweak
  have htri := integral_abs_sub_triangle
    (integrable_smooth μ (by positivity : 0 < (exp (-(A + n))) ^ 2))
    (integrable_smooth μ (by positivity : 0 < (exp (-A)) ^ 2))
    (integrable_smooth μ (by norm_num : (0 : ℝ) < 1))
  exact (htri.trans (add_le_add htail hstart)).trans_eq (by ring)

end LpSelfSimilar.Gaussian
