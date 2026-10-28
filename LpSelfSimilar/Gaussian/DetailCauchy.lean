module

public import LpSelfSimilar.Gaussian.LogarithmicSmoothing
public import LpSelfSimilar.Gaussian.SmoothingMeasure
public import LpSelfSimilar.Analysis.InverseSquareIntegral
public import LpSelfSimilar.Analysis.NonnegativeL1Limit

@[expose] public section

/-!
Inverse-square detail decay makes Gaussian smoothings Cauchy in L1. This module
constructs the nonnegative integrable limit; identifying its measure is a
separate approximate-identity argument.
-/

open MeasureTheory MeasureTheory.Measure Real Set Filter
open scoped Topology

namespace LpSelfSimilar.Gaussian

lemma integral_logarithmic_detail_le {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (h : ∀ R ∈ Icc a b, detail μ (exp (-R)) ≤ 1 / R ^ 2) :
    (∫ R in a..b, detail μ (exp (-R))) ≤ 1 / a := by
  have hc : ContinuousOn (fun R : ℝ ↦ 1 / R ^ 2) (Icc a b) := by
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    exact fun R hR ↦ pow_ne_zero _ (ha.trans_le hR.1).ne'
  apply le_trans _ (integral_inverse_sq_le ha hab)
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  apply integral_mono_ae (integrableOn_detail_logarithmic μ a b)
    (hc.intervalIntegrable_of_Icc hab).1
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with R hR
  exact h R ⟨hR.1.le, hR.2⟩

lemma smoothing_difference_le_inverse_logarithmic (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (h : ∀ R ∈ Icc a b, detail μ (exp (-R)) ≤ 1 / R ^ 2) :
    (∫ x, |smooth μ ((exp (-b)) ^ 2) x - smooth μ ((exp (-a)) ^ 2) x|) ≤
      (2 / detailNormalization) / a := by
  apply (smoothing_difference_le_logarithmic_detail μ hab).trans
  have hQ : 0 ≤ 2 / detailNormalization :=
    div_nonneg (by norm_num) detailNormalization_pos.le
  exact (mul_le_mul_of_nonneg_left (integral_logarithmic_detail_le ha hab h) hQ).trans_eq
    (by ring)

/-- The limit is an actual nonnegative integrable real function, not a
postulated density. Its equality to the original law is established separately. -/
theorem exists_smoothing_L1_limit (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {A : ℝ} (hA : 0 < A)
    (h : ∀ R : ℝ, A ≤ R → detail μ (exp (-R)) ≤ 1 / R ^ 2) :
    ∃ f : ℝ → ℝ, Integrable f volume ∧ (∀ x, 0 ≤ f x) ∧
      Tendsto (fun n : ℕ ↦ ∫ x,
        |smooth μ ((exp (-(A + n))) ^ 2) x - f x|) atTop (𝓝 0) := by
  have hseq : Tendsto (fun n : ℕ ↦ A + (n : ℝ)) atTop atTop := by
    apply tendsto_atTop.2
    intro c
    obtain ⟨N, hN⟩ := exists_nat_ge (c - A)
    apply eventually_atTop.2
    refine ⟨N, ?_⟩
    intro n hn
    have hnR : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
    linarith
  have hb : Tendsto (fun n : ℕ ↦ (2 / detailNormalization) / (A + n)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp hseq).const_mul (2 / detailNormalization)
  apply exists_nonnegative_L1_limit
    (fun n : ℕ ↦ smooth μ ((exp (-(A + n))) ^ 2))
    (fun n ↦ integrable_smooth μ (by positivity))
    (fun n ↦ ae_of_all _ (fun x ↦ smooth_nonneg μ (by positivity) x))
    (fun n : ℕ ↦ (2 / detailNormalization) / (A + n)) hb
  intro n m hnm
  have ha : 0 < A + (n : ℝ) := by positivity
  have hab : A + (n : ℝ) ≤ A + (m : ℝ) := add_le_add le_rfl (Nat.cast_le.mpr hnm)
  have hc := smoothing_difference_le_inverse_logarithmic μ ha hab
    (fun R hR ↦ h R ((le_add_of_nonneg_right (Nat.cast_nonneg n)).trans hR.1))
  simpa only [abs_sub_comm] using hc

end LpSelfSimilar.Gaussian
