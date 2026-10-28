module

public import LpSelfSimilar.Gaussian.VarianceTaylor
public import LpSelfSimilar.Analysis.VarianceTaylorWeight
public import LpSelfSimilar.Analysis.IntegralRemainderEstimate

@[expose] public section

/-!
L1 control of the finite-variance Taylor formula. Product integrability is proved
from Gaussian scaling, and the remainder uses the exact rational weight integral.
-/

open MeasureTheory MeasureTheory.Measure Real Set

namespace LpSelfSimilar.Gaussian

lemma integral_abs_higherSmooth_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (k : ℕ) {a y : ℝ} (ha : 0 < a) (hay : a ≤ y) :
    (∫ x, |higherSmooth μ k y x|) ≤ a ^ (-(k : ℝ)) * higherKernelNorm k := by
  have hy := ha.trans_le hay
  have h := integral_abs_averageTranslate_le μ (continuous_higherKernel_space k y)
    (integrable_higherKernel k hy)
  rw [integral_abs_higherKernel k hy] at h
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_nonpos ha hay (neg_nonpos.mpr (Nat.cast_nonneg k)))
    (higherKernelNorm_nonneg k))

lemma integrable_varianceTaylor_product (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (n k : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Integrable (fun p : ℝ × ℝ ↦ (1 - p.1) ^ n * higherSmooth μ k (b + p.1 * (a - b)) p.2)
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod volume) := by
  have hm : Measurable (fun p : ℝ × ℝ ↦
      (1 - p.1) ^ n * higherSmooth μ k (b + p.1 * (a - b)) p.2) := by
    apply Measurable.mul (by fun_prop)
    exact (measurable_higherSmooth_joint μ k).comp
      (f := fun p : ℝ × ℝ ↦ (b + p.1 * (a - b), p.2)) (by fun_prop)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (integrable_higherSmooth μ k (variance_segment_pos ha hab ⟨ht.1.le, ht.2⟩)).const_mul _
  · apply (integrable_const (a ^ (-(k : ℝ)) * higherKernelNorm k)).mono'
      hm.stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hw : 0 ≤ (1 - t) ^ n := pow_nonneg (sub_nonneg.mpr ht.2) _
    have hw1 : (1 - t) ^ n ≤ 1 := pow_le_one₀ (sub_nonneg.mpr ht.2) (by linarith [ht.1])
    have hay : a ≤ b + t * (a - b) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr ht.2)]
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw, integral_const_mul,
      abs_of_nonneg (mul_nonneg hw (integral_nonneg (fun _ ↦ abs_nonneg _)))]
    exact (mul_le_mul_of_nonneg_left (integral_abs_higherSmooth_le μ k ha hay) hw).trans
      (mul_le_of_le_one_left (mul_nonneg (Real.rpow_nonneg ha.le _)
        (higherKernelNorm_nonneg k)) hw1)

lemma integral_varianceTaylor_product_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (n : ℕ) {a b D : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hD : ∀ y ∈ Icc a b, (∫ x, |higherSmooth μ (n + 2) y x|) ≤ D / y ^ (n + 2)) :
    (∫ t in Ioc (0 : ℝ) 1,
      ∫ x, |(1 - t) ^ n * higherSmooth μ (n + 2) (b + t * (a - b)) x|) ≤
      D * ∫ t in (0 : ℝ)..1, (1 - t) ^ n / (b + t * (a - b)) ^ (n + 2) := by
  have hi := (integrable_varianceTaylor_product μ n (n + 2) ha hab).abs.integral_prod_left
  have hc : ContinuousOn (fun t : ℝ ↦ D * ((1 - t) ^ n /
      (b + t * (a - b)) ^ (n + 2))) (Icc 0 1) := by
    apply ContinuousOn.const_mul
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    exact fun t ht ↦ pow_ne_zero _ (variance_segment_pos ha hab ht).ne'
  have hj : IntegrableOn (fun t : ℝ ↦ D * ((1 - t) ^ n /
      (b + t * (a - b)) ^ (n + 2))) (Ioc 0 1) volume :=
    (hc.intervalIntegrable_of_Icc zero_le_one).1
  rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le zero_le_one]
  apply integral_mono_ae hi hj
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have hw : 0 ≤ (1 - t) ^ n := pow_nonneg (sub_nonneg.mpr ht.2) _
  have hy : b + t * (a - b) ∈ Icc a b := by
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr ht.2),
      mul_nonneg (sub_nonneg.mpr hab) ht.1.le]
  simp only [abs_mul, abs_of_nonneg hw, integral_const_mul]
  exact (mul_le_mul_of_nonneg_left (hD _ hy) hw).trans_eq (by ring)

/-- L1 Taylor bound with the sharp factorial remainder coefficient. -/
theorem integral_abs_firstSmooth_le_taylor (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (n : ℕ) {a b D : ℝ} (ha : 0 < a) (hab : a ≤ b) (hD0 : 0 ≤ D)
    (hD : ∀ y ∈ Icc a b, (∫ x, |higherSmooth μ (n + 2) y x|) ≤ D / y ^ (n + 2)) :
    (∫ x, |firstSmooth μ a x|) ≤
      (∑ j ∈ Finset.range (n + 1), (b - a) ^ j / (j.factorial : ℝ) *
        ∫ x, |higherSmooth μ (j + 1) b x|) + D / ((n + 1).factorial * a) := by
  have hb := ha.trans_le hab
  have hi := integrable_varianceTaylor_product μ n (n + 2) ha hab
  have h := integral_abs_finite_expansion_le (Finset.range (n + 1))
    (fun j ↦ (a - b) ^ j / (j.factorial : ℝ)) (fun j ↦ higherSmooth μ (j + 1) b)
    (fun j _ ↦ integrable_higherSmooth μ (j + 1) hb)
    ((a - b) ^ (n + 1) / (n.factorial : ℝ)) hi
  have habs (j m : ℕ) : |(a - b) ^ j / (m.factorial : ℝ)| =
      (b - a) ^ j / (m.factorial : ℝ) := by
    rw [abs_div, abs_pow, abs_of_nonpos (sub_nonpos.mpr hab),
      abs_of_nonneg (Nat.cast_nonneg m.factorial : (0 : ℝ) ≤ (m.factorial : ℝ))]
    congr 2
    ring
  simp only [habs] at h
  have he (x : ℝ) : firstSmooth μ a x =
      (∑ j ∈ Finset.range (n + 1), (a - b) ^ j / (j.factorial : ℝ) * higherSmooth μ (j + 1) b x) +
      (a - b) ^ (n + 1) / (n.factorial : ℝ) * ∫ t in Ioc (0 : ℝ) 1,
        (1 - t) ^ n * higherSmooth μ (n + 2) (b + t * (a - b)) x := by
    rw [firstSmooth_taylor_variance μ n ha hab x, intervalIntegral.integral_of_le zero_le_one]
  simp_rw [← he] at h
  apply h.trans
  apply add_le_add le_rfl
  apply (mul_le_mul_of_nonneg_left (integral_varianceTaylor_product_le μ n ha hab hD)
    (by positivity : 0 ≤ (b - a) ^ (n + 1) / (n.factorial : ℝ))).trans
  have hw := mul_le_mul_of_nonneg_left (weighted_varianceTaylor_integral_le n ha hab)
    (div_nonneg hD0 (Nat.cast_nonneg n.factorial))
  convert hw using 1
  · ring
  · rw [Nat.factorial_succ, Nat.cast_mul]
    ring

end LpSelfSimilar.Gaussian
