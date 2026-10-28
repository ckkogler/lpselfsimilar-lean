module

public import LpSelfSimilar.Analysis.ThreeFactorHolder

@[expose] public section

/-!
The weighted factorization used in Young's convolution inequality. Every
exponent is nonnegative, so the identity also holds at zero and infinity.
-/

open MeasureTheory
open scoped ENNReal

namespace LpSelfSimilar

lemma young_power_factorization (a b : ℝ≥0∞) {p q u v w : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hp : p * (u + v) = 1) (hq : q * (u + w) = 1) :
    (a ^ p * b ^ q) ^ u * (a ^ p) ^ v * (b ^ q) ^ w = a * b := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ hu]
  calc
    _ = ((a ^ p) ^ u * (a ^ p) ^ v) * ((b ^ q) ^ u * (b ^ q) ^ w) := by ac_rfl
    _ = (a ^ p) ^ (u + v) * (b ^ q) ^ (u + w) := by
      rw [ENNReal.rpow_add_of_nonneg _ _ hu hv, ENNReal.rpow_add_of_nonneg _ _ hu hw]
    _ = a ^ (p * (u + v)) * b ^ (q * (u + w)) := by
      rw [ENNReal.rpow_mul, ENNReal.rpow_mul]
    _ = _ := by rw [hp, hq, ENNReal.rpow_one, ENNReal.rpow_one]

lemma young_weight_bounds {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hpr : p ≤ r) (hqr : q ≤ r) (hs : 1 / p + 1 / q = 1 + 1 / r) :
    0 ≤ 1 / r ∧ 0 ≤ 1 / p - 1 / r ∧ 0 ≤ 1 / q - 1 / r ∧
      1 / r + (1 / p - 1 / r) + (1 / q - 1 / r) = 1 ∧
      p * (1 / r + (1 / p - 1 / r)) = 1 ∧
      q * (1 / r + (1 / q - 1 / r)) = 1 := by
  have h1 := one_div_le_one_div_of_le hp hpr
  have h2 := one_div_le_one_div_of_le hq hqr
  refine ⟨by positivity, by linarith, by linarith, by linarith, ?_, ?_⟩ <;> field_simp <;> ring

/-- Hölder gives the pointwise Young bound before integration in the output variable. -/
theorem lintegral_mul_young_bound {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hpr : p ≤ r) (hqr : q ≤ r) (hs : 1 / p + 1 / q = 1 + 1 / r) :
    (∫⁻ x, f x * g x ∂μ) ^ r ≤
      (∫⁻ x, f x ^ p * g x ^ q ∂μ) *
        ((∫⁻ x, f x ^ p ∂μ) ^ (1 / p - 1 / r) *
          (∫⁻ x, g x ^ q ∂μ) ^ (1 / q - 1 / r)) ^ r := by
  obtain ⟨hu, hv, hw, hsum, hpw, hqw⟩ := young_weight_bounds hp hq hr hpr hqr hs
  have h := lintegral_three_weighted_powers_le ((hf.pow_const p).mul (hg.pow_const q))
    (hf.pow_const p) (hg.pow_const q) hu hv hw hsum
  simp only [Pi.mul_apply] at h
  simp only [young_power_factorization _ _ hu hv hw hpw hqw] at h
  have hpow := ENNReal.rpow_le_rpow h hr.le
  have he : ((∫⁻ x, f x ^ p * g x ^ q ∂μ) ^ (1 / r) *
      (∫⁻ x, f x ^ p ∂μ) ^ (1 / p - 1 / r) *
      (∫⁻ x, g x ^ q ∂μ) ^ (1 / q - 1 / r)) ^ r =
      (∫⁻ x, f x ^ p * g x ^ q ∂μ) *
        ((∫⁻ x, f x ^ p ∂μ) ^ (1 / p - 1 / r) *
          (∫⁻ x, g x ^ q ∂μ) ^ (1 / q - 1 / r)) ^ r := by
    rw [mul_assoc, ENNReal.mul_rpow_of_nonneg _ _ hr.le, ← ENNReal.rpow_mul]
    simp [hr.ne']
  exact hpow.trans_eq he

end LpSelfSimilar
