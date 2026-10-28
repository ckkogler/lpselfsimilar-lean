module

public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import LpSelfSimilar.Analysis.YoungFactorization
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
Tonelli's identity and Young's inequality for nonnegative kernels on the real
line. This extended-integral formulation handles arbitrary measurable kernels,
including their null exceptional sets, before selecting real representatives.
-/

open MeasureTheory
open scoped ENNReal

namespace LpSelfSimilar

lemma lintegral_convolution_product {f g : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, ∫⁻ z, f z * g (x - z)) = (∫⁻ z, f z) * ∫⁻ x, g x := by
  rw [lintegral_lintegral_swap (by fun_prop)]
  have hinner (z : ℝ) : (∫⁻ x, f z * g (x - z)) = f z * ∫⁻ x, g x := by
    rw [lintegral_const_mul (f z) (f := fun x ↦ g (x - z)) (by fun_prop),
      lintegral_sub_right_eq_self]
  simp_rw [hinner]
  exact lintegral_mul_const _ hf

/-- The integrated Young bound; no sharp norm constant is needed downstream. -/
theorem lintegral_convolution_rpow_le {f g : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hpr : p ≤ r) (hqr : q ≤ r) (hs : 1 / p + 1 / q = 1 + 1 / r) :
    (∫⁻ x, (∫⁻ z, f z * g (x - z)) ^ r) ≤
      ((∫⁻ z, f z ^ p) * ∫⁻ z, g z ^ q) *
        ((∫⁻ z, f z ^ p) ^ (1 / p - 1 / r) *
          (∫⁻ z, g z ^ q) ^ (1 / q - 1 / r)) ^ r := by
  calc
    _ ≤ ∫⁻ x, (∫⁻ z, f z ^ p * g (x - z) ^ q) *
        ((∫⁻ z, f z ^ p) ^ (1 / p - 1 / r) *
          (∫⁻ z, g z ^ q) ^ (1 / q - 1 / r)) ^ r := by
      apply lintegral_mono
      intro x
      have h := lintegral_mul_young_bound (μ := volume) (g := fun z ↦ g (x - z)) hf.aemeasurable
        (by fun_prop) hp hq hr hpr hqr hs
      have he := lintegral_sub_left_eq_self (μ := volume) (fun z ↦ g z ^ q) x
      simpa only [he] using h
    _ = _ := by
      rw [lintegral_mul_const _ (by fun_prop)]
      rw [lintegral_convolution_product (hf.pow_const p) (hg.pow_const q)]

/-- Finite input power integrals give a finite output power integral. -/
theorem lintegral_convolution_rpow_lt_top {f g : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hpr : p ≤ r) (hqr : q ≤ r) (hs : 1 / p + 1 / q = 1 + 1 / r)
    (hfp : (∫⁻ z, f z ^ p) < ∞) (hgq : (∫⁻ z, g z ^ q) < ∞) :
    (∫⁻ x, (∫⁻ z, f z * g (x - z)) ^ r) < ∞ := by
  obtain ⟨_, hv, hw, _⟩ := young_weight_bounds hp hq hr hpr hqr hs
  apply (lintegral_convolution_rpow_le hf hg hp hq hr hpr hqr hs).trans_lt
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hfp hgq)
    (ENNReal.rpow_lt_top_of_nonneg hr.le (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg hv hfp.ne)
      (ENNReal.rpow_lt_top_of_nonneg hw hgq.ne)).ne)

end LpSelfSimilar
