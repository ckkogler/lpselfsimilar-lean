module

public import LpSelfSimilar.Analysis.WeightedLogMinimum
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

/-!
# The supporting inequality at a logarithmic minimizer

Moving towards any feasible nonnegative vector gives a one-sided derivative
inequality. Only a half-segment is used, so every coordinate with nonzero weight
remains strictly positive, even if the endpoint has zero coordinates. A zero
weight contributes a constant zero function and needs no logarithmic derivative.
-/

open Set
open scoped BigOperators

namespace LpSelfSimilar

/-- First-order support inequality at a weighted logarithmic minimum. -/
theorem weighted_log_minimizer_support_bound {ι : Type*} [Fintype ι]
    (p x : ι → ℝ) (K : Set (ι → ℝ)) (hK : Convex ℝ K)
    (hK0 : ∀ z ∈ K, ∀ i, 0 ≤ z i) (hxK : x ∈ K)
    (hx0 : ∀ i, p i ≠ 0 → 0 < x i)
    (hmin : ∀ y ∈ K, (∀ i, p i ≠ 0 → 0 < y i) →
      (∑ i, p i * (-Real.log (x i))) ≤ ∑ i, p i * (-Real.log (y i)))
    {z : ι → ℝ} (hzK : z ∈ K) :
    (∑ i, p i * z i / x i) ≤ ∑ i, p i := by
  classical
  let f : ℝ → ℝ := fun t ↦ ∑ i, p i * Real.log (x i + t * (z i - x i))
  have hmax : IsMaxOn f (Icc 0 (1 / 2)) 0 := by
    intro t ht
    have hmem : (fun i ↦ x i + t * (z i - x i)) ∈ K := by
      convert hK hxK hzK (show 0 ≤ 1 - t by linarith [ht.2]) ht.1
        (show (1 - t) + t = 1 by ring) using 1
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hpos : ∀ i, p i ≠ 0 → 0 < x i + t * (z i - x i) := by
      intro i hpi
      have hx := hx0 i hpi
      have hz := hK0 z hzK i
      have h1 : 0 < 1 - t := by linarith [ht.2]
      have hfirst := mul_pos h1 hx
      have hsecond := mul_nonneg ht.1 hz
      nlinarith
    have h := hmin _ hmem hpos
    simp only [mul_neg, Finset.sum_neg_distrib] at h
    change f t ≤ f 0
    simpa only [f, zero_mul, add_zero] using neg_le_neg_iff.mp h
  have hd : HasDerivAt f (∑ i, p i * (z i - x i) / x i) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    by_cases hpi : p i = 0
    · simpa [hpi] using (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    · have h := (((hasDerivAt_id (0 : ℝ)).mul_const (z i - x i)).const_add (x i)).log
        (by simpa only [id_eq, zero_mul, add_zero] using (hx0 i hpi).ne')
      simpa [id_eq, mul_div_assoc] using h.const_mul (p i)
  have htangent : (1 / 2 : ℝ) ∈ posTangentConeAt (Icc 0 (1 / 2)) (0 : ℝ) := by
    apply mem_posTangentConeAt_of_segment_subset
    rw [zero_add, segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hderiv := hmax.localize.hasFDerivWithinAt_nonpos hd.hasFDerivAt.hasFDerivWithinAt htangent
  change (1 / 2 : ℝ) * (∑ i, p i * (z i - x i) / x i) ≤ 0 at hderiv
  have he : (∑ i, p i * (z i - x i) / x i) = (∑ i, p i * z i / x i) - ∑ i, p i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hpi : p i = 0
    · simp [hpi]
    · field_simp [(hx0 i hpi).ne']
  rw [he] at hderiv
  linarith

end LpSelfSimilar
