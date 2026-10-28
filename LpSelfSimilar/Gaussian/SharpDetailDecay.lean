module

public import LpSelfSimilar.Gaussian.DetailDecay
public import LpSelfSimilar.Analysis.SharpDetailDecayScalars

@[expose] public section

/-!
Higher Gaussian detail implies inverse-square logarithmic decay from the precise
scale 4 R_0 in revised Lemma 3.4. Finite-variance Taylor recovery supplies the
comparison, so no infinite-variance boundary condition is left as an assumption.
-/

open MeasureTheory MeasureTheory.Measure Real Set

namespace LpSelfSimilar.Gaussian

/-- The inverse-square estimate used in the integrating-detail lemma. The
threshold is exactly the paper's `4*R₀`. -/
theorem detail_exp_neg_le_inverse_sq_sharp (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {R₀ : ℝ} (hR₀ : 100 ≤ R₀)
    (h : ∀ S : ℝ, R₀ ≤ S → ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ 10 * log S →
      higherDetail μ k (exp (-S)) ≤ (1 / 100 : ℝ) ^ k)
    {R : ℝ} (hR : 4 * R₀ ≤ R) :
    detail μ (exp (-R)) ≤ 1 / R ^ 2 := by
  have hRlarge : 400 ≤ R := by linarith
  have hR0 : 0 < R := by linarith
  let k : ℕ := ⌈2 * log R⌉₊
  have hk := detail_order_bounds (by linarith : 10 ≤ R)
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have ha : 0 < exp (-(2 * R)) := exp_pos _
  have hab : exp (-(2 * R)) ≤ exp (-R) := exp_le_exp.mpr (by linarith)
  have hh (y : ℝ) (hy : y ∈ Icc (exp (-(2 * R))) (exp (-R))) :
      higherDetail μ k (sqrt (y / (k : ℝ))) ≤ (1 / 100 : ℝ) ^ k := by
    have hy0 : 0 < y := ha.trans_le hy.1
    have hr : 0 < sqrt (y / (k : ℝ)) := by positivity
    have hyr : y / (k : ℝ) ≤ exp (-R) := by
      apply (div_le_iff₀ (by linarith : (0 : ℝ) < k)).mpr
      exact hy.2.trans (le_mul_of_one_le_right (exp_pos _).le hkR)
    have hsmall : sqrt (y / (k : ℝ)) ≤ exp (-(R / 2)) := by
      apply (sqrt_le_iff).mpr
      refine ⟨(exp_pos _).le, ?_⟩
      have he : (exp (-(R / 2))) ^ 2 = exp (-R) := by
        rw [← exp_nat_mul]
        congr 1
        norm_num <;> ring
      rwa [he]
    have hS : R / 2 ≤ -log (sqrt (y / (k : ℝ))) := by
      have hm := log_le_log hr hsmall
      rw [log_exp] at hm
      linarith
    have hh := h (-log (sqrt (y / (k : ℝ)))) (by linarith)
      k (by omega) (detail_order_le_ten_log (by linarith : 10 ≤ R) hS)
    simpa only [neg_neg, exp_log hr] using hh
  have hc := detail_le_of_higherDetail_order μ hk.1 ha hab (by positivity) hh
  have hsqrt : sqrt (exp (-(2 * R))) = exp (-R) := by
    rw [Real.sqrt_eq_iff_eq_sq (exp_pos _).le (exp_pos _).le]
    rw [← exp_nat_mul]
    congr 1
    norm_num
  have hquot : exp (-(2 * R)) / exp (-R) = exp (-R) := by
    rw [← exp_sub]
    congr 1
    ring
  rw [hsqrt, hquot] at hc
  exact hc.trans (detail_decay_numerical_sharp hRlarge)


end LpSelfSimilar.Gaussian
