module

public import LpSelfSimilar.Gaussian.Kernel

@[expose] public section

/-!
Uniform spatial bounds for the Gaussian kernel and its first variance derivative.
They provide integrable dominating functions against arbitrary finite measures,
which justifies differentiating Gaussian convolutions in the variance.
-/

open Real

namespace LpSelfSimilar.Gaussian

lemma sq_mul_kernel_le {y : ℝ} (hy : 0 < y) (x : ℝ) :
    x ^ 2 * kernel y x ≤ 2 * y * (Real.sqrt (2 * Real.pi * y))⁻¹ := by
  have he : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have h := mul_le_mul_of_nonneg_left
    ((Real.mul_exp_neg_le_exp_neg_one (x ^ 2 / (2 * y))).trans he)
    (by positivity : 0 ≤ 2 * y)
  have heq : 2 * y * (x ^ 2 / (2 * y) * Real.exp (-(x ^ 2 / (2 * y)))) =
      x ^ 2 * Real.exp (-x ^ 2 / (2 * y)) := by
    rw [neg_div]
    field_simp
  rw [heq, mul_one] at h
  have hp : 0 ≤ (Real.sqrt (2 * Real.pi * y))⁻¹ := by positivity
  simpa only [kernel, mul_assoc, mul_comm, mul_left_comm] using
    mul_le_mul_of_nonneg_right h hp

lemma abs_firstKernel_le {y : ℝ} (hy : 0 < y) (x : ℝ) :
    |firstKernel y x| ≤ (3 / (2 * y)) * (Real.sqrt (2 * Real.pi * y))⁻¹ := by
  have hk := (kernel_pos hy x).le
  have hnum : |x ^ 2 - y| ≤ x ^ 2 + y := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg x]
  calc
    |firstKernel y x| = |x ^ 2 - y| / (2 * y ^ 2) * kernel y x := by
      rw [firstKernel, abs_mul, abs_div, abs_of_nonneg hk, abs_of_pos (by positivity : 0 < 2 * y ^ 2)]
    _ ≤ (x ^ 2 + y) / (2 * y ^ 2) * kernel y x := by gcongr
    _ = (x ^ 2 * kernel y x + y * kernel y x) / (2 * y ^ 2) := by ring
    _ ≤ (2 * y * (Real.sqrt (2 * Real.pi * y))⁻¹ +
        y * (Real.sqrt (2 * Real.pi * y))⁻¹) / (2 * y ^ 2) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact add_le_add (sq_mul_kernel_le hy x)
        (mul_le_mul_of_nonneg_left (kernel_le_peak hy x) hy.le)
    _ = _ := by field_simp; ring

lemma abs_firstKernel_le_of_le {a y : ℝ} (ha : 0 < a) (hay : a ≤ y) (x : ℝ) :
    |firstKernel y x| ≤ (3 / (2 * a)) * (Real.sqrt (2 * Real.pi * a))⁻¹ := by
  have hy := ha.trans_le hay
  apply (abs_firstKernel_le hy x).trans
  apply mul_le_mul
  · exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  · apply inv_anti₀ (by positivity)
    apply Real.sqrt_le_sqrt
    nlinarith [Real.pi_pos]
  · positivity
  · positivity

lemma continuousAt_kernel {p : ℝ × ℝ} (hp : 0 < p.1) :
    ContinuousAt (fun q : ℝ × ℝ ↦ kernel q.1 q.2) p := by
  unfold kernel
  fun_prop (disch := positivity)

lemma continuousAt_firstKernel {p : ℝ × ℝ} (hp : 0 < p.1) :
    ContinuousAt (fun q : ℝ × ℝ ↦ firstKernel q.1 q.2) p := by
  have hk := continuousAt_kernel hp
  unfold firstKernel
  have hpref : ContinuousAt (fun q : ℝ × ℝ ↦ (q.2 ^ 2 - q.1) / (2 * q.1 ^ 2)) p := by
    fun_prop (disch := positivity)
  exact hpref.mul hk

end LpSelfSimilar.Gaussian
