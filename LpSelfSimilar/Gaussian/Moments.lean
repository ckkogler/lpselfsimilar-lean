module

public import LpSelfSimilar.Gaussian.DerivativeNorm

@[expose] public section

/-!
Gaussian second moments and a quantitative bound for the first derivative norm.
The moment is transferred from Mathlib's proved Gaussian variance formula;
this also proves that the variance derivative has integral zero.
-/

open MeasureTheory ProbabilityTheory Real

namespace LpSelfSimilar.Gaussian

lemma integrable_sq_mul_kernel {y : ℝ} (hy : 0 < y) :
    Integrable (fun x ↦ x ^ 2 * kernel y x) volume := by
  have h := ((integrable_firstKernel hy).const_mul (2 * y ^ 2)).add
    ((integrable_kernel hy.le).const_mul y)
  convert h using 1 <;> try rfl
  ext x
  simp only [Pi.add_apply, firstKernel]
  field_simp
  <;> ring

lemma integral_sq_mul_kernel {y : ℝ} (hy : 0 < y) :
    (∫ x, x ^ 2 * kernel y x) = y := by
  let v : NNReal := NNReal.mk y hy.le
  have hv : v ≠ 0 := by
    intro h
    exact hy.ne' (congrArg (fun z : NNReal ↦ (z : ℝ)) h)
  have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral (X := fun x : ℝ ↦ x) (by fun_prop), integral_id_gaussianReal] at h
  simp only [sub_zero] at h
  rw [integral_gaussianReal_eq_integral_smul hv] at h
  simpa only [v, smul_eq_mul, ← kernel_eq_gaussianPDFReal hy.le, mul_comm, NNReal.coe_mk] using h

lemma integral_firstKernel {y : ℝ} (hy : 0 < y) : (∫ x, firstKernel y x) = 0 := by
  have heq : firstKernel y = fun x ↦
      (x ^ 2 * kernel y x - y * kernel y x) / (2 * y ^ 2) := by
    ext x
    unfold firstKernel
    ring
  rw [heq, integral_div, integral_sub (integrable_sq_mul_kernel hy)
    ((integrable_kernel hy.le).const_mul y), integral_const_mul,
    integral_sq_mul_kernel hy, integral_kernel hy]
  ring

/-- The L1 norm at variance one is at most one, so the normalization `Q` is
at least one. This bound suffices for the constants in the integration argument. -/
lemma firstNorm_le_one : firstNorm ≤ 1 := by
  have h₁ := integrable_kernel (by norm_num : (0 : ℝ) ≤ 1)
  have h₂ := integrable_sq_mul_kernel (by norm_num : (0 : ℝ) < 1)
  calc
    firstNorm ≤ ∫ x, (x ^ 2 * kernel 1 x + kernel 1 x) / 2 := by
      apply integral_mono (integrable_firstKernel (by norm_num)).abs ((h₂.add h₁).div_const 2)
      intro x
      simp only [Pi.add_apply]
      have hk := (kernel_pos (by norm_num : (0 : ℝ) < 1) x).le
      simp only [firstKernel, one_pow, mul_one, abs_mul, abs_of_nonneg hk, abs_div,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have ha : |x ^ 2 - 1| ≤ x ^ 2 + 1 := by
        rw [abs_le]
        constructor <;> nlinarith [sq_nonneg x]
      have hm := mul_le_mul_of_nonneg_right ha hk
      nlinarith
    _ = 1 := by
      rw [integral_div, integral_add h₂ h₁, integral_sq_mul_kernel (by norm_num),
        integral_kernel (by norm_num)]
      norm_num

lemma one_le_detailNormalization : 1 ≤ detailNormalization := by
  exact (one_le_inv₀ firstNorm_pos).mpr firstNorm_le_one

end LpSelfSimilar.Gaussian
