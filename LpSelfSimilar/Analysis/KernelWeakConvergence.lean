module

public import LpSelfSimilar.Analysis.KernelTestIdentity
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-!
# Weak approximation by signed mass-one kernels

Two dominated convergence arguments identify the weak limit. The inner
integrand is dominated by norm(test)*norm(kernel); the outer finite-measure
integral is dominated by norm(test)*norm_1(kernel). Only kernel integrability
and mass one are used; the kernel need not be nonnegative.
-/

open MeasureTheory MeasureTheory.Measure Filter
open scoped Topology BoundedContinuousFunction

namespace LpSelfSimilar.Analysis

/-- A bounded test against any translated, scaled argument has a uniform kernel L1 bound. -/
theorem norm_integral_bounded_test_kernel_le (v : ℝ →ᵇ ℝ) {k : ℝ → ℝ}
    (hi : Integrable k) (r y : ℝ) :
    ‖∫ z, v (y + r*z) * k z‖ ≤ ‖v‖ * ∫ z, ‖k z‖ := by
  apply (norm_integral_le_of_norm_le (hi.norm.const_mul ‖v‖) ?_).trans_eq
    (integral_const_mul ‖v‖ (fun z => ‖k z‖))
  exact ae_of_all _ (fun z => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (v.norm_coe_le_norm _) (norm_nonneg _))

/-- The actual convolution by a continuous integrable signed mass-one kernel converges weakly. -/
theorem tendsto_integral_bounded_test_convolution_rescaledKernel
    (μ : Measure ℝ) [IsFiniteMeasure μ] (v : ℝ →ᵇ ℝ)
    {k : ℝ → ℝ} (hc : Continuous k) (hi : Integrable k) (hmass : (∫ z, k z) = 1)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, v x * measureFunctionConvolution μ (rescaledKernel (r n) k) x)
      atTop (𝓝 (∫ x, v x ∂μ)) := by
  simp_rw [integral_bounded_test_convolution_rescaledKernel μ v hc hi (hr _)]
  have hmeas (n : ℕ) : Measurable (fun p : ℝ × ℝ => v (p.1 + r n * p.2) * k p.2) := by
    fun_prop
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖v‖ * ∫ z, ‖k z‖)
  · intro n
    exact ((hmeas n).stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable
  · exact integrable_const _
  · exact fun n => ae_of_all _ (fun y => norm_integral_bounded_test_kernel_le v hi (r n) y)
  · apply ae_of_all
    intro y
    have ht : Tendsto (fun n => ∫ z, v (y + r n*z) * k z) atTop
        (𝓝 (∫ z, v y * k z)) := by
      apply tendsto_integral_of_dominated_convergence (fun z => ‖v‖ * ‖k z‖)
      · intro n
        fun_prop
      · exact hi.norm.const_mul ‖v‖
      · intro n
        exact ae_of_all _ (fun z => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (v.norm_coe_le_norm _) (norm_nonneg _))
      · apply ae_of_all
        intro z
        have harg : Tendsto (fun n => y + r n*z) atTop (𝓝 y) := by
          simpa only [zero_mul, add_zero] using (hrlim.mul_const z).const_add y
        exact (v.continuous.continuousAt.tendsto.comp harg).mul_const (k z)
    simpa only [integral_const_mul, hmass, mul_one] using ht

end LpSelfSimilar.Analysis
