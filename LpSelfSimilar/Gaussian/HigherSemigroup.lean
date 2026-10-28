module

public import LpSelfSimilar.Gaussian.HigherSmoothing
public import LpSelfSimilar.Gaussian.Semigroup
public import LpSelfSimilar.Analysis.FunctionConvolution

@[expose] public section

/-!
Convolution identities for genuine higher Gaussian derivatives. Gaussian
variance addition is differentiated under the integral, with explicit uniform
bounds. Derivative orders and variances both add under function convolution.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real Filter Set
open scoped Topology NNReal

namespace LpSelfSimilar.Gaussian

lemma higherSmooth_gaussian (v : ℝ≥0) (k : ℕ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    higherSmooth (gaussianReal 0 v) k y x = higherKernel k ((v : ℝ) + y) x := by
  induction k generalizing y with
  | zero => rw [higherSmooth_zero, higherKernel_zero, smooth_gaussian v hy]
  | succ k ih =>
    have he : (fun z ↦ higherSmooth (gaussianReal 0 v) k z x) =ᶠ[𝓝 y]
        (fun z ↦ higherKernel k ((v : ℝ) + z) x) := by
      filter_upwards [Ioi_mem_nhds hy] with z hz
      exact ih hz
    have hd := (hasDerivAt_higherKernel_variance k (by positivity : 0 < (v : ℝ) + y) x).comp y
      (h := fun z : ℝ ↦ (v : ℝ) + z) ((hasDerivAt_id y).const_add (v : ℝ))
    have hd' : HasDerivAt (fun z ↦ higherKernel k ((v : ℝ) + z) x)
        (higherKernel (k + 1) ((v : ℝ) + y) x) y := by
      convert hd using 1 <;> first | rfl | simp only [mul_one]
    exact (hasDerivAt_higherSmooth_variance (gaussianReal 0 v) k hy x).unique
      (hd'.congr_of_eventuallyEq he)

lemma averageTranslate_gaussian_eq_functionConvolution {y : ℝ} (hy : 0 < y)
    (f : ℝ → ℝ) (x : ℝ) :
    averageTranslate (gaussianReal 0 (NNReal.mk y hy.le)) f x =
      functionConvolution (kernel y) f x := by
  have hn : NNReal.mk y hy.le ≠ 0 := by
    intro h
    have := congrArg (fun v : ℝ≥0 ↦ (v : ℝ)) h
    exact hy.ne' this
  unfold averageTranslate functionConvolution
  rw [integral_gaussianReal_eq_integral_smul hn]
  simp only [smul_eq_mul, ← kernel_eq_gaussianPDFReal hy.le]

lemma hasDerivAt_functionConvolution_higherKernel {f : ℝ → ℝ}
    (hfc : Continuous f) (hf : Integrable f volume) (k : ℕ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    HasDerivAt (fun t ↦ functionConvolution f (higherKernel k t) x)
      (functionConvolution f (higherKernel (k + 1) y) x) y := by
  have ha : 0 < y / 2 := by positivity
  obtain ⟨C, _, hb⟩ := exists_uniform_bound_higherKernel (k + 1) ha
  obtain ⟨D, _, hD⟩ := exists_uniform_bound_higherKernel k hy
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := fun t z ↦ f z * higherKernel k t (x - z))
    (F' := fun t z ↦ f z * higherKernel (k + 1) t (x - z)) (bound := fun z ↦ |f z| * C)
    (Ioi_mem_nhds (by linarith : y / 2 < y))
    (Eventually.of_forall (fun _ ↦ by fun_prop))
    (integrable_functionConvolution_integrand hfc hf (continuous_higherKernel_space k y) (hD y le_rfl) x)
    (by fun_prop)
    (ae_of_all _ (fun z t ht ↦ by
      simpa only [Real.norm_eq_abs, abs_mul] using
        mul_le_mul_of_nonneg_left (hb t ht.le (x - z)) (abs_nonneg (f z))))
    (hf.abs.mul_const C)
    (ae_of_all _ (fun z t ht ↦ (hasDerivAt_higherKernel_variance k (ha.trans ht) (x - z)).const_mul (f z)))
  exact hd.2

/-- Orders and variances add under convolution of higher Gaussian kernels. -/
theorem functionConvolution_higherKernel (k l : ℕ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    functionConvolution (higherKernel k a) (higherKernel l b) x =
      higherKernel (k + l) (a + b) x := by
  induction l generalizing b with
  | zero =>
    simp only [Nat.add_zero]
    have h0 : higherKernel 0 b = kernel b := funext (higherKernel_zero b)
    rw [h0, functionConvolution_comm, ← averageTranslate_gaussian_eq_functionConvolution hb]
    change higherSmooth (gaussianReal 0 (NNReal.mk b hb.le)) k a x = _
    rw [higherSmooth_gaussian _ k ha, NNReal.coe_mk, add_comm b a]
  | succ l ih =>
    have he : (fun t ↦ functionConvolution (higherKernel k a) (higherKernel l t) x) =ᶠ[𝓝 b]
        (fun t ↦ higherKernel (k + l) (a + t) x) := by
      filter_upwards [Ioi_mem_nhds hb] with t ht
      exact ih ht
    have hd := (hasDerivAt_higherKernel_variance (k + l) (add_pos ha hb) x).comp b
      (h := fun t : ℝ ↦ a + t) ((hasDerivAt_id b).const_add a)
    have hd' : HasDerivAt (fun t ↦ higherKernel (k + l) (a + t) x)
        (higherKernel (k + (l + 1)) (a + b) x) b := by
      convert hd using 1 <;> first | rfl | simp only [mul_one, Nat.add_assoc]
    exact (hasDerivAt_functionConvolution_higherKernel
      (continuous_higherKernel_space k a) (integrable_higherKernel k ha) l hb x).unique
      (hd'.congr_of_eventuallyEq he)

end LpSelfSimilar.Gaussian
