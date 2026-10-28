module

public import LpSelfSimilar.Gaussian.HigherKernelBounds
public import LpSelfSimilar.Gaussian.Smoothing
public import LpSelfSimilar.Gaussian.Detail
public import LpSelfSimilar.Analysis.ConvolutionAction

@[expose] public section

/-!
Convolution of finite measures with all Gaussian variance derivatives.
Uniform kernel bounds justify differentiation under the measure. The resulting
functions equal the actual iterated variance derivatives of Gaussian smoothing.
-/

open MeasureTheory MeasureTheory.Measure Real Polynomial Filter Set
open scoped Topology

namespace LpSelfSimilar.Gaussian

noncomputable def higherSmooth (μ : Measure ℝ) (k : ℕ) (y x : ℝ) : ℝ :=
  averageTranslate μ (higherKernel k y) x

@[fun_prop] lemma measurable_higherKernel_joint (k : ℕ) :
    Measurable (fun p : ℝ × ℝ ↦ higherKernel k p.1 p.2) := by
  unfold higherKernel
  fun_prop

@[fun_prop] lemma measurable_higherSmooth_joint (μ : Measure ℝ) [SFinite μ] (k : ℕ) :
    Measurable (fun p : ℝ × ℝ ↦ higherSmooth μ k p.1 p.2) := by
  have h : StronglyMeasurable (fun p : (ℝ × ℝ) × ℝ ↦ higherKernel k p.1.1 (p.1.2 - p.2)) := by
    apply Measurable.stronglyMeasurable
    fun_prop
  exact h.integral_prod_right'.measurable

lemma integrable_higherKernel_translate (μ : Measure ℝ) [IsFiniteMeasure μ]
    (k : ℕ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    Integrable (fun z ↦ higherKernel k y (x - z)) μ := by
  obtain ⟨C, _, hb⟩ := exists_uniform_bound_higherKernel k hy
  exact integrable_translate_of_bounded μ (continuous_higherKernel_space k y) (hb y le_rfl) x

lemma hasDerivAt_higherSmooth_variance (μ : Measure ℝ) [IsFiniteMeasure μ]
    (k : ℕ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    HasDerivAt (fun t ↦ higherSmooth μ k t x) (higherSmooth μ (k + 1) y x) y := by
  have ha : 0 < y / 2 := by positivity
  obtain ⟨C, _, hb⟩ := exists_uniform_bound_higherKernel (k + 1) ha
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun t z ↦ higherKernel k t (x - z))
    (F' := fun t z ↦ higherKernel (k + 1) t (x - z)) (bound := fun _ ↦ C)
    (Ioi_mem_nhds (by linarith : y / 2 < y))
    (Eventually.of_forall (fun _ ↦ by fun_prop))
    (integrable_higherKernel_translate μ k hy x) (by fun_prop)
    (ae_of_all _ (fun z t ht ↦ by simpa only [Real.norm_eq_abs] using hb t ht.le (x - z)))
    (integrable_const _)
    (ae_of_all _ (fun z t ht ↦ hasDerivAt_higherKernel_variance k (ha.trans ht) (x - z)))
  exact hd.2

lemma higherSmooth_zero (μ : Measure ℝ) (y x : ℝ) : higherSmooth μ 0 y x = smooth μ y x := by
  unfold higherSmooth averageTranslate smooth
  simp_rw [higherKernel_zero]
  rfl

lemma higherKernel_one {y : ℝ} (hy : 0 < y) (x : ℝ) : higherKernel 1 y x = firstKernel y x := by
  have h := hasDerivAt_higherKernel_variance 0 hy x
  simp only [higherKernel_zero, zero_add] at h
  exact h.unique (hasDerivAt_kernel_variance hy x)

lemma higherSmooth_one (μ : Measure ℝ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    higherSmooth μ 1 y x = firstSmooth μ y x := by
  unfold higherSmooth firstSmooth averageTranslate
  simp_rw [higherKernel_one hy]

lemma higherSmooth_eq_iteratedDeriv (μ : Measure ℝ) [IsFiniteMeasure μ]
    (k : ℕ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    higherSmooth μ k y x = iteratedDeriv k (fun z ↦ smooth μ z x) y := by
  induction k generalizing y with
  | zero => simp only [higherSmooth_zero, iteratedDeriv_zero]
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have he : (fun z ↦ higherSmooth μ k z x) =ᶠ[𝓝 y]
        iteratedDeriv k (fun z ↦ smooth μ z x) := by
      filter_upwards [Ioi_mem_nhds hy] with z hz
      exact ih hz
    exact (hasDerivAt_higherSmooth_variance μ k hy x).deriv.symm.trans he.deriv_eq

lemma integrable_higherSmooth (μ : Measure ℝ) [IsFiniteMeasure μ] (k : ℕ)
    {y : ℝ} (hy : 0 < y) : Integrable (higherSmooth μ k y) volume :=
  integrable_averageTranslate μ (continuous_higherKernel_space k y) (integrable_higherKernel k hy)

lemma continuous_higherSmooth_space (μ : Measure ℝ) [IsFiniteMeasure μ] (k : ℕ)
    {y : ℝ} (hy : 0 < y) : Continuous (higherSmooth μ k y) := by
  obtain ⟨C, _, hb⟩ := exists_uniform_bound_higherKernel k hy
  exact continuous_averageTranslate_of_bounded μ (continuous_higherKernel_space k y) (hb y le_rfl)

/-- Higher detail as defined in Section 3, using the actual kth variance derivative. -/
noncomputable def higherDetail (μ : Measure ℝ) (k : ℕ) (r : ℝ) : ℝ :=
  r ^ (2 * k) * detailNormalization ^ k * ∫ x, |higherSmooth μ k ((k : ℝ) * r ^ 2) x|

lemma higherDetail_one (μ : Measure ℝ) {r : ℝ} (hr : 0 < r) : higherDetail μ 1 r = detail μ r := by
  unfold higherDetail detail
  norm_num only [Nat.cast_one, mul_one, one_mul, pow_one]
  simp_rw [higherSmooth_one μ (sq_pos_of_pos hr)]
  rfl

lemma higherDetail_nonneg (μ : Measure ℝ) (k : ℕ) (r : ℝ) : 0 ≤ higherDetail μ k r := by
  unfold higherDetail
  apply mul_nonneg _ (integral_nonneg (fun _ ↦ abs_nonneg _))
  rw [pow_mul]
  positivity [detailNormalization_pos]

end LpSelfSimilar.Gaussian
