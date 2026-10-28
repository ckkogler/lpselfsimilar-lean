module

public import LpSelfSimilar.Gaussian.UniformBounds
public import LpSelfSimilar.Analysis.MeasureConvolution
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

/-!
Gaussian smoothing of arbitrary finite measures. The derivative in the variance
is proved by dominated differentiation; the domination is uniform in space and
in every variance interval bounded away from zero.
-/

open MeasureTheory MeasureTheory.Measure Filter Set Real
open scoped Topology

namespace LpSelfSimilar.Gaussian

/-- Convolution of a measure with the centered Gaussian of variance `y`. -/
noncomputable def smooth (μ : Measure ℝ) (y x : ℝ) : ℝ :=
  averageTranslate μ (kernel y) x

/-- Convolution with the first variance derivative of the Gaussian. -/
noncomputable def firstSmooth (μ : Measure ℝ) (y x : ℝ) : ℝ :=
  averageTranslate μ (firstKernel y) x

@[fun_prop] lemma measurable_kernel_joint : Measurable (fun p : ℝ × ℝ ↦ kernel p.1 p.2) := by
  unfold kernel
  fun_prop

@[fun_prop] lemma measurable_firstKernel_joint :
    Measurable (fun p : ℝ × ℝ ↦ firstKernel p.1 p.2) := by
  unfold firstKernel
  fun_prop

@[fun_prop] lemma measurable_firstSmooth_joint (μ : Measure ℝ) [SFinite μ] :
    Measurable (fun p : ℝ × ℝ ↦ firstSmooth μ p.1 p.2) := by
  have h : StronglyMeasurable
      (fun p : (ℝ × ℝ) × ℝ ↦ firstKernel p.1.1 (p.1.2 - p.2)) := by
    apply Measurable.stronglyMeasurable
    fun_prop
  exact h.integral_prod_right'.measurable

lemma integrable_kernel_translate (μ : Measure ℝ) [IsFiniteMeasure μ]
    {y : ℝ} (hy : 0 < y) (x : ℝ) : Integrable (fun z ↦ kernel y (x - z)) μ := by
  apply (integrable_const ((Real.sqrt (2 * Real.pi * y))⁻¹)).mono' (by fun_prop)
  exact ae_of_all _ (fun z ↦ by
    rw [Real.norm_eq_abs, abs_of_pos (kernel_pos hy _)]
    exact kernel_le_peak hy _)

lemma integrable_firstKernel_translate (μ : Measure ℝ) [IsFiniteMeasure μ]
    {y : ℝ} (hy : 0 < y) (x : ℝ) : Integrable (fun z ↦ firstKernel y (x - z)) μ := by
  apply (integrable_const ((3 / (2 * y)) * (Real.sqrt (2 * Real.pi * y))⁻¹)).mono'
    (by fun_prop)
  exact ae_of_all _ (fun z ↦ by simpa only [Real.norm_eq_abs] using abs_firstKernel_le hy (x - z))

lemma hasDerivAt_smooth_variance (μ : Measure ℝ) [IsFiniteMeasure μ]
    {y : ℝ} (hy : 0 < y) (x : ℝ) :
    HasDerivAt (fun t ↦ smooth μ t x) (firstSmooth μ y x) y := by
  have ha : 0 < y / 2 := by positivity
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun t z ↦ kernel t (x - z))
    (F' := fun t z ↦ firstKernel t (x - z))
    (bound := fun _ ↦ (3 / (2 * (y / 2))) * (Real.sqrt (2 * Real.pi * (y / 2)))⁻¹)
    (Ioi_mem_nhds (by linarith : y / 2 < y))
    (Eventually.of_forall (fun _ ↦ by fun_prop))
    (integrable_kernel_translate μ hy x) (by fun_prop)
    (ae_of_all _ (fun z t ht ↦ by
      simpa only [Real.norm_eq_abs] using abs_firstKernel_le_of_le ha ht.le (x - z)))
    (integrable_const _)
    (ae_of_all _ (fun z t ht ↦ hasDerivAt_kernel_variance (ha.trans ht) (x - z)))
  exact hd.2

lemma continuousAt_firstSmooth (μ : Measure ℝ) [IsFiniteMeasure μ]
    {p : ℝ × ℝ} (hp : 0 < p.1) :
    ContinuousAt (fun q : ℝ × ℝ ↦ firstSmooth μ q.1 q.2) p := by
  have ha : 0 < p.1 / 2 := by positivity
  apply continuousAt_of_dominated
    (bound := fun _ ↦ (3 / (2 * (p.1 / 2))) * (Real.sqrt (2 * Real.pi * (p.1 / 2)))⁻¹)
  · exact Eventually.of_forall (fun _ ↦ by fun_prop)
  · filter_upwards [continuous_fst.continuousAt.eventually
      (Ioi_mem_nhds (by linarith : p.1 / 2 < p.1))] with q hq
    exact ae_of_all _ (fun z ↦ by
      simpa only [Real.norm_eq_abs] using abs_firstKernel_le_of_le ha hq.le (q.2 - z))
  · exact integrable_const _
  · apply ae_of_all
    intro z
    exact (continuousAt_firstKernel (p := (p.1, p.2 - z)) hp).comp
      (f := fun q : ℝ × ℝ ↦ (q.1, q.2 - z))
      (continuousAt_fst.prodMk (continuousAt_snd.sub_const z))

lemma continuous_firstSmooth_space (μ : Measure ℝ) [IsFiniteMeasure μ]
    {y : ℝ} (hy : 0 < y) : Continuous (firstSmooth μ y) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (continuousAt_firstSmooth μ (p := (y, x)) hy).comp
    (continuousAt_const.prodMk continuousAt_id)

lemma continuousOn_firstSmooth_variance (μ : Measure ℝ) [IsFiniteMeasure μ]
    (x : ℝ) : ContinuousOn (fun y ↦ firstSmooth μ y x) (Ioi 0) := by
  intro y hy
  exact ((continuousAt_firstSmooth μ (p := (y, x)) hy).comp (f := fun t ↦ (t, x))
    (continuousAt_id.prodMk continuousAt_const)).continuousWithinAt

lemma integrable_smooth (μ : Measure ℝ) [IsFiniteMeasure μ]
    {y : ℝ} (hy : 0 < y) : Integrable (smooth μ y) volume :=
  integrable_averageTranslate μ (continuous_kernel y) (integrable_kernel hy.le)

lemma integrable_firstSmooth (μ : Measure ℝ) [IsFiniteMeasure μ]
    {y : ℝ} (hy : 0 < y) : Integrable (firstSmooth μ y) volume :=
  integrable_averageTranslate μ (continuous_firstKernel y) (integrable_firstKernel hy)

end LpSelfSimilar.Gaussian
