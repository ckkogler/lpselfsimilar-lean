module

public import LpSelfSimilar.Gaussian.Smoothing
public import LpSelfSimilar.Gaussian.Detail
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-!
The fundamental theorem of calculus for Gaussian smoothing in the scale
parameter, and the L1 estimate (3.3). All product integrability needed for
interchanging the space and scale integrals is established explicitly.
-/

open MeasureTheory MeasureTheory.Measure Set Real

namespace LpSelfSimilar.Gaussian

/-- Derivative of smoothing at variance `r²` with respect to the scale `r`. -/
noncomputable def radiusDerivative (μ : Measure ℝ) (r x : ℝ) : ℝ :=
  (2 * r) * firstSmooth μ (r ^ 2) x

@[fun_prop] lemma measurable_radiusDerivative_joint (μ : Measure ℝ) [SFinite μ] :
    Measurable (fun p : ℝ × ℝ ↦ radiusDerivative μ p.1 p.2) := by
  unfold radiusDerivative
  fun_prop

lemma hasDerivAt_smooth_scale (μ : Measure ℝ) [IsFiniteMeasure μ]
    {r : ℝ} (hr : 0 < r) (x : ℝ) :
    HasDerivAt (fun t ↦ smooth μ (t ^ 2) x) (radiusDerivative μ r x) r := by
  convert (hasDerivAt_smooth_variance μ (by positivity : 0 < r ^ 2) x).comp r
    (h := fun t ↦ t ^ 2)
    ((hasDerivAt_id r).pow 2) using 1 <;> try rfl
  simp [radiusDerivative, mul_comm]

lemma continuousOn_radiusDerivative (μ : Measure ℝ) [IsFiniteMeasure μ] (x : ℝ) :
    ContinuousOn (fun r ↦ radiusDerivative μ r x) (Ioi 0) := by
  intro r hr
  have hr' : 0 < r := hr
  apply ContinuousAt.continuousWithinAt
  unfold radiusDerivative
  apply ContinuousAt.mul (by fun_prop)
  exact (continuousAt_firstSmooth μ (p := (r ^ 2, x)) (by positivity)).comp
    (f := fun t ↦ (t ^ 2, x)) (by fun_prop)

lemma smooth_sub_eq_integral_radiusDerivative (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (x : ℝ) :
    smooth μ (b ^ 2) x - smooth μ (a ^ 2) x =
      ∫ r in a..b, radiusDerivative μ r x := by
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro r hr
    rw [uIcc_of_le hab] at hr
    exact hasDerivAt_smooth_scale μ (ha.trans_le hr.1) x
  · apply ContinuousOn.intervalIntegrable
    apply (continuousOn_radiusDerivative μ x).mono
    rw [uIcc_of_le hab]
    exact fun _ hr ↦ ha.trans_le hr.1

lemma integrable_radiusDerivative (μ : Measure ℝ) [IsFiniteMeasure μ]
    {r : ℝ} (hr : 0 < r) : Integrable (radiusDerivative μ r) volume :=
  (integrable_firstSmooth μ (by positivity : 0 < r ^ 2)).const_mul (2 * r)

lemma integral_abs_radiusDerivative (μ : Measure ℝ) [IsFiniteMeasure μ]
    {r : ℝ} (hr : 0 < r) :
    (∫ x, |radiusDerivative μ r x|) =
      (2 * r) * ∫ x, |firstSmooth μ (r ^ 2) x| := by
  have h (x : ℝ) : |radiusDerivative μ r x| = 2 * r * |firstSmooth μ (r ^ 2) x| := by
    rw [radiusDerivative, abs_mul, abs_of_pos (by positivity : 0 < 2 * r)]
  simp_rw [h]
  exact integral_const_mul _ _

lemma integral_abs_radiusDerivative_le (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a r : ℝ} (ha : 0 < a) (har : a ≤ r) :
    (∫ x, |radiusDerivative μ r x|) ≤ (2 / a) * μ.real univ * firstNorm := by
  have hr := ha.trans_le har
  have h := integral_abs_averageTranslate_le μ (continuous_firstKernel (r ^ 2))
    (integrable_firstKernel (by positivity : 0 < r ^ 2))
  rw [integral_abs_firstKernel (by positivity : 0 < r ^ 2)] at h
  rw [integral_abs_radiusDerivative μ hr]
  calc
    (2 * r) * (∫ x, |firstSmooth μ (r ^ 2) x|) ≤
        (2 * r) * (μ.real univ * ((r ^ 2)⁻¹ * firstNorm)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = (2 / r) * μ.real univ * firstNorm := by field_simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ firstNorm_pos.le
      gcongr

lemma integrable_radiusDerivative_product (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a b : ℝ} (ha : 0 < a) :
    Integrable (fun p : ℝ × ℝ ↦ radiusDerivative μ p.1 p.2)
      ((volume.restrict (Ioc a b)).prod volume) := by
  apply (integrable_prod_iff (measurable_radiusDerivative_joint μ).aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact integrable_radiusDerivative μ (ha.trans hr.1)
  · have hm : AEStronglyMeasurable
        (fun r ↦ ∫ x, ‖radiusDerivative μ r x‖) (volume.restrict (Ioc a b)) := by
      exact (measurable_radiusDerivative_joint μ).stronglyMeasurable.norm.integral_prod_right'
        |>.aestronglyMeasurable
    apply (integrable_const ((2 / a) * μ.real univ * firstNorm)).mono' hm
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ ↦ norm_nonneg _))]
    simpa only [Real.norm_eq_abs] using integral_abs_radiusDerivative_le μ ha hr.1.le

lemma integral_abs_smooth_sub_le (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x, |smooth μ (b ^ 2) x - smooth μ (a ^ 2) x|) ≤
      ∫ r in a..b, ∫ x, |radiusDerivative μ r x| := by
  have hi := integrable_radiusDerivative_product μ (b := b) ha
  have hb : 0 < b := ha.trans_le hab
  rw [intervalIntegral.integral_of_le hab]
  calc
    (∫ x, |smooth μ (b ^ 2) x - smooth μ (a ^ 2) x|) ≤
        ∫ x, ∫ r in Ioc a b, |radiusDerivative μ r x| := by
      apply integral_mono
        ((integrable_smooth μ (by positivity : 0 < b ^ 2)).sub
          (integrable_smooth μ (by positivity : 0 < a ^ 2))).abs
        hi.norm.integral_prod_right
      intro x
      change |smooth μ (b ^ 2) x - smooth μ (a ^ 2) x| ≤
        ∫ r in Ioc a b, |radiusDerivative μ r x|
      rw [smooth_sub_eq_integral_radiusDerivative μ ha hab,
        intervalIntegral.integral_of_le hab]
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun r ↦ radiusDerivative μ r x)
          (μ := volume.restrict (Ioc a b))
    _ = _ := integral_integral_swap hi.norm.swap

lemma integral_abs_radiusDerivative_eq_detail (μ : Measure ℝ) [IsFiniteMeasure μ]
    {r : ℝ} (hr : 0 < r) :
    (∫ x, |radiusDerivative μ r x|) =
      (2 / detailNormalization) * (detail μ r / r) := by
  rw [integral_abs_radiusDerivative μ hr]
  unfold detail firstSmooth
  field_simp [detailNormalization_pos.ne', hr.ne']

/-- The exact integral-over-scales estimate (3.3) of the paper. -/
theorem smoothing_difference_le_integral_detail (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x, |smooth μ (b ^ 2) x - smooth μ (a ^ 2) x|) ≤
      (2 / detailNormalization) * ∫ r in a..b, detail μ r / r := by
  apply (integral_abs_smooth_sub_le μ ha hab).trans_eq
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le hab] at hr
  exact integral_abs_radiusDerivative_eq_detail μ (ha.trans_le hr.1)

end LpSelfSimilar.Gaussian
