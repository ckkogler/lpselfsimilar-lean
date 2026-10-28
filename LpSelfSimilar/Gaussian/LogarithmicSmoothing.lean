module

public import LpSelfSimilar.Gaussian.IntegratingScales

@[expose] public section

/-!
Gaussian smoothing in logarithmic radius. This is (3.3) after the change of
variable r = exp(-R), proved directly by the chain rule and Fubini. The derivative
has L1 norm at most 2/Q, giving product integrability on every finite interval.
-/

open MeasureTheory MeasureTheory.Measure Real Set

namespace LpSelfSimilar.Gaussian

@[fun_prop] lemma measurable_detail_logarithmic (μ : Measure ℝ) [SFinite μ] :
    Measurable (fun R : ℝ ↦ detail μ (exp (-R))) := by
  have hm : Measurable (fun p : ℝ × ℝ ↦ |firstSmooth μ ((exp (-p.1)) ^ 2) p.2|) := by
    fun_prop
  change Measurable (fun R : ℝ ↦ (exp (-R)) ^ 2 * detailNormalization *
    ∫ x, |firstSmooth μ ((exp (-R)) ^ 2) x|)
  exact Measurable.mul (by fun_prop) hm.stronglyMeasurable.integral_prod_right'.measurable

lemma integrableOn_detail_logarithmic (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b : ℝ) : IntegrableOn (fun R : ℝ ↦ detail μ (exp (-R))) (Ioc a b) volume := by
  apply (integrable_const (1 : ℝ)).mono'
    (measurable_detail_logarithmic μ).aestronglyMeasurable
  apply ae_of_all
  intro R
  rw [Real.norm_eq_abs, abs_of_nonneg (detail_nonneg μ (exp (-R)))]
  exact detail_le_one μ (exp_pos (-R))

noncomputable def logarithmicDerivative (μ : Measure ℝ) (R x : ℝ) : ℝ :=
  -exp (-R) * radiusDerivative μ (exp (-R)) x

@[fun_prop] lemma measurable_logarithmicDerivative_joint (μ : Measure ℝ) [SFinite μ] :
    Measurable (fun p : ℝ × ℝ ↦ logarithmicDerivative μ p.1 p.2) := by
  unfold logarithmicDerivative
  fun_prop

lemma hasDerivAt_smooth_logarithmic (μ : Measure ℝ) [IsFiniteMeasure μ]
    (R x : ℝ) : HasDerivAt (fun S ↦ smooth μ ((exp (-S)) ^ 2) x)
      (logarithmicDerivative μ R x) R := by
  have he := ((hasDerivAt_id R).neg).exp
  convert (hasDerivAt_smooth_scale μ (exp_pos (-R)) x).comp R
    (h := fun S ↦ exp (-S)) he using 1 <;> try rfl
  dsimp only [logarithmicDerivative, Pi.neg_apply, id_eq]
  ring

lemma continuous_logarithmicDerivative (μ : Measure ℝ) [IsFiniteMeasure μ] (x : ℝ) :
    Continuous (fun R ↦ logarithmicDerivative μ R x) := by
  rw [continuous_iff_continuousAt]
  intro R
  unfold logarithmicDerivative radiusDerivative
  apply ContinuousAt.mul (by fun_prop)
  apply ContinuousAt.mul (by fun_prop)
  exact (continuousAt_firstSmooth μ (p := ((exp (-R)) ^ 2, x)) (by positivity)).comp
    (f := fun S ↦ ((exp (-S)) ^ 2, x)) (by fun_prop)

lemma integrable_logarithmicDerivative (μ : Measure ℝ) [IsFiniteMeasure μ] (R : ℝ) :
    Integrable (logarithmicDerivative μ R) volume :=
  (integrable_radiusDerivative μ (exp_pos (-R))).const_mul _

lemma integral_abs_logarithmicDerivative (μ : Measure ℝ) [IsFiniteMeasure μ] (R : ℝ) :
    (∫ x, |logarithmicDerivative μ R x|) =
      (2 / detailNormalization) * detail μ (exp (-R)) := by
  simp only [logarithmicDerivative, abs_mul, abs_neg, abs_of_pos (exp_pos (-R)),
    integral_const_mul]
  rw [integral_abs_radiusDerivative_eq_detail μ (exp_pos (-R))]
  field_simp

lemma integrable_logarithmicDerivative_product (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b : ℝ) : Integrable (fun p : ℝ × ℝ ↦ logarithmicDerivative μ p.1 p.2)
      ((volume.restrict (Ioc a b)).prod volume) := by
  have hm := measurable_logarithmicDerivative_joint μ
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ (fun R ↦ integrable_logarithmicDerivative μ R)
  · apply (integrable_const (2 / detailNormalization)).mono'
      hm.stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable
    apply ae_of_all
    intro R
    simp only [Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg (fun _ ↦ abs_nonneg _)),
      integral_abs_logarithmicDerivative]
    have hQ : 0 ≤ 2 / detailNormalization :=
      div_nonneg (by norm_num) detailNormalization_pos.le
    rw [abs_of_nonneg (mul_nonneg hQ (detail_nonneg μ (exp (-R))))]
    exact mul_le_of_le_one_right hQ
      (detail_le_one μ (exp_pos (-R)))

lemma smooth_logarithmic_sub (μ : Measure ℝ) [IsFiniteMeasure μ] (a b x : ℝ) :
    smooth μ ((exp (-b)) ^ 2) x - smooth μ ((exp (-a)) ^ 2) x =
      ∫ R in a..b, logarithmicDerivative μ R x := by
  symm
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun R _ ↦ hasDerivAt_smooth_logarithmic μ R x)
    ((continuous_logarithmicDerivative μ x).intervalIntegrable a b)

/-- The exact scale-integral estimate in logarithmic coordinates. -/
theorem smoothing_difference_le_logarithmic_detail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a b : ℝ} (hab : a ≤ b) :
    (∫ x, |smooth μ ((exp (-b)) ^ 2) x - smooth μ ((exp (-a)) ^ 2) x|) ≤
      (2 / detailNormalization) * ∫ R in a..b, detail μ (exp (-R)) := by
  have hi := integrable_logarithmicDerivative_product μ a b
  calc
    _ ≤ ∫ R in Ioc a b, ∫ x, |logarithmicDerivative μ R x| := by
      calc
        _ ≤ ∫ x, ∫ R in Ioc a b, |logarithmicDerivative μ R x| := by
          apply integral_mono
            ((integrable_smooth μ (by positivity : 0 < (exp (-b)) ^ 2)).sub
              (integrable_smooth μ (by positivity : 0 < (exp (-a)) ^ 2))).abs
            hi.norm.integral_prod_right
          intro x
          change |smooth μ ((exp (-b)) ^ 2) x - smooth μ ((exp (-a)) ^ 2) x| ≤
            ∫ R in Ioc a b, |logarithmicDerivative μ R x|
          rw [smooth_logarithmic_sub μ a b x, intervalIntegral.integral_of_le hab]
          simpa only [Real.norm_eq_abs] using
            norm_integral_le_integral_norm (fun R ↦ logarithmicDerivative μ R x)
              (μ := volume.restrict (Ioc a b))
        _ = _ := integral_integral_swap hi.norm.swap
    _ = _ := by
      simp_rw [integral_abs_logarithmicDerivative]
      rw [integral_const_mul, intervalIntegral.integral_of_le hab]

end LpSelfSimilar.Gaussian
