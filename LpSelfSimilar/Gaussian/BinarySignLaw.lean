module

public import LpSelfSimilar.Gaussian.BinaryChannelLaw
public import LpSelfSimilar.Gaussian.StandardTailBound
public import LpSelfSimilar.Probability.SignPartition

@[expose] public section

/-!
# The actual binary Gaussian sign channel

The Gaussian output mixture is reflection-invariant and has no atom at zero,
so its sign is fair. The positive-mean component's negative-sign probability
is exactly the corresponding standard Gaussian upper tail. These are measure
identities for the actual additive channel, including amplitude zero.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal
open LpSelfSimilar.Probability

namespace LpSelfSimilar.Gaussian

theorem binaryGaussianLaw_eq_half_add (u : ℝ) :
    binaryGaussianLaw u = (1 / 2 : ℝ≥0∞) • gaussianReal u 1 +
      (1 / 2 : ℝ≥0∞) • gaussianReal (-u) 1 := by
  ext s hs
  rw [binaryGaussianLaw_eq_channel_mixture, Measure.bind_apply hs (Kernel.measurable _).aemeasurable,
    lintegral_fintype]
  simp only [binary_channel_component_eq_gaussian, Fintype.sum_bool,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, Fintype.card_bool, Bool.false_eq_true, ite_false, ite_true,
    Measure.add_apply, Measure.smul_apply, smul_eq_mul, one_div]
  ac_rfl

theorem binaryGaussianLaw_map_neg (u : ℝ) :
    (binaryGaussianLaw u).map (fun x : ℝ => -x) = binaryGaussianLaw u := by
  rw [binaryGaussianLaw_eq_half_add, Measure.map_add _ _ measurable_neg]
  simp only [Measure.map_smul, gaussianReal_map_neg, neg_neg]
  rw [add_comm]

theorem binaryGaussianLaw_singleton_zero (u : ℝ) : binaryGaussianLaw u {0} = 0 := by
  rw [binaryGaussianLaw_eq_withDensity]
  haveI : NullSingletonClass
      (volume.withDensity (fun x => ENNReal.ofReal (binaryGaussianDensity u x))) := inferInstance
  exact measure_singleton 0

theorem binaryGaussianLaw_sign_masses (u : ℝ) (b : Bool) :
    ((binaryGaussianLaw u).map nonnegativeSign) {b} = (1 / 2 : ℝ≥0∞) :=
  symmetric_sign_masses (binaryGaussianLaw u) (binaryGaussianLaw_map_neg u)
    (binaryGaussianLaw_singleton_zero u) b

/-- The conditional error of the sign decoder is exactly a standard upper tail. -/
theorem gaussian_positive_component_sign_error (u : ℝ) :
    ((gaussianReal u 1).map nonnegativeSign) {false} = (gaussianReal 0 1) (Ioi u) := by
  rw [Measure.map_apply measurable_nonnegativeSign (measurableSet_singleton _),
    nonnegativeSign_preimage_false]
  have hshift : gaussianReal u 1 = (gaussianReal 0 1).map (fun x : ℝ => x + u) := by
    rw [gaussianReal_map_add_const]; simp
  rw [hshift, Measure.map_apply (by fun_prop) measurableSet_Iio]
  have hpre : (fun x : ℝ => x + u) ⁻¹' Iio 0 = Iio (-u) := by
    ext x; simp only [mem_preimage, mem_Iio]; constructor <;> intro h <;> linarith
  rw [hpre]
  have href : (gaussianReal 0 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
    rw [gaussianReal_map_neg]; simp
  have h := congrArg (fun μ : Measure ℝ => μ (Iio (-u))) href
  rw [Measure.map_apply measurable_neg measurableSet_Iio] at h
  have hneg : (fun x : ℝ => -x) ⁻¹' Iio (-u) = Ioi u := by
    ext x; simp
  simpa only [hneg] using h.symm

/-- The other conditional decoder error has the same standard upper tail. -/
theorem gaussian_negative_component_sign_error (u : ℝ) :
    ((gaussianReal (-u) 1).map nonnegativeSign) {true} = (gaussianReal 0 1) (Ioi u) := by
  rw [Measure.map_apply measurable_nonnegativeSign (measurableSet_singleton _),
    nonnegativeSign_preimage_true]
  have hshift : gaussianReal (-u) 1 = (gaussianReal 0 1).map (fun x : ℝ => x - u) := by
    have h := gaussianReal_map_add_const (μ := (0 : ℝ)) (v := (1 : NNReal)) (-u)
    simpa only [zero_add, sub_eq_add_neg] using h.symm
  rw [hshift, Measure.map_apply (by fun_prop) measurableSet_Ici]
  have hpre : (fun x : ℝ => x - u) ⁻¹' Ici 0 = Ici u := by
    ext x; simp only [mem_preimage, mem_Ici]; constructor <;> intro h <;> linarith
  rw [hpre]
  haveI := nullSingletonClass_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal)) (by norm_num)
  exact measure_Ici_eq_Ioi_of_singleton_zero (gaussianReal 0 1) u (measure_singleton u)

/-- The fair-input error is the average of the two actual conditional errors. -/
theorem binaryGaussian_sign_error_eq_tail (u : ℝ) :
    ((((gaussianReal u 1).map nonnegativeSign) {false}).toReal +
      (((gaussianReal (-u) 1).map nonnegativeSign) {true}).toReal) / 2 =
        ((gaussianReal 0 1) (Ioi u)).toReal := by
  rw [gaussian_positive_component_sign_error, gaussian_negative_component_sign_error]
  ring

/-- Both conditional errors, and hence their fair average, satisfy the strict decoder threshold. -/
theorem binaryGaussian_sign_error_two_lt :
    ((((gaussianReal 2 1).map nonnegativeSign) {false}).toReal +
      (((gaussianReal (-2) 1).map nonnegativeSign) {true}).toReal) / 2 < (1 / 32 : ℝ) := by
  rw [binaryGaussian_sign_error_eq_tail]
  exact standard_gaussian_tail_two_lt

theorem gaussian_positive_component_sign_error_two_lt :
    (((gaussianReal 2 1).map nonnegativeSign) {false}).toReal < (1 / 32 : ℝ) := by
  rw [gaussian_positive_component_sign_error]
  exact standard_gaussian_tail_two_lt

end LpSelfSimilar.Gaussian
