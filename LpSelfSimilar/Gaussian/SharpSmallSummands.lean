module

public import LpSelfSimilar.Probability.MapProbability

public import LpSelfSimilar.Gaussian.SmallSummands
public import LpSelfSimilar.Gaussian.ExactNormalization
public import LpSelfSimilar.Gaussian.HermiteFiveBound
public import LpSelfSimilar.Gaussian.AbsoluteMomentBounds
public import LpSelfSimilar.Analysis.SharpVarianceWeights
public import LpSelfSimilar.Probability.Centering

@[expose] public section

/-!
The explicit small-summand estimate of revised Lemma 3.2. The earlier Gaussian
replacement proof is retained; sharper telescoping weights and proved Hermite
and moment bounds give the numerical error 30 epsilon. Centering is derived,
and the bound applies to arbitrary finite probability laws, including point masses.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real
open scoped NNReal

namespace LpSelfSimilar.Gaussian

lemma replacementConstant_le_eleven_div_four : replacementConstant ≤ 11 / 4 := by
  have hs : Real.sqrt 120 ≤ 11 := by
    have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 120)
    nlinarith [Real.sqrt_nonneg 120]
  have ht : thirdSpatialNorm ≤ 11 / 2 := thirdSpatialNorm_le_sqrt.trans
    (div_le_div_of_nonneg_right hs (by norm_num))
  have hp := mul_le_mul (show 1 + unitThirdMoment ≤ 3 by linarith [unitThirdMoment_le_two])
    ht thirdSpatialNorm_nonneg (by norm_num : (0 : ℝ) ≤ 3)
  unfold replacementConstant
  nlinarith

lemma twice_normalized_replacementConstant_le_fifteen :
    2 * detailNormalization * replacementConstant ≤ 15 := by
  have h := mul_le_mul detailNormalization_lt_twenty_one_div_ten.le
    replacementConstant_le_eleven_div_four replacementConstant_nonneg
    (by norm_num : (0 : ℝ) ≤ 21 / 10)
  nlinarith

/-- The constant-two telescoping replacement estimate. -/
theorem finite_replacementError_le_two {n : ℕ} (μ : Fin n → Measure ℝ) (v : Fin n → ℝ≥0)
    [∀ i, IsProbabilityMeasure (μ i)] {R y : ℝ} (hR : 0 ≤ R) (hy : 0 < y)
    (hRy : R ^ 2 ≤ y) (hb : ∀ i, ∀ᵐ u ∂μ i, |u| ≤ R)
    (hm : ∀ i, (∫ u : ℝ, u ∂μ i) = 0)
    (hv : ∀ i, (∫ u : ℝ, u ^ 2 ∂μ i) = v i) :
    replacementError (finiteConvolution μ) (∑ i, v i) y ≤
      2 * replacementConstant * R * (y⁻¹ / Real.sqrt y) := by
  induction n generalizing y with
  | zero =>
    simp only [finiteConvolution, Finset.univ_eq_empty, Finset.sum_empty, replacementError_dirac_zero]
    positivity [replacementConstant_nonneg]
  | succ n ih =>
    let μt := fun j : Fin n ↦ μ j.succ
    let vt := fun j : Fin n ↦ v j.succ
    have hnew : 0 < (v 0 : ℝ) + y := by positivity
    have hRy' : R ^ 2 ≤ (v 0 : ℝ) + y := by linarith [(v 0).coe_nonneg]
    have hrest := ih μt vt hnew hRy' (fun j ↦ hb j.succ)
      (fun j ↦ hm j.succ) (fun j ↦ hv j.succ)
    have hhead := firstSmooth_sub_gaussian_le (μ 0) hR hy (hb 0) (hm 0) (v 0) (hv 0)
    have hvy : (v 0 : ℝ) ≤ y := by
      rw [← hv 0]
      exact (integral_sq_le_of_ae_bound (μ 0) hR (hb 0)).trans hRy
    have hw := variance_increment_weight_le_two hy (v 0).coe_nonneg hvy
    have hweighted := mul_le_mul_of_nonneg_left hw
      (mul_nonneg replacementConstant_nonneg hR)
    rw [finiteConvolution, Fin.sum_univ_succ]
    apply (replacementError_conv_le (μ 0) (finiteConvolution μt) (v 0) (∑ j, vt j) hy).trans
    apply (add_le_add hhead hrest).trans
    rw [add_comm (v 0 : ℝ) y]
    nlinarith

/-- Centered small summands, with the numerical error fifteen epsilon. -/
theorem detail_finiteConvolution_le_fifteen {n : ℕ} (μ : Fin n → Measure ℝ)
    (v : Fin n → ℝ≥0) [∀ i, IsProbabilityMeasure (μ i)] {ε r : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hr : 0 < r)
    (hb : ∀ i, ∀ᵐ u ∂μ i, |u| ≤ ε * r)
    (hm : ∀ i, (∫ u : ℝ, u ∂μ i) = 0)
    (hv : ∀ i, (∫ u : ℝ, u ^ 2 ∂μ i) = v i) :
    detail (finiteConvolution μ) r ≤
      r ^ 2 / (r ^ 2 + (∑ i, v i : ℝ≥0)) + 15 * ε := by
  have hR : 0 ≤ ε * r := mul_nonneg hε hr.le
  have hRy : (ε * r) ^ 2 ≤ r ^ 2 := by
    apply pow_le_pow_left₀ hR
    nlinarith
  have he := finite_replacementError_le_two μ v hR (sq_pos_of_pos hr) hRy hb hm hv
  have he' := mul_le_mul_of_nonneg_left he
    (mul_nonneg (sq_nonneg r) detailNormalization_pos.le)
  have hn : r ^ 2 * detailNormalization *
      (2 * replacementConstant * (ε * r) * ((r ^ 2)⁻¹ / Real.sqrt (r ^ 2))) =
      (2 * detailNormalization * replacementConstant) * ε := by
    rw [Real.sqrt_sq hr.le]
    field_simp
  rw [hn] at he'
  exact (detail_le_gaussian_add_replacementError _ _ hr).trans
    (add_le_add le_rfl (he'.trans (mul_le_mul_of_nonneg_right
      twice_normalized_replacementConstant_le_fifteen hε)))

/-- Revised Lemma 3.2, for the laws of arbitrary independent bounded summands.
Finite convolution is their actual sum law. No centering or smoothing hypothesis
is imposed, and all variances are the canonical Mathlib variances. -/
theorem small_summands_explicit {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] {ε r : ℝ}
    (hε : 0 ≤ ε) (hr : 0 < r)
    (hb : ∀ i, ∀ᵐ u ∂μ i, |u| ≤ ε * r) :
    detail (finiteConvolution μ) r ≤
      r ^ 2 / (r ^ 2 + ∑ i, variance (fun u : ℝ ↦ u) (μ i)) + 30 * ε := by
  have hvn : 0 ≤ ∑ i, variance (fun u : ℝ ↦ u) (μ i) :=
    Finset.sum_nonneg (fun i _ ↦ variance_nonneg _ _)
  have hfrac : 0 ≤ r ^ 2 / (r ^ 2 + ∑ i, variance (fun u : ℝ ↦ u) (μ i)) := by positivity
  by_cases he : 2 * ε ≤ 1
  · let v (i : Fin n) : ℝ≥0 := ⟨variance (fun u : ℝ ↦ u) (μ i), variance_nonneg _ _⟩
    have hR : 0 ≤ ε * r := mul_nonneg hε hr.le
    have hh := detail_finiteConvolution_le_fifteen (fun i ↦ centeredLaw (μ i)) v
      (by positivity : 0 ≤ 2 * ε) he hr
      (fun i ↦ by simpa only [mul_assoc] using centeredLaw_bound (μ i) hR (hb i))
      (fun i ↦ centeredLaw_mean (μ i) hR (hb i))
      (fun i ↦ centeredLaw_secondMoment (μ i))
    rw [finiteConvolution_centered, detail_map_add] at hh
    have hsv : ((∑ i, v i : ℝ≥0) : ℝ) = ∑ i, variance (fun u : ℝ ↦ u) (μ i) :=
      NNReal.coe_sum Finset.univ v
    rw [hsv] at hh
    linarith
  · exact (detail_le_one _ hr).trans (by linarith)

/-- The random-variable formulation of revised Lemma 3.2. -/
theorem small_summands_independent {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X P) {ε r : ℝ}
    (hε : 0 ≤ ε) (hr : 0 < r) (hb : ∀ i, ∀ᵐ ω ∂P, |X i ω| ≤ ε * r) :
    detail (P.map (fun ω ↦ ∑ i, X i ω)) r ≤
      r ^ 2 / (r ^ 2 + ∑ i, variance (X i) P) + 30 * ε := by
  haveI (i : Fin n) : IsProbabilityMeasure (P.map (X i)) :=
    LpSelfSimilar.Probability.isProbabilityMeasure_map (hX i).aemeasurable
  have hb' (i : Fin n) : ∀ᵐ u ∂P.map (X i), |u| ≤ ε * r := by
    rw [ae_map_iff (hX i).aemeasurable (isClosed_le continuous_abs continuous_const).measurableSet]
    exact hb i
  have h := small_summands_explicit (fun i ↦ P.map (X i)) hε hr hb'
  have hv (i : Fin n) : variance (fun u : ℝ ↦ u) (P.map (X i)) = variance (X i) P :=
    variance_id_map (hX i).aemeasurable
  simp_rw [hv] at h
  rw [map_sum_eq_finiteConvolution hX hind]
  exact h

end LpSelfSimilar.Gaussian
