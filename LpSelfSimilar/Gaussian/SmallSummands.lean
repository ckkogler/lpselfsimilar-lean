module

public import LpSelfSimilar.Gaussian.ReplacementError
public import LpSelfSimilar.Analysis.VarianceWeights
public import LpSelfSimilar.Probability.FiniteConvolutionLaws

@[expose] public section

/-!
Finite Lindeberg replacement for bounded centered summands. The variance weights
telescope, so the error is independent of the number of summands and their total
variance. This is the finite-convolution form of the small-summand estimate.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real
open scoped NNReal

namespace LpSelfSimilar.Gaussian

/-- Finite replacement error, uniformly over the number of summands. -/
theorem finite_replacementError_le {n : ℕ} (μ : Fin n → Measure ℝ) (v : Fin n → ℝ≥0)
    [∀ i, IsProbabilityMeasure (μ i)] {R y : ℝ} (hR : 0 ≤ R) (hy : 0 < y)
    (hRy : R ^ 2 ≤ y) (hb : ∀ i, ∀ᵐ u ∂μ i, |u| ≤ R)
    (hm : ∀ i, (∫ u : ℝ, u ∂μ i) = 0)
    (hv : ∀ i, (∫ u : ℝ, u ^ 2 ∂μ i) = v i) :
    replacementError (finiteConvolution μ) (∑ i, v i) y ≤
      24 * replacementConstant * R * (y⁻¹ / Real.sqrt y) := by
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
    have hw := variance_increment_weight_le hy (v 0).coe_nonneg hvy
    have hweighted := mul_le_mul_of_nonneg_left hw
      (mul_nonneg replacementConstant_nonneg hR)
    rw [finiteConvolution, Fin.sum_univ_succ]
    apply (replacementError_conv_le (μ 0) (finiteConvolution μt) (v 0) (∑ j, vt j) hy).trans
    apply (add_le_add hhead hrest).trans
    rw [add_comm (v 0 : ℝ) y]
    nlinarith

/-- The ordinary detail is bounded by the matching Gaussian detail and the
normalized first-derivative replacement error. -/
lemma detail_le_gaussian_add_replacementError (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (v : ℝ≥0) {r : ℝ} (hr : 0 < r) :
    detail μ r ≤ r ^ 2 / (r ^ 2 + (v : ℝ)) +
      r ^ 2 * detailNormalization * replacementError μ v (r ^ 2) := by
  have hy : 0 < r ^ 2 := sq_pos_of_pos hr
  have hvy : 0 < (v : ℝ) + r ^ 2 := by positivity
  have hi := (integrable_firstSmooth μ hy).sub (integrable_firstKernel hvy)
  have hb : (∫ x, |firstSmooth μ (r ^ 2) x|) ≤
      (∫ x, |firstKernel ((v : ℝ) + r ^ 2) x|) + replacementError μ v (r ^ 2) := by
    calc
      _ ≤ ∫ x, |firstKernel ((v : ℝ) + r ^ 2) x| +
          |firstSmooth μ (r ^ 2) x - firstKernel ((v : ℝ) + r ^ 2) x| := by
        apply integral_mono (integrable_firstSmooth μ hy).abs
          ((integrable_firstKernel hvy).abs.add hi.abs)
        intro x
        convert (abs_add_le (firstKernel ((v : ℝ) + r ^ 2) x)
          (firstSmooth μ (r ^ 2) x - firstKernel ((v : ℝ) + r ^ 2) x)) using 1 <;> try rfl
        congr 1
        ring
      _ = _ := integral_add (integrable_firstKernel hvy).abs hi.abs
  have h := mul_le_mul_of_nonneg_left hb
    (mul_nonneg (sq_nonneg r) detailNormalization_pos.le)
  have hg := detail_gaussian v hr
  unfold detail at hg ⊢
  change r ^ 2 * detailNormalization * (∫ x, |firstSmooth (gaussianReal 0 v) (r ^ 2) x|) = _ at hg
  simp_rw [firstSmooth_gaussian v hy] at hg
  change r ^ 2 * detailNormalization * (∫ x, |firstSmooth μ (r ^ 2) x|) ≤ _
  rw [mul_add, hg] at h
  exact h

/-- An absolute constant in the finite small-summand estimate. -/
noncomputable def smallSummandConstant : ℝ := 24 * detailNormalization * replacementConstant

lemma smallSummandConstant_nonneg : 0 ≤ smallSummandConstant := by
  unfold smallSummandConstant
  positivity [detailNormalization_pos, replacementConstant_nonneg]

/-- Lemma 3.2 for finitely many bounded centered independent summands, expressed
through their convolution laws. The variance and all moment conditions are
explicit; no smoothing hypothesis is assumed. -/
theorem detail_finiteConvolution_le {n : ℕ} (μ : Fin n → Measure ℝ) (v : Fin n → ℝ≥0)
    [∀ i, IsProbabilityMeasure (μ i)] {ε r : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hr : 0 < r)
    (hb : ∀ i, ∀ᵐ u ∂μ i, |u| ≤ ε * r)
    (hm : ∀ i, (∫ u : ℝ, u ∂μ i) = 0)
    (hv : ∀ i, (∫ u : ℝ, u ^ 2 ∂μ i) = v i) :
    detail (finiteConvolution μ) r ≤
      r ^ 2 / (r ^ 2 + (∑ i, v i : ℝ≥0)) + smallSummandConstant * ε := by
  have hR : 0 ≤ ε * r := mul_nonneg hε hr.le
  have hRy : (ε * r) ^ 2 ≤ r ^ 2 := by
    apply pow_le_pow_left₀ hR
    nlinarith
  have he := finite_replacementError_le μ v hR (sq_pos_of_pos hr) hRy hb hm hv
  have he' := mul_le_mul_of_nonneg_left he
    (mul_nonneg (sq_nonneg r) detailNormalization_pos.le)
  have hn : r ^ 2 * detailNormalization *
      (24 * replacementConstant * (ε * r) * ((r ^ 2)⁻¹ / Real.sqrt (r ^ 2))) =
      smallSummandConstant * ε := by
    rw [Real.sqrt_sq hr.le]
    unfold smallSummandConstant
    field_simp
    <;> ring
  rw [hn] at he'
  exact (detail_le_gaussian_add_replacementError _ _ hr).trans (add_le_add le_rfl he')

end LpSelfSimilar.Gaussian
