module

public import LpSelfSimilar.Gaussian.HigherDetail
public import LpSelfSimilar.Probability.FiniteMixture

@[expose] public section

/-!
Convexity of ordinary and higher detail under finite probability mixtures.
This is the averaging step in conditioning on finitely many grid cells.
-/

open MeasureTheory MeasureTheory.Measure Real
open scoped NNReal

namespace LpSelfSimilar.Gaussian

lemma higherDetail_finiteMixture_le {I : Type*} [Fintype I]
    (w : I → ℝ≥0) (μ : I → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {k : ℕ} (hk : 0 < k) {r : ℝ} (hr : 0 < r) :
    higherDetail (finiteMixture w μ) k r ≤ ∑ i, (w i : ℝ) * higherDetail (μ i) k r := by
  have hy : 0 < (k : ℝ) * r ^ 2 := by positivity
  obtain ⟨C, _, hb⟩ := exists_uniform_bound_higherKernel k hy
  have he (x : ℝ) : higherSmooth (finiteMixture w μ) k ((k : ℝ) * r ^ 2) x =
      ∑ i, (w i : ℝ) * higherSmooth (μ i) k ((k : ℝ) * r ^ 2) x :=
    averageTranslate_finiteMixture w μ (continuous_higherKernel_space k _) (hb _ le_rfl) x
  have hi (i : I) := (integrable_higherSmooth (μ i) k hy).const_mul (w i : ℝ)
  have hL : (∫ x, |∑ i, (w i : ℝ) * higherSmooth (μ i) k ((k : ℝ) * r ^ 2) x|) ≤
      ∑ i, (w i : ℝ) * ∫ x, |higherSmooth (μ i) k ((k : ℝ) * r ^ 2) x| := by
    calc
      _ ≤ ∫ x, ∑ i, |(w i : ℝ) * higherSmooth (μ i) k ((k : ℝ) * r ^ 2) x| := by
        apply integral_mono (integrable_finset_sum _ (fun i _ ↦ hi i)).abs
          (integrable_finset_sum _ (fun i _ ↦ (hi i).abs))
        intro x
        exact Finset.abs_sum_le_sum_abs _ _
      _ = _ := by
        rw [integral_finset_sum _ (fun i _ ↦ (hi i).abs)]
        simp only [abs_mul, abs_of_nonneg (w _).coe_nonneg, integral_const_mul]
  unfold higherDetail
  simp_rw [he]
  have h := mul_le_mul_of_nonneg_left hL
    (by positivity [detailNormalization_pos] : 0 ≤ r ^ (2 * k) * detailNormalization ^ k)
  convert h using 1 <;> try rfl
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma detail_finiteMixture_le {I : Type*} [Fintype I]
    (w : I → ℝ≥0) (μ : I → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {r : ℝ} (hr : 0 < r) :
    detail (finiteMixture w μ) r ≤ ∑ i, (w i : ℝ) * detail (μ i) r := by
  have h := higherDetail_finiteMixture_le w μ (k := 1) (by norm_num) hr
  simpa only [higherDetail_one _ hr] using h

end LpSelfSimilar.Gaussian
