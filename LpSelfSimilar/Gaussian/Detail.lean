module

public import LpSelfSimilar.Gaussian.Moments
public import LpSelfSimilar.Analysis.MeasureConvolution

@[expose] public section

/-!
Ordinary Gaussian detail, normalized exactly as in Section 3. This module
establishes the universal bound, the point-mass normalization and translation
invariance. The convolution against a measure is a Bochner integral of the
actual first variance derivative, not a separately postulated smoothing operator.
-/

open MeasureTheory MeasureTheory.Measure Real

namespace LpSelfSimilar.Gaussian

/-- The ordinary detail `s_r(μ)` of Section 3. -/
noncomputable def detail (μ : Measure ℝ) (r : ℝ) : ℝ :=
  r ^ 2 * detailNormalization * ∫ x, |averageTranslate μ (firstKernel (r ^ 2)) x|

lemma detail_nonneg (μ : Measure ℝ) (r : ℝ) : 0 ≤ detail μ r := by
  unfold detail
  exact mul_nonneg (mul_nonneg (sq_nonneg r) detailNormalization_pos.le)
    (integral_nonneg (fun _ ↦ abs_nonneg _))

/-- The ordinary case of the universal bound in (3.4). -/
lemma detail_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r) :
    detail μ r ≤ 1 := by
  have hn := integral_abs_averageTranslate_le μ (continuous_firstKernel (r ^ 2))
    (integrable_firstKernel (by positivity : 0 < r ^ 2))
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_mul] at hn
  calc
    detail μ r ≤ r ^ 2 * detailNormalization * ∫ x, |firstKernel (r ^ 2) x| :=
      mul_le_mul_of_nonneg_left hn (mul_nonneg (sq_nonneg r) detailNormalization_pos.le)
    _ = 1 := normalized_firstKernel_norm hr

lemma detail_dirac (a : ℝ) {r : ℝ} (hr : 0 < r) : detail (dirac a) r = 1 := by
  unfold detail averageTranslate
  simp only [integral_dirac]
  rw [integral_sub_right_eq_self (fun x ↦ |firstKernel (r ^ 2) x|)]
  exact normalized_firstKernel_norm hr

/-- Translating a measure does not change its detail. -/
lemma detail_map_add (μ : Measure ℝ) (r a : ℝ) :
    detail (μ.map (fun x ↦ x + a)) r = detail μ r := by
  have hinner (x : ℝ) : averageTranslate (μ.map (fun z ↦ z + a)) (firstKernel (r ^ 2)) x =
      averageTranslate μ (firstKernel (r ^ 2)) (x - a) := by
    unfold averageTranslate
    rw [integral_map (by fun_prop) (by fun_prop)]
    congr 1
    ext z
    congr 1
    ring
  unfold detail
  simp_rw [hinner]
  rw [integral_sub_right_eq_self (fun x ↦ |averageTranslate μ (firstKernel (r ^ 2)) x|)]

end LpSelfSimilar.Gaussian
