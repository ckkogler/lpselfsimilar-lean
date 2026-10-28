module

public import LpSelfSimilar.Gaussian.HigherSemigroup
public import LpSelfSimilar.Analysis.ConvolutionFactorization
public import LpSelfSimilar.Probability.FiniteConvolutionLaws

@[expose] public section

/-!
The higher-detail product inequality and universal bound, equation (3.4).
The factorization uses actual higher Gaussian derivatives, proved in
HigherSemigroup, and the real function-convolution L1 inequality.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real

namespace LpSelfSimilar.Gaussian

lemma higherSmooth_conv (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (k l : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    higherSmooth (μ ∗ ν) (k + l) (a + b) x =
      functionConvolution (higherSmooth μ k a) (higherSmooth ν l b) x := by
  obtain ⟨C, _, hC⟩ := exists_uniform_bound_higherKernel k ha
  obtain ⟨D, _, hD⟩ := exists_uniform_bound_higherKernel l hb
  have he : higherKernel (k + l) (a + b) =
      functionConvolution (higherKernel k a) (higherKernel l b) :=
    funext (fun z ↦ (functionConvolution_higherKernel k l ha hb z).symm)
  unfold higherSmooth
  rw [he]
  exact averageTranslate_conv_functionConvolution μ ν
    (continuous_higherKernel_space k a) (integrable_higherKernel k ha) (hC a le_rfl)
    (continuous_higherKernel_space l b) (integrable_higherKernel l hb) (hD b le_rfl) x

lemma higherDetail_conv_le (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {k l : ℕ} (hk : 0 < k) (hl : 0 < l) {r : ℝ} (hr : 0 < r) :
    higherDetail (μ ∗ ν) (k + l) r ≤ higherDetail μ k r * higherDetail ν l r := by
  have ha : 0 < (k : ℝ) * r ^ 2 := by positivity
  have hb : 0 < (l : ℝ) * r ^ 2 := by positivity
  have h := integral_abs_functionConvolution_le
    (continuous_higherSmooth_space μ k ha) (integrable_higherSmooth μ k ha)
    (continuous_higherSmooth_space ν l hb) (integrable_higherSmooth ν l hb)
  have hm := mul_le_mul_of_nonneg_left h
    (by positivity [detailNormalization_pos] : 0 ≤ r ^ (2 * (k + l)) * detailNormalization ^ (k + l))
  unfold higherDetail
  rw [Nat.cast_add, add_mul]
  simp_rw [higherSmooth_conv μ ν k l ha hb]
  convert hm using 1 <;> try rfl
  rw [Nat.mul_add, pow_add, pow_add]
  ring

/-- The universal bound in (3.4), proved by splitting off Gaussian derivatives. -/
theorem higherDetail_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {k : ℕ} (hk : 0 < k) {r : ℝ} (hr : 0 < r) : higherDetail μ k r ≤ 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  induction n with
  | zero => simpa only [zero_add, higherDetail_one μ hr] using detail_le_one μ hr
  | succ n ih =>
    have h := higherDetail_conv_le μ (dirac 0) (k := n + 1) (l := 1) (Nat.succ_pos n) (by norm_num) hr
    rw [Measure.conv_dirac_zero, higherDetail_one _ hr, detail_dirac _ hr, mul_one] at h
    exact h.trans (ih (Nat.succ_pos n))

lemma higherDetail_conv_le_right (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℕ} (hk : 0 < k)
    {r : ℝ} (hr : 0 < r) : higherDetail (μ ∗ ν) k r ≤ higherDetail ν k r := by
  have hy : 0 < (k : ℝ) * r ^ 2 := by positivity
  obtain ⟨C, _, hb⟩ := exists_uniform_bound_higherKernel k hy
  have he (x : ℝ) : higherSmooth (μ ∗ ν) k ((k : ℝ) * r ^ 2) x =
      averageTranslate μ (higherSmooth ν k ((k : ℝ) * r ^ 2)) x :=
    averageTranslate_conv μ ν (continuous_higherKernel_space k _) (hb _ le_rfl) x
  have h := integral_abs_averageTranslate_le μ
    (continuous_higherSmooth_space ν k hy) (integrable_higherSmooth ν k hy)
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_mul] at h
  unfold higherDetail
  simp_rw [he]
  exact mul_le_mul_of_nonneg_left h (by positivity [detailNormalization_pos])

/-- The finite product bound in (3.4). -/
theorem higherDetail_finiteConvolution_le {n : ℕ} (μ : Fin (n + 1) → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] {r : ℝ} (hr : 0 < r) :
    higherDetail (finiteConvolution μ) (n + 1) r ≤ ∏ i, detail (μ i) r := by
  induction n with
  | zero =>
    simp only [finiteConvolution, Measure.conv_dirac_zero, higherDetail_one _ hr]
    exact (Fin.prod_univ_one (fun i : Fin 1 ↦ detail (μ i) r)).ge
  | succ n ih =>
    let μt := fun j : Fin (n + 1) ↦ μ j.succ
    have h := higherDetail_conv_le (μ 0) (finiteConvolution μt)
      (by norm_num : 0 < 1) (Nat.succ_pos n) hr
    rw [higherDetail_one _ hr] at h
    have ht := ih μt
    rw [finiteConvolution, Fin.prod_univ_succ]
    have he : 1 + (n + 1) = n + 1 + 1 := by omega
    rw [he] at h
    exact h.trans (mul_le_mul_of_nonneg_left ht (detail_nonneg _ _))

end LpSelfSimilar.Gaussian
