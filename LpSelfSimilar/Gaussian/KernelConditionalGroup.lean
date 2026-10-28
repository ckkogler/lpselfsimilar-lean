module

public import LpSelfSimilar.Gaussian.KernelMixtureDetail
public import LpSelfSimilar.Gaussian.SharpShortIntervals
public import LpSelfSimilar.Probability.KernelConvolution
public import LpSelfSimilar.Probability.KernelVariance
public import LpSelfSimilar.Probability.VarianceConcentration

@[expose] public section

/-!
The one-group conditional-variance bound for general probability-kernel mixtures.
All support assumptions hold only almost everywhere in the conditioning space.
Independence and bounded variance give Chebyshev concentration; mixture convexity
and the sharp small-summand estimate give the exact revised paper constants.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real Set

namespace LpSelfSimilar.Gaussian

theorem conditional_kernel_group_detail_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (κ : Fin n → Kernel Ω ℝ) [∀ i, IsMarkovKernel (κ i)]
    (c : Fin n → Ω → ℝ) {ε r A : ℝ} (hε : 0 ≤ ε) (hr : 0 < r) (hA : 0 < A)
    (hb : ∀ i, ∀ᵐ ω ∂P, ∀ᵐ u ∂κ i ω, |u - c i ω| ≤ ε * r)
    (hind : iIndepFun (fun i ω ↦ variance (fun u : ℝ ↦ u) (κ i ω)) P)
    (hmass : A * r ^ 2 ≤ ∑ i, ∫ ω, variance (fun u : ℝ ↦ u) (κ i ω) ∂P) :
    detail (finiteConvolutionKernel κ ∘ₘ P) r ≤
      2 / A + (30 : ℝ) * ε + 4 * ε ^ 2 / A := by
  let W (i : Fin n) (ω : Ω) := variance (fun u : ℝ ↦ u) (κ i ω)
  let m := ∑ i, ∫ ω, W i ω ∂P
  let V (ω : Ω) := ∑ i, W i ω
  have hm : 0 < m := (mul_pos hA (sq_pos_of_pos hr)).trans_le hmass
  have hW (i : Fin n) : ∀ᵐ ω ∂P, W i ω ∈ Icc 0 ((ε * r) ^ 2) :=
    (hb i).mono (fun ω hω ↦ ⟨variance_nonneg _ _, variance_kernel_le_radius_sq (κ i) ω hω⟩)
  have hprob := probability_sum_lt_half_mean_le P W
    (fun i ↦ (stronglyMeasurable_variance_kernel (κ i)).measurable) hind (sq_nonneg (ε * r)) hW hm
  let E := {ω | V ω < m / 2}
  have hE : MeasurableSet E := measurableSet_lt
    (Finset.measurable_fun_sum _ (fun i _ ↦ (stronglyMeasurable_variance_kernel (κ i)).measurable))
    measurable_const
  have hpoint : ∀ᵐ ω ∂P, detail (finiteConvolution (fun i ↦ κ i ω)) r ≤
      (2 * r ^ 2 / m + (30 : ℝ) * ε) + E.indicator (fun _ ↦ 1) ω := by
    filter_upwards [ae_all_iff.2 hb] with ω hω
    by_cases he : ω ∈ E
    · rw [Set.indicator_of_mem he]
      have hn : 0 ≤ 2 * r ^ 2 / m + (30 : ℝ) * ε := by
        positivity
      exact (detail_le_one _ hr).trans (by linarith)
    · rw [Set.indicator_of_notMem he]
      have hV : m / 2 ≤ V ω := le_of_not_gt he
      have hs := small_summands_intervals_explicit (fun i ↦ κ i ω) (fun i ↦ c i ω) hε hr hω
      have hv : 0 ≤ V ω := Finset.sum_nonneg (fun i _ ↦ variance_nonneg _ _)
      have hf : r ^ 2 / (r ^ 2 + V ω) ≤ 2 * r ^ 2 / m := by
        apply (div_le_div_iff₀ (by positivity : 0 < r ^ 2 + V ω) hm).2
        nlinarith [mul_le_mul_of_nonneg_left hV (sq_nonneg r)]
      change detail (finiteConvolution (fun i ↦ κ i ω)) r ≤ r ^ 2 / (r ^ 2 + V ω) + _ at hs
      linarith
  have hconv := detail_kernel_comp_le P (finiteConvolutionKernel κ) hr
  simp only [finiteConvolutionKernel_apply] at hconv
  have hdetail : Integrable (fun ω ↦ detail (finiteConvolution (fun i ↦ κ i ω)) r) P := by
    simpa only [higherDetail_one _ hr, finiteConvolutionKernel_apply] using
      integrable_higherDetail_kernel P (finiteConvolutionKernel κ) (k := 1) (by norm_num) hr
  have hi := integral_mono_ae hdetail
    ((integrable_const _).add ((integrable_const (1 : ℝ)).indicator hE)) hpoint
  have he : (∫ ω, (2 * r ^ 2 / m + (30 : ℝ) * ε) +
      E.indicator (fun _ ↦ 1) ω ∂P) =
      2 * r ^ 2 / m + (30 : ℝ) * ε + P.real E := by
    rw [integral_add (integrable_const _) ((integrable_const (1 : ℝ)).indicator hE), integral_const]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    congr 1
    exact integral_indicator_one (μ := P) hE
  simp only [Pi.add_apply] at hi
  rw [he] at hi
  have h1 : 2 * r ^ 2 / m ≤ 2 / A := by
    apply (div_le_div_iff₀ hm hA).2
    nlinarith [hmass]
  have h2 : 4 * (ε * r) ^ 2 / m ≤ 4 * ε ^ 2 / A := by
    apply (div_le_div_iff₀ hm hA).2
    nlinarith [mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ 4 * ε ^ 2)]
  exact hconv.trans (hi.trans (by
    change _ ≤ _
    change P.real E ≤ 4 * (ε * r) ^ 2 / m at hprob
    linarith))

/-- The exact one-group choice in revised Lemma 3.3: epsilon_0=10^-4. -/
theorem conditional_kernel_group_detail_le_one_hundredth {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (κ : Fin n → Kernel Ω ℝ) [∀ i, IsMarkovKernel (κ i)] (c : Fin n → Ω → ℝ)
    {r : ℝ} (hr : 0 < r)
    (hb : ∀ i, ∀ᵐ ω ∂P, ∀ᵐ u ∂κ i ω, |u - c i ω| ≤ (1 / 10000 : ℝ) * r)
    (hind : iIndepFun (fun i ω ↦ variance (fun u : ℝ ↦ u) (κ i ω)) P)
    (hmass : 1000 * r ^ 2 ≤ ∑ i, ∫ ω, variance (fun u : ℝ ↦ u) (κ i ω) ∂P) :
    detail (finiteConvolutionKernel κ ∘ₘ P) r ≤ 1 / 100 := by
  apply (conditional_kernel_group_detail_le P κ c (ε := 1 / 10000) (A := 1000)
    (by norm_num) hr (by norm_num) hb hind hmass).trans
  norm_num

end LpSelfSimilar.Gaussian
