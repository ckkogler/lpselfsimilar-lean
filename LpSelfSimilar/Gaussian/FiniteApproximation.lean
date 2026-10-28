module

public import LpSelfSimilar.Probability.MapProbability

public import LpSelfSimilar.Gaussian.ConvolutionDetail
public import LpSelfSimilar.Analysis.FatouNorm
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-!
Almost-sure finite approximation of Gaussian detail. Boundedness of the first
Gaussian derivative gives pointwise convergence of its smoothed averages by
dominated convergence; Fatou then passes an upper bound to the limiting law.
No density or total-variation convergence of the laws is needed.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real Filter
open scoped Topology

namespace LpSelfSimilar.Gaussian

lemma tendsto_firstSmooth_map {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, Measurable (X n)) (hY : Measurable Y)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ X n ω) atTop (𝓝 (Y ω)))
    {y : ℝ} (hy : 0 < y) (x : ℝ) :
    Tendsto (fun n ↦ firstSmooth (P.map (X n)) y x) atTop
      (𝓝 (firstSmooth (P.map Y) y x)) := by
  have he (Z : Ω → ℝ) (hZ : Measurable Z) :
      firstSmooth (P.map Z) y x = ∫ ω, firstKernel y (x - Z ω) ∂P := by
    unfold firstSmooth averageTranslate
    rw [integral_map hZ.aemeasurable (by fun_prop)]
  simp_rw [he _ hY, he _ (hX _)]
  apply tendsto_integral_of_dominated_convergence
    (fun _ ↦ 3 / (2 * y) * (Real.sqrt (2 * Real.pi * y))⁻¹)
  · intro n
    exact ((continuous_firstKernel y).measurable.comp (measurable_const.sub (hX n))).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact ae_of_all _ (fun ω ↦ by simpa only [Real.norm_eq_abs] using abs_firstKernel_le hy (x - X n ω))
  · filter_upwards [hlim] with ω hω
    exact (continuous_firstKernel y).continuousAt.tendsto.comp (tendsto_const_nhds.sub hω)

lemma detail_map_le_of_tendsto {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, Measurable (X n)) (hY : Measurable Y)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ X n ω) atTop (𝓝 (Y ω)))
    {r : ℝ} (hr : 0 < r) {C : ℕ → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (hC : Tendsto C atTop (𝓝 c))
    (hb : ∀ n, detail (P.map (X n)) r ≤ C n) : detail (P.map Y) r ≤ c := by
  haveI (n : ℕ) : IsProbabilityMeasure (P.map (X n)) :=
    LpSelfSimilar.Probability.isProbabilityMeasure_map (hX n).aemeasurable
  haveI : IsProbabilityMeasure (P.map Y) := LpSelfSimilar.Probability.isProbabilityMeasure_map hY.aemeasurable
  let A := r ^ 2 * detailNormalization
  have hA : 0 ≤ A := mul_nonneg (sq_nonneg r) detailNormalization_pos.le
  have hi (n : ℕ) := (integrable_firstSmooth (P.map (X n)) (sq_pos_of_pos hr)).const_mul A
  have hf := (integrable_firstSmooth (P.map Y) (sq_pos_of_pos hr)).const_mul A
  have he (μ : Measure ℝ) : (∫ x, |A * firstSmooth μ (r ^ 2) x|) = detail μ r := by
    simp only [abs_mul, abs_of_nonneg hA, integral_const_mul]
    rfl
  have hh := integral_abs_le_of_tendsto hi hf
    (ae_of_all _ (fun x ↦ tendsto_const_nhds.mul
      (tendsto_firstSmooth_map P hX hY hlim (sq_pos_of_pos hr) x))) hc hC
    (fun n ↦ by rw [he]; exact hb n)
  rw [he] at hh
  exact hh

end LpSelfSimilar.Gaussian
