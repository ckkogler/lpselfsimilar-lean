module

public import LpSelfSimilar.Gaussian.SmoothingMeasure
public import LpSelfSimilar.Gaussian.AbsoluteMoments
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.Group.IntegralConvolution
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-!
Gaussian smoothing tends weakly to the original finite measure. The proof uses
the actual Gaussian scaling identity and two dominated-convergence arguments
against bounded continuous test functions. It requires no density of the measure.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction

namespace LpSelfSimilar.Gaussian

lemma integral_bounded_test_smooth (μ : Measure ℝ) [IsFiniteMeasure μ]
    (φ : ℝ →ᵇ ℝ) {r : ℝ} (hr : 0 < r) :
    (∫ x, φ x * smooth μ (r ^ 2) x) =
      ∫ z, (∫ w, φ (z + r * w) ∂gaussianReal 0 1) ∂μ := by
  let v : ℝ≥0 := ⟨r ^ 2, sq_nonneg r⟩
  have hg : gaussianReal 0 v = (gaussianReal 0 1).map (fun w ↦ r * w) := by
    rw [gaussian_eq_map_scaled_unit]
    have hs : sqrt (v : ℝ) = r := by
      change sqrt (r ^ 2) = r
      exact sqrt_sq hr.le
    simp only [hs]
  have hd : μ ∗ gaussianReal 0 v =
      volume.withDensity (fun x ↦ ENNReal.ofReal (smooth μ (r ^ 2) x)) :=
    convolution_gaussian_eq_withDensity μ (sq_pos_of_pos hr)
  have ht : (∫ x, φ x ∂μ ∗ gaussianReal 0 v) = ∫ x, φ x * smooth μ (r ^ 2) x := by
    rw [hd, integral_withDensity_eq_integral_toReal_smul
      (continuous_smooth_space μ (sq_pos_of_pos hr)).measurable.ennreal_ofReal
      (ae_of_all _ (fun x ↦ ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (smooth_nonneg μ (sq_pos_of_pos hr) _), smul_eq_mul]
    congr 1
    funext x
    ring
  rw [← ht, integral_conv (φ.integrable (μ ∗ gaussianReal 0 v))]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  dsimp only
  rw [hg, integral_map (by fun_prop) (by fun_prop)]

/-- Weak Gaussian approximation, stated with ordinary integrals of the actual
smoothed density against every bounded continuous real test function. -/
theorem tendsto_integral_bounded_test_smooth (μ : Measure ℝ) [IsFiniteMeasure μ]
    (φ : ℝ →ᵇ ℝ) {r : ℕ → ℝ} (hr : ∀ n, 0 < r n)
    (hlim : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x, φ x * smooth μ ((r n) ^ 2) x) atTop
      (𝓝 (∫ x, φ x ∂μ)) := by
  simp_rw [integral_bounded_test_smooth μ φ (hr _)]
  have hm (n : ℕ) : Measurable (fun p : ℝ × ℝ ↦ φ (p.1 + r n * p.2)) := by
    fun_prop
  have hb (n : ℕ) (z : ℝ) : ‖∫ w, φ (z + r n * w) ∂gaussianReal 0 1‖ ≤ ‖φ‖ := by
    have hh := norm_integral_le_of_norm_le_const (μ := gaussianReal 0 1)
      (ae_of_all _ (fun w ↦ φ.norm_coe_le_norm (z + r n * w)))
    simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, one_mul, mul_one] using hh
  apply tendsto_integral_of_dominated_convergence (fun _ ↦ ‖φ‖)
  · intro n
    exact (hm n).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  · exact integrable_const _
  · exact fun n ↦ ae_of_all _ (hb n)
  · apply ae_of_all
    intro z
    have ht : Tendsto (fun n ↦ ∫ w, φ (z + r n * w) ∂gaussianReal 0 1) atTop
        (𝓝 (∫ _w : ℝ, φ z ∂gaussianReal 0 1)) := by
      apply tendsto_integral_of_dominated_convergence (fun _ ↦ ‖φ‖)
      · intro n
        fun_prop
      · exact integrable_const _
      · exact fun n ↦ ae_of_all _ (fun w ↦ φ.norm_coe_le_norm _)
      · apply ae_of_all
        intro w
        have ht : Tendsto (fun n ↦ z + r n * w) atTop (𝓝 z) := by
          simpa only [zero_mul, add_zero] using (hlim.mul_const w).const_add z
        exact φ.continuous.continuousAt.tendsto.comp ht
    simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
      one_smul] using ht

end LpSelfSimilar.Gaussian
