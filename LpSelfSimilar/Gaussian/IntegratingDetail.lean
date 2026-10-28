module

public import LpSelfSimilar.Gaussian.DetailDecay
public import LpSelfSimilar.Gaussian.DensityLimit
public import LpSelfSimilar.Gaussian.ApproximationBound

@[expose] public section

/-!
Lemma 3.4 of the paper, with an explicit absolute constant 200. Higher detail
first gives inverse-square logarithmic decay. Completeness supplies an L1 limit,
Gaussian approximate identity identifies its measure, and the weak-detail bound
controls the remaining scales. Absolute continuity is a conclusion.
-/

open MeasureTheory MeasureTheory.Measure Real Filter
open scoped Topology ENNReal

namespace LpSelfSimilar.Gaussian

/-- Integrating detail produces a nonnegative density and quantitative L1
approximation by smoothing at variance one (Lemma 3.4). -/
theorem integrating_detail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {R₀ δ : ℝ} (hR₀ : 100 ≤ R₀) (hδ : 0 < δ)
    (hhigh : ∀ R : ℝ, R₀ ≤ R → ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ 10 * log R →
      higherDetail μ k (exp (-R)) ≤ (1 / 100 : ℝ) ^ k)
    (hweak : ∀ r : ℝ, 0 < r → r ≤ 1 → detail μ r ≤ δ) :
    ∃ f : ℝ → ℝ, (∀ x, 0 ≤ f x) ∧ Integrable f volume ∧
      μ = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) ∧
      (∫ x, |f x - smooth μ 1 x|) ≤ 200 * (1 / R₀ + δ * R₀) := by
  have hR₀pos : 0 < R₀ := by linarith
  have hA : 0 < 100 * R₀ := by positivity
  have hdecay (R : ℝ) (hR : 100 * R₀ ≤ R) : detail μ (exp (-R)) ≤ 1 / R ^ 2 :=
    detail_exp_neg_le_inverse_sq μ hR₀ hhigh hR
  obtain ⟨f, hf, hf0, hlim⟩ := exists_smoothing_L1_limit μ hA hdecay
  have hseq : Tendsto (fun n : ℕ ↦ 100 * R₀ + (n : ℝ)) atTop atTop := by
    apply tendsto_atTop.2
    intro c
    obtain ⟨N, hN⟩ := exists_nat_ge (c - 100 * R₀)
    apply eventually_atTop.2
    refine ⟨N, ?_⟩
    intro n hn
    have hnR := Nat.cast_le (α := ℝ).mpr hn
    linarith
  have hr : Tendsto (fun n : ℕ ↦ exp (-(100 * R₀ + n))) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using tendsto_exp_neg_atTop_nhds_zero.comp hseq
  have heq := eq_withDensity_of_smoothing_L1_limit μ (fun n ↦ exp_pos _) hr hf hf0 hlim
  refine ⟨f, hf0, hf, heq, ?_⟩
  have happrox := smoothing_L1_limit_approximation μ hA hdecay hweak hf hlim
  have hQ : 2 / detailNormalization ≤ 2 := by
    apply (div_le_iff₀ detailNormalization_pos).mpr
    linarith [one_le_detailNormalization]
  have hi : 1 / (100 * R₀) ≤ 1 / R₀ :=
    one_div_le_one_div_of_le hR₀pos (by linarith)
  calc
    _ ≤ (2 / detailNormalization) * (1 / (100 * R₀) + δ * (100 * R₀)) := happrox
    _ ≤ 2 * (1 / (100 * R₀) + δ * (100 * R₀)) :=
      mul_le_mul_of_nonneg_right hQ (by positivity)
    _ ≤ 2 * (1 / R₀ + δ * (100 * R₀)) := by gcongr
    _ ≤ _ := by
      have hinv : 0 ≤ 1 / R₀ := by positivity
      nlinarith

end LpSelfSimilar.Gaussian
