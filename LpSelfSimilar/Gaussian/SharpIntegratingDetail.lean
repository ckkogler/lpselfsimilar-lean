module

public import LpSelfSimilar.Gaussian.SharpDetailDecay
public import LpSelfSimilar.Gaussian.ExactNormalization
public import LpSelfSimilar.Gaussian.DensityLimit
public import LpSelfSimilar.Gaussian.ApproximationBound

@[expose] public section

/-!
Revised Lemma 3.4, with the exact bound 4 delta R_0 + 1/(4 R_0), for R_0>=100.
The improved logarithmic threshold and Q>2 sharpen the existing complete L1
limit argument. Absolute continuity, a nonnegative density and the measure
identity are conclusions; no compact support or preliminary density is assumed.
-/

open MeasureTheory MeasureTheory.Measure Real Filter
open scoped Topology ENNReal

namespace LpSelfSimilar.Gaussian

/-- Integrating detail produces a nonnegative density and quantitative L1
approximation by smoothing at variance one (Lemma 3.4). -/
theorem integrating_detail_explicit (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {R₀ δ : ℝ} (hR₀ : 100 ≤ R₀) (hδ : 0 < δ)
    (hhigh : ∀ R : ℝ, R₀ ≤ R → ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ 10 * log R →
      higherDetail μ k (exp (-R)) ≤ (1 / 100 : ℝ) ^ k)
    (hweak : ∀ r : ℝ, 0 < r → r ≤ 1 → detail μ r ≤ δ) :
    ∃ f : ℝ → ℝ, (∀ x, 0 ≤ f x) ∧ Integrable f volume ∧
      μ = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) ∧
      (∫ x, |f x - smooth μ 1 x|) ≤ 4 * δ * R₀ + 1 / (4 * R₀) := by
  have hR₀pos : 0 < R₀ := by linarith
  have hA : 0 < 4 * R₀ := by positivity
  have hdecay (R : ℝ) (hR : 4 * R₀ ≤ R) : detail μ (exp (-R)) ≤ 1 / R ^ 2 :=
    detail_exp_neg_le_inverse_sq_sharp μ hR₀ hhigh hR
  obtain ⟨f, hf, hf0, hlim⟩ := exists_smoothing_L1_limit μ hA hdecay
  have hseq : Tendsto (fun n : ℕ ↦ 4 * R₀ + (n : ℝ)) atTop atTop := by
    apply tendsto_atTop.2
    intro c
    obtain ⟨N, hN⟩ := exists_nat_ge (c - 4 * R₀)
    apply eventually_atTop.2
    refine ⟨N, ?_⟩
    intro n hn
    have hnR := Nat.cast_le (α := ℝ).mpr hn
    linarith
  have hr : Tendsto (fun n : ℕ ↦ exp (-(4 * R₀ + n))) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using tendsto_exp_neg_atTop_nhds_zero.comp hseq
  have heq := eq_withDensity_of_smoothing_L1_limit μ (fun n ↦ exp_pos _) hr hf hf0 hlim
  refine ⟨f, hf0, hf, heq, ?_⟩
  have happrox := smoothing_L1_limit_approximation μ hA hdecay hweak hf hlim
  have hQ : 2 / detailNormalization ≤ 1 := by
    apply (div_le_iff₀ detailNormalization_pos).mpr
    linarith [two_lt_detailNormalization]
  calc
    _ ≤ (2 / detailNormalization) * (1 / (4 * R₀) + δ * (4 * R₀)) := happrox
    _ ≤ 1 * (1 / (4 * R₀) + δ * (4 * R₀)) :=
      mul_le_mul_of_nonneg_right hQ (by positivity)
    _ = _ := by ring

end LpSelfSimilar.Gaussian
