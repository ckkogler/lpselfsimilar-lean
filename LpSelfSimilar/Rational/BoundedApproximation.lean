module

public import LpSelfSimilar.Rational.ApproximationConstants
public import LpSelfSimilar.Gaussian.IntegratingDetail
public import LpSelfSimilar.Gaussian.SmoothingBound

@[expose] public section

/-!
Bounded approximation for rational Bernoulli convolutions, the analytic part
of Proposition 3.1. Absolute continuity is proved from rational arithmetic and
Gaussian detail. The threshold is uniform after fixing the requested L1 error.
-/

open MeasureTheory Real
open LpSelfSimilar.Bernoulli LpSelfSimilar.Gaussian

namespace LpSelfSimilar.Rational

/-- An actual nonnegative density, close to a continuous function bounded by 1/2. -/
theorem bounded_density_approximation {η : ℝ} (hη : 0 < η)
    {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : a.Coprime b)
    (hl0 : 1 / 2 ≤ (a : ℝ) / b) (hl1 : (a : ℝ) / b < 1)
    (hsmall : -log ((a : ℝ) / b) * complexity b ^ 10 ≤ approximationThreshold η) :
    ∃ f f₀ : ℝ → ℝ, (∀ x, 0 ≤ f x) ∧ Integrable f volume ∧
      convolution ((a : ℝ) / b) = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) ∧
      Continuous f₀ ∧ Integrable f₀ volume ∧ (∀ x, 0 ≤ f₀ x ∧ f₀ x ≤ 1 / 2) ∧
      (∫ x, |f x - f₀ x|) ≤ η := by
  let l := (a : ℝ) / b
  let B := complexity b
  let R₀ := approximationScale η * B ^ 3
  let δ := weakSmoothingConstant * (-log l) ^ (1 / 3 : ℝ)
  have hB : 2 ≤ B := two_le_complexity hb
  have hB0 : 0 < B := complexity_pos hb
  have hB3 : 1 ≤ B ^ 3 := one_le_pow₀ (by linarith : 1 ≤ B)
  have hscale := approximationScale_ge η
  have hR₀ : 100 ≤ R₀ := by
    have h := mul_le_mul_of_nonneg_left hB3 (by linarith : 0 ≤ approximationScale η)
    dsimp [R₀]
    linarith
  have hl : 0 < l := by dsimp [l]; linarith
  have hχ : 0 < -log l := neg_pos.mpr (log_neg hl hl1)
  have hδ : 0 < δ := mul_pos weakSmoothingConstant_pos (rpow_pos_of_pos hχ _)
  have heff : -log l * complexity b ^ 10 ≤ effectiveDetailThreshold :=
    hsmall.trans (min_le_left _ _)
  have hhigh (R : ℝ) (hR : R₀ ≤ R) (k : ℕ) (hk : 1 ≤ k)
      (hkR : (k : ℝ) ≤ 10 * log R) :
      higherDetail (convolution l) k (exp (-R)) ≤ (1 / 100 : ℝ) ^ k := by
    apply effective_detail ha hb hab hl0 hl1 heff _ hk hkR
    exact (mul_le_mul_of_nonneg_right hscale (pow_nonneg hB0.le _)).trans hR
  obtain ⟨f, hf0, hf, heq, herr⟩ := integrating_detail (convolution l) hR₀ hδ hhigh
    (fun r hr hr1 ↦ weak_smoothing hl0 hl1 hr hr1)
  refine ⟨f, smooth (convolution l) 1, hf0, hf, heq,
    continuous_smooth_space _ (by norm_num), integrable_smooth _ (by norm_num), ?_, ?_⟩
  · intro x
    exact ⟨smooth_nonneg _ (by norm_num) _, smooth_one_le_half _ _⟩
  · exact herr.trans (approximation_error_bound hη hB hχ hsmall)

/-- Uniformity is explicit: fix the error, then choose one threshold before a,b. -/
theorem exists_uniform_bounded_approximation {η : ℝ} (hη : 0 < η) :
    ∃ c : ℝ, 0 < c ∧ ∀ a b : ℕ, 2 ≤ a → 2 ≤ b → a.Coprime b →
      1 / 2 ≤ (a : ℝ) / b → (a : ℝ) / b < 1 →
      -log ((a : ℝ) / b) * complexity b ^ 10 ≤ c →
      ∃ f f₀ : ℝ → ℝ, (∀ x, 0 ≤ f x) ∧ Integrable f volume ∧
        convolution ((a : ℝ) / b) = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) ∧
        Continuous f₀ ∧ Integrable f₀ volume ∧ (∀ x, 0 ≤ f₀ x ∧ f₀ x ≤ 1 / 2) ∧
        (∫ x, |f x - f₀ x|) ≤ η :=
  ⟨approximationThreshold η, approximationThreshold_pos hη,
    fun _ _ ha hb hab hl0 hl1 hs ↦ bounded_density_approximation hη ha hb hab hl0 hl1 hs⟩

end LpSelfSimilar.Rational
