module

public import LpSelfSimilar.Algebraic.EffectiveDetail
public import LpSelfSimilar.Algebraic.ApproximationConstants
public import LpSelfSimilar.Bernoulli.SharpWeakSmoothing
public import LpSelfSimilar.Gaussian.SharpIntegratingDetail
public import LpSelfSimilar.Gaussian.SmoothingBound

@[expose] public section

/-!
The bounded approximation (3.2) for all algebraic parameters under the revised
explicit threshold. Absolute continuity and the representing density follow from
integrating detail; the Gaussian smoothing is nonnegative and bounded by 1/2.
-/

open MeasureTheory Real
open LpSelfSimilar.Bernoulli LpSelfSimilar.Gaussian

namespace LpSelfSimilar.Algebraic

/-- The complete bounded approximation required in the reduction of Proposition 3.1. -/
theorem bounded_density_approximation {l : ℝ} (hlalg : IsAlgebraic ℚ l)
    (hl0 : 1 / 2 < l) (hl1 : l < 1)
    (hsmall : -log l * complexity l ^ 10 ≤ 1 / (10 : ℝ) ^ 100) :
    ∃ f f₀ : ℝ → ℝ, (∀ x, 0 ≤ f x) ∧ Integrable f volume ∧
      convolution l = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) ∧
      Continuous f₀ ∧ Integrable f₀ volume ∧ (∀ x, 0 ≤ f₀ x ∧ f₀ x ≤ 1 / 2) ∧
      (∫ x, |f x - f₀ x|) ≤ 1 / (2 * 21 ^ 2) := by
  let B := complexity l
  let R₀ := (10 : ℝ) ^ 6 * B ^ 3
  let δ := 40 * (-log l) ^ (1 / 3 : ℝ)
  have hl : 0 < l := by linarith
  have hB : 3 ≤ B := three_le_complexity hlalg hl hl1
  have hB0 : 0 < B := by linarith
  have hB3 : 1 ≤ B ^ 3 := one_le_pow₀ (by linarith : 1 ≤ B)
  have hR₀ : 100 ≤ R₀ := by dsimp [R₀]; nlinarith
  have hχ : 0 < -log l := neg_pos.mpr (log_neg hl hl1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hhigh (R : ℝ) (hR : R₀ ≤ R) (k : ℕ) (hk : 1 ≤ k)
      (hkR : (k : ℝ) ≤ 10 * log R) :
      higherDetail (convolution l) k (exp (-R)) ≤ (1 / 100 : ℝ) ^ k :=
    effective_detail hlalg hl0.le hl1 hsmall hR hk hkR
  obtain ⟨f, hf0, hf, heq, herr⟩ := integrating_detail_explicit (convolution l)
    hR₀ hδ hhigh (fun r hr hr1 ↦ weak_smoothing_explicit hl0 hl1 hr hr1)
  refine ⟨f, smooth (convolution l) 1, hf0, hf, heq,
    continuous_smooth_space _ (by norm_num), integrable_smooth _ (by norm_num), ?_, ?_⟩
  · intro x
    exact ⟨smooth_nonneg _ (by norm_num) _, smooth_one_le_half _ _⟩
  · apply herr.trans
    have h := approximation_error_bound hB hχ hsmall
    convert h using 1 <;> first | rfl | (dsimp [δ, R₀]; ring)

end LpSelfSimilar.Algebraic
