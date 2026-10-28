module

public import LpSelfSimilar.Entropy.GridDisagreement
public import LpSelfSimilar.Entropy.GridBounds
public import LpSelfSimilar.Analysis.SqrtAverages

@[expose] public section

/-!
Entropy-to-variance within a single coarse interval. A grid four times finer
has at most five atoms. The collision estimate and Jensen's inequality give
the fourth-root variance bound with the paper's constant ten.
-/

open MeasureTheory Set Real

namespace LpSelfSimilar.Entropy

lemma gridEntropy_le_four_sqrt_variance (p : PMF ℝ) (hp : p.support.Finite)
    {A B s : ℝ} (hAB : p.support ⊆ Icc A B) (hs : 0 < s) (hlen : B - A ≤ 4 * s) :
    gridEntropy p hp s ≤ 4 * Real.sqrt (Real.sqrt (2 * FiniteProbability.variance p hp id) / s) := by
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  letI : IsProbabilityMeasure μ := ⟨by simp [μ]⟩
  let D (t : ℝ) :=
    1 - collisionProbability (p.map (quantize s t)) (by simpa using hp.image (quantize s t))
  have hn (t : ℝ) : 0 ≤ D t := sub_nonneg.mpr (collisionProbability_le_one _ _)
  have hi : Integrable D μ := integrable_grid_disagreement p hp s
  have hroot := integrable_sqrt_of_nonneg hi (ae_of_all _ hn)
  have he (t : ℝ) : gridEntropyAt p hp s t ≤ 4 * Real.sqrt (D t) := by
    apply finiteEntropy_le_four_sqrt_disagreement
    exact grid_card_le_of_length_le_nat p hp hAB hs 4 hlen t
  calc
    gridEntropy p hp s ≤ ∫ t, 4 * Real.sqrt (D t) ∂μ :=
      integral_mono (integrable_gridEntropyAt p hp s) (hroot.const_mul 4) he
    _ = 4 * ∫ t, Real.sqrt (D t) ∂μ := integral_const_mul _ _
    _ ≤ 4 * Real.sqrt (∫ t, D t ∂μ) :=
      mul_le_mul_of_nonneg_left (integral_sqrt_le_sqrt_integral hi (ae_of_all _ hn)) (by norm_num)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.sqrt_le_sqrt (integral_grid_disagreement_le p hp hs)

/-- The one-cell estimate used in Lemma 3.5, with exactly the constant ten. -/
lemma fine_gridEntropy_le_ten_fourthRoot_variance (p : PMF ℝ) (hp : p.support.Finite)
    {A B s : ℝ} (hAB : p.support ⊆ Icc A B) (hs : 0 < s) (hlen : B - A ≤ s) :
    gridEntropy p hp (s / 4) ≤
      10 * Real.sqrt (Real.sqrt (FiniteProbability.variance p hp id / s ^ 2)) := by
  apply (gridEntropy_le_four_sqrt_variance p hp hAB (by positivity : 0 < s / 4)
    (by linarith)).trans
  exact four_sqrt_sqrt_div_quarter_le (FiniteProbability.variance_nonneg p hp id) hs

end LpSelfSimilar.Entropy
