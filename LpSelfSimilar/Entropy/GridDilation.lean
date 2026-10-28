module

public import LpSelfSimilar.Entropy.GridVariance
public import LpSelfSimilar.Probability.ConditionalMomentTransform

@[expose] public section

/-!
Normalized conditional variance is invariant when a finite real law and its
observation mesh are dilated by the same positive factor. This transports the
rational block-variance estimates to the actual positions of digit blocks.
-/

open MeasureTheory

namespace LpSelfSimilar.Entropy

lemma quantize_dilation {c : ℝ} (hc : c ≠ 0) (s t x : ℝ) :
    quantize (c * s) t (c * x) = quantize s t x := by
  unfold quantize
  rw [mul_div_mul_left _ _ hc]

lemma gridVarianceAt_dilation (p : PMF ℝ) (hp : p.support.Finite)
    {c : ℝ} (hc : 0 < c) (s t : ℝ) :
    gridVarianceAt (p.map (fun x ↦ c * x))
      (by simpa using hp.image (fun x ↦ c * x)) (c * s) t = gridVarianceAt p hp s t := by
  have hq : quantize (c * s) t ∘ (fun x ↦ c * x) = quantize s t := by
    funext x
    exact quantize_dilation hc.ne' s t x
  unfold gridVarianceAt
  rw [FiniteProbability.meanConditionalVariance_map p hp (fun x ↦ c * x), hq]
  change FiniteProbability.meanConditionalVariance p hp (quantize s t) (fun x ↦ c * id x) /
    (c * s) ^ 2 = _
  rw [FiniteProbability.meanConditionalVariance_const_mul]
  rw [mul_pow, mul_div_mul_left _ _ (pow_ne_zero 2 hc.ne')]

/-- The exact scaling law for `V(X;s)`, including arbitrary mesh values. -/
theorem scaleVariance_dilation (p : PMF ℝ) (hp : p.support.Finite)
    {c : ℝ} (hc : 0 < c) (s : ℝ) :
    scaleVariance (p.map (fun x ↦ c * x))
      (by simpa using hp.image (fun x ↦ c * x)) (c * s) = scaleVariance p hp s := by
  unfold scaleVariance
  simp_rw [gridVarianceAt_dilation p hp hc]

end LpSelfSimilar.Entropy
