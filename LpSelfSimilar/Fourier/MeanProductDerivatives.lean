module

public import LpSelfSimilar.Analysis.WeightedProductDerivatives
public import LpSelfSimilar.Probability.ProductPMF

@[expose] public section

/-!
# A deterministic factor in averaged derivative estimates

A single fixed Fourier factor can be multiplied into a family averaged under an
actual finite label PMF. Averaging Leibniz terms adds the two derivative costs
and multiplies the majorants, with no loss in the second derivative.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace LpSelfSimilar.Fourier

/-- A fixed factor adds its derivative cost to the averaged family's cost. -/
theorem integral_norm_iteratedDeriv_mul_le {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (p : PMF Ω)
    (f : Ω → ℝ → ℂ) (g : ℝ → ℂ) {B E C D : ℝ}
    (hB : 0 ≤ B) (hE : 0 ≤ E) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (n : ℕ) (x : ℝ) (hf : ∀ a, ContDiffAt ℝ n (f a) x) (hg : ContDiffAt ℝ n g x)
    (hfb : ∀ j ≤ n, (∫ a, ‖iteratedDeriv j (f a) x‖ ∂p.toMeasure) ≤ C ^ j * B)
    (hgb : ∀ j ≤ n, ‖iteratedDeriv j g x‖ ≤ D ^ j * E) (k : ℕ) (hk : k ≤ n) :
    (∫ a, ‖iteratedDeriv k (fun y ↦ f a y * g y) x‖ ∂p.toMeasure) ≤
      (C + D) ^ k * (B * E) := by
  simp_rw [PMF.integral_eq_sum, smul_eq_mul] at hfb ⊢
  have h := Analysis.sum_norm_iteratedDeriv_mul_le
    (fun a ↦ (p a).toReal) (fun _ : Unit ↦ (1 : ℝ)) f (fun _ ↦ g)
    hB hE hC hD (fun a ↦ ENNReal.toReal_nonneg) (fun _ ↦ by norm_num)
    n x hf (fun _ ↦ hg) hfb (fun j hj ↦ by simpa using hgb j hj) k hk
  simpa only [Fintype.sum_unique, mul_one] using h

end LpSelfSimilar.Fourier
