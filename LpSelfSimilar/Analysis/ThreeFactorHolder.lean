module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Tactic

@[expose] public section

/-!
Three-factor Hölder in weighted-power form. Nonnegative exponents summing to
one include the endpoint weights and require no finite-integral assumptions.
This is the reusable input to the Young convolution estimate.
-/

open MeasureTheory
open scoped ENNReal

namespace LpSelfSimilar

lemma lintegral_three_weighted_powers_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g h : X → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hh : AEMeasurable h μ) {u v w : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hsum : u + v + w = 1) :
    (∫⁻ x, f x ^ u * g x ^ v * h x ^ w ∂μ) ≤
      (∫⁻ x, f x ∂μ) ^ u * (∫⁻ x, g x ∂μ) ^ v * (∫⁻ x, h x ∂μ) ^ w := by
  have hm : ∀ i ∈ (Finset.univ : Finset (Fin 3)), AEMeasurable (![f, g, h] i) μ := by
    intro i _
    fin_cases i <;> assumption
  have he : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ (![u, v, w] i) := by
    intro i _
    fin_cases i <;> assumption
  have hs : ∑ i : Fin 3, (![u, v, w] i) = 1 := by simpa [Fin.sum_univ_succ, add_assoc] using hsum
  have hb := ENNReal.lintegral_prod_norm_pow_le (Finset.univ : Finset (Fin 3)) hm hs he
  simpa [Fin.prod_univ_succ, mul_assoc] using hb

end LpSelfSimilar
