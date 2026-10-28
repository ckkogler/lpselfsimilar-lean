module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Interchanging finite weighted sums and integrals

No pointwise bound on a summand is inferred from a mean bound. The exact finite
interchange lets later arguments integrate a weighted pointwise estimate.
-/

open MeasureTheory
open scoped BigOperators

namespace LpSelfSimilar.Analysis

/-- Exact interchange of a finite weighted sum and real integrals. -/
theorem sum_mul_integral_eq_integral_sum {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (f : ι → ℝ → ℝ) (hf : ∀ i, Integrable (f i)) :
    (∑ i, w i * ∫ x, f i x) = ∫ x, ∑ i, w i * f i x := by
  rw [integral_finsetSum Finset.univ (fun i hi ↦ (hf i).const_mul (w i))]
  simp only [integral_const_mul]

/-- Integrating a finite weighted norm bound retains its original weights. -/
theorem sum_mul_integral_norm_le {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (f : ι → ℝ → ℂ) {g : ℝ → ℝ}
    (hf : ∀ i, Integrable (f i)) (hg : Integrable g)
    (hb : ∀ x, (∑ i, w i * ‖f i x‖) ≤ g x) :
    (∑ i, w i * ∫ x, ‖f i x‖) ≤ ∫ x, g x := by
  rw [sum_mul_integral_eq_integral_sum w (fun i x ↦ ‖f i x‖) (fun i ↦ (hf i).norm)]
  exact integral_mono (integrable_finsetSum _ (fun i hi ↦ (hf i).norm.const_mul (w i))) hg hb

end LpSelfSimilar.Analysis
