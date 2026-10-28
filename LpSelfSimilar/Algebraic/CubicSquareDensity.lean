module

public import LpSelfSimilar.Algebraic.CubicSquareSmallness
public import LpSelfSimilar.Bernoulli.WorkingRegularityCriterion

@[expose] public section

/-!
# L2 density at the square under the cubic hypothesis

The canonical arithmetic proves every entropy, separation, cell-count and
smallness input of the complete working criterion. Its application gives an
actual nonnegative L2 density at the squared parameter, retaining the strict
Gaussian L1 error. Compact support is not an additional assumption.
-/

open MeasureTheory Real
open LpSelfSimilar.Bernoulli LpSelfSimilar.Gaussian

namespace LpSelfSimilar.Algebraic

/-- The full working regularity conclusion follows from the exact algebraic cubic hypothesis. -/
theorem cubic_square_density_with_gaussian_error {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1)
    (hcubic : 1 - (min 1 (log (mahlerMeasure x)) / degreeMahlerScale x) ^ 3 ≤ x) :
    ∃ f : ℝ → ℝ, Measurable f ∧ Integrable f volume ∧ (∀ y, 0 ≤ f y) ∧
      Bernoulli.convolution (x ^ 2) = volume.withDensity (fun y => ENNReal.ofReal (f y)) ∧
      MemLp f 2 volume ∧
      (∫ y : ℝ, |f y - kernel ((1 - (x ^ 2) ^ 2)⁻¹) y|) < 2 * (-log (x ^ 2)) := by
  have hθ := cubic_square_range_and_gap hx hx0 hx1 hcubic
  have hθ0 : 0 < x ^ 2 := by linarith [hθ.1]
  have halg : IsAlgebraic ℚ (x ^ 2) := isAlgebraic_pow hx 2
  exact working_regularity_criterion hθ.1 hθ.2.1 hθ.2.2.le
    (cubicEntropyBits_pos halg hθ0 hθ.2.1) (cubicEntropyBits_le_one _)
    (three_le_cubicSeparationBits halg hθ.1 hθ.2.1)
    (cubic_cell_log_bound halg hθ0 hθ.2.1)
    (cubic_square_packing_smallness hx hx0 hx1 hcubic)
    (fun n hn => digit_entropy_ge_cubicEntropyBits halg hθ0 hθ.2.1 n)
    (fun n hn a ha b hb hab => digitPMF_separation_cubicSeparationBits halg hθ0 hθ.2.1 n ha hb hab)

end LpSelfSimilar.Algebraic
