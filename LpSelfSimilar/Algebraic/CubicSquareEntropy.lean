module

public import LpSelfSimilar.Algebraic.CubicCriterionParameters
public import LpSelfSimilar.Algebraic.DegreeMahlerPowers

@[expose] public section

/-!
# Entropy strength after squaring the algebraic parameter

The logarithmic Mahler measure does not decrease on squaring. Consequently
the exact piecewise entropy coefficient at the squared parameter always
retains at least 3/10 times the original truncated logarithmic Mahler measure.
-/

open Real

namespace LpSelfSimilar.Algebraic

/-- The piecewise coefficient at the square retains the original entropy scale. -/
theorem algebraicEntropyLowerBound_square_ge {x : ℝ} (hx : IsAlgebraic ℚ x) :
    (3 / 10 : ℝ) * min 1 (log (mahlerMeasure x)) ≤ algebraicEntropyLowerBound (x ^ 2) := by
  unfold algebraicEntropyLowerBound
  split_ifs with hm
  · exact mul_le_mul_of_nonneg_left
      (min_le_min_left 1 (log_mahlerMeasure_le_pow hx (by decide : 0 < (2 : ℕ)))) (by norm_num)
  · have hs := min_le_left (1 : ℝ) (log (mahlerMeasure x))
    linarith

/-- The same retained scale expressed in bits. -/
theorem cubicEntropyBits_square_ge {x : ℝ} (hx : IsAlgebraic ℚ x) :
    3 * min 1 (log (mahlerMeasure x)) / (10 * log 2) ≤ cubicEntropyBits (x ^ 2) := by
  have h := div_le_div_of_nonneg_right (algebraicEntropyLowerBound_square_ge hx)
    (log_pos (by norm_num : (1 : ℝ) < 2)).le
  convert! h using 1 <;> ring

end LpSelfSimilar.Algebraic
