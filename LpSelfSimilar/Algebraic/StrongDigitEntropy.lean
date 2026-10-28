module

public import LpSelfSimilar.Algebraic.ContractingMatrixNormalization
public import LpSelfSimilar.Algebraic.MatrixDigitEntropy
public import LpSelfSimilar.Algebraic.UnitDigits
public import LpSelfSimilar.Gaussian.RankOneInformationComparison
public import LpSelfSimilar.Gaussian.BinaryInformationScaling
public import LpSelfSimilar.Gaussian.BinaryInformationDecoder

@[expose] public section

/-!
# Strong finite-digit entropy from canonical algebraic data

For algebraic units, the actual contracting-conjugate matrix, its normalized
covariance and the Gaussian axis comparison give a lower bound for every finite
word length by each scalar information gain. The proved scalar estimates supply
the constants 3/10 and 1/2. Nonunits have distinct words and exactly log(2)
entropy per digit. Thus the final bounds assume only a contracting algebraic
parameter; no entropy theorem, matrix construction or analytic estimate is an
input hypothesis. All entropies in this module use natural logarithms.
-/

open Real Matrix Polynomial MeasureTheory ProbabilityTheory
open scoped Classical MatrixOrder
open LpSelfSimilar.Bernoulli LpSelfSimilar.Entropy LpSelfSimilar.Gaussian

namespace LpSelfSimilar.Algebraic

/-- The canonical matrix supplies the full Gaussian comparison at each finite length. -/
theorem unit_digit_entropy_ge_binary_information {x : ℝ} (hx : IsAlgebraicUnit x)
    (hx0 : 0 < x) (hx1 : x < 1) (u : ℝ) (n : ℕ) :
    (n : ℝ) * (binaryGaussianInformation (u * mahlerMeasure x) - binaryGaussianInformation u) ≤
      finiteEntropy (digitPMF x n) (digitPMF_support_finite _ _) := by
  have ha : IsAlgebraic ℚ x := (hx.2.1.tower_top (A := ℚ)).isAlgebraic
  have hM : 0 < mahlerMeasure x := zero_lt_one.trans (one_lt_mahlerMeasure ha hx0 hx1)
  obtain ⟨U, w, hcov, hle, hpoly, hw, hvariance⟩ :=
    exists_normalized_contracting_unit_with_direction hx hx0 hx1
  obtain ⟨e, he, hgain⟩ := exists_axis_information_difference
    (↑U : Matrix (ContractingRootCoordinates x) (ContractingRootCoordinates x) ℝ)
    w hw hcov hM.ne' hvariance
  have h := digit_entropy_ge_matrix_information ha U hle hpoly (u • e) n
  rwa [hgain u] at h

/-- The coefficient 3/10 is uniform over all contracting algebraic units. -/
theorem unit_digit_entropy_three_tenths_lower {x : ℝ} (hx : IsAlgebraicUnit x)
    (hx0 : 0 < x) (hx1 : x < 1) (n : ℕ) :
    (n : ℝ) * ((3 / 10 : ℝ) * min 1 (log (mahlerMeasure x))) ≤
      finiteEntropy (digitPMF x n) (digitPMF_support_finite _ _) := by
  have ha : IsAlgebraic ℚ x := (hx.2.1.tower_top (A := ℚ)).isAlgebraic
  obtain ⟨u, hu, hgain⟩ := exists_binaryGaussianInformation_scaling_gain
    (one_lt_mahlerMeasure ha hx0 hx1).le
  exact (mul_le_mul_of_nonneg_left hgain (Nat.cast_nonneg n)).trans
    (unit_digit_entropy_ge_binary_information hx hx0 hx1 u n)

/-- At logarithmic Mahler measure at least two, one half is a valid entropy per digit. -/
theorem unit_digit_entropy_half_lower {x : ℝ} (hx : IsAlgebraicUnit x)
    (hx0 : 0 < x) (hx1 : x < 1) (hm : 2 ≤ log (mahlerMeasure x)) (n : ℕ) :
    (n : ℝ) * (1 / 2 : ℝ) ≤
      finiteEntropy (digitPMF x n) (digitPMF_support_finite _ _) := by
  have ha : IsAlgebraic ℚ x := (hx.2.1.tower_top (A := ℚ)).isAlgebraic
  have hM : 0 < mahlerMeasure x := zero_lt_one.trans (one_lt_mahlerMeasure ha hx0 hx1)
  have hscale : exp 2 ≤ mahlerMeasure x := by
    simpa only [exp_log hM] using exp_le_exp.mpr hm
  obtain ⟨u, hu, hgain⟩ := exists_binaryGaussianInformation_half_gain hscale
  exact (mul_le_mul_of_nonneg_left hgain (Nat.cast_nonneg n)).trans
    (unit_digit_entropy_ge_binary_information hx hx0 hx1 u n)

/-- Strong entropy at the canonical Mahler measure, including nonunits and length zero. -/
theorem digit_entropy_three_tenths_lower {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1) (n : ℕ) :
    (n : ℝ) * ((3 / 10 : ℝ) * min 1 (log (mahlerMeasure x))) ≤
      finiteEntropy (digitPMF x n) (digitPMF_support_finite _ _) := by
  by_cases hu : IsAlgebraicUnit x
  · exact unit_digit_entropy_three_tenths_lower hu hx0 hx1 n
  · rw [digit_entropy_of_not_isAlgebraicUnit hx0.ne' hu]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
    have hmin := min_le_left (1 : ℝ) (log (mahlerMeasure x))
    linarith [log_two_gt_d9]

/-- The stronger high-Mahler coefficient also holds for all contracting algebraic parameters. -/
theorem digit_entropy_half_lower {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1) (hm : 2 ≤ log (mahlerMeasure x)) (n : ℕ) :
    (n : ℝ) * (1 / 2 : ℝ) ≤
      finiteEntropy (digitPMF x n) (digitPMF_support_finite _ _) := by
  by_cases hu : IsAlgebraicUnit x
  · exact unit_digit_entropy_half_lower hu hx0 hx1 hm n
  · rw [digit_entropy_of_not_isAlgebraicUnit hx0.ne' hu]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
    linarith [log_two_gt_d9]

/-- The exact piecewise entropy coefficient, in nats, for the cubic criterion. -/
noncomputable def algebraicEntropyLowerBound (x : ℝ) : ℝ :=
  if log (mahlerMeasure x) < 2 then (3 / 10 : ℝ) * min 1 (log (mahlerMeasure x)) else 1 / 2

/-- Every finite digit law satisfies the exact piecewise entropy bound from algebraic hypotheses. -/
theorem digit_entropy_ge_algebraicEntropyLowerBound {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1) (n : ℕ) :
    (n : ℝ) * algebraicEntropyLowerBound x ≤
      finiteEntropy (digitPMF x n) (digitPMF_support_finite _ _) := by
  unfold algebraicEntropyLowerBound
  split_ifs with hm
  · exact digit_entropy_three_tenths_lower hx hx0 hx1 n
  · exact digit_entropy_half_lower hx hx0 hx1 (le_of_not_gt hm) n

theorem algebraicEntropyLowerBound_pos {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1) : 0 < algebraicEntropyLowerBound x := by
  have hm : 0 < log (mahlerMeasure x) := log_pos (one_lt_mahlerMeasure hx hx0 hx1)
  unfold algebraicEntropyLowerBound
  split_ifs
  · exact mul_pos (by norm_num) (lt_min zero_lt_one hm)
  · norm_num

theorem algebraicEntropyLowerBound_le_log_two (x : ℝ) :
    algebraicEntropyLowerBound x ≤ log 2 := by
  unfold algebraicEntropyLowerBound
  split_ifs
  · have hmin := min_le_left (1 : ℝ) (log (mahlerMeasure x))
    linarith [log_two_gt_d9]
  · linarith [log_two_gt_d9]

end LpSelfSimilar.Algebraic
