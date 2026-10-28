module

public import LpSelfSimilar.Algebraic.StrongDigitEntropy
public import LpSelfSimilar.Algebraic.DegreeMahlerScale

@[expose] public section

/-!
# Canonical entropy and separation parameters in bits

The natural-logarithm entropy and separation estimates convert to the precise
parameters used by the working regularity criterion. The gap bound alone gives
L>=3 for parameters above one half, uniformly over all algebraic degrees.
Actual PMF support values are lifted to words before applying separation.
-/

open Real Set
open LpSelfSimilar.Bernoulli LpSelfSimilar.Entropy

namespace LpSelfSimilar.Algebraic

/-- Separation exponent in base two, using the canonical degree--Mahler scale. -/
noncomputable def cubicSeparationBits (x : ℝ) : ℝ := degreeMahlerScale x / log 2

/-- Guaranteed entropy per digit in bits, using the exact piecewise coefficient. -/
noncomputable def cubicEntropyBits (x : ℝ) : ℝ := algebraicEntropyLowerBound x / log 2

theorem cubicEntropyBits_pos {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1) : 0 < cubicEntropyBits x :=
  div_pos (algebraicEntropyLowerBound_pos hx hx0 hx1) (log_pos (by norm_num))

theorem cubicEntropyBits_le_one (x : ℝ) : cubicEntropyBits x ≤ 1 := by
  apply (div_le_one (log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  exact algebraicEntropyLowerBound_le_log_two x

/-- The gap estimate proves L>=3 without a separate rational-parameter case. -/
theorem three_le_cubicSeparationBits {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hxhalf : 1 / 2 < x) (hx1 : x < 1) : 3 ≤ cubicSeparationBits x := by
  have hx0 : 0 < x := by linarith
  have hg : 0 < 1 - x := sub_pos.mpr hx1
  have htwo : (2 : ℝ) ≤ 1 / (1 - x) := (le_div_iff₀ hg).mpr (by linarith)
  have hl := log_le_log (by norm_num : (0 : ℝ) < 2) htwo
  have hgap := log_inverse_gap_le_degree_mahler hx hx0 hx1
  have hd : (1 : ℝ) ≤ algebraicDegree x := by exact_mod_cast algebraicDegree_pos hx
  have hlog : log (2 : ℝ) < 1 := by linarith [log_two_lt_d9]
  have hm := mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr hlog.le)
  apply (le_div_iff₀ (log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  unfold degreeMahlerScale
  nlinarith

/-- The normalized entropy/separation ratio is exactly D/h. -/
theorem cubicSeparationBits_div_cubicEntropyBits (x : ℝ) :
    cubicSeparationBits x / cubicEntropyBits x = degreeMahlerScale x / algebraicEntropyLowerBound x := by
  unfold cubicSeparationBits cubicEntropyBits
  field_simp

/-- Every finite digit law has the required entropy bound in bits. -/
theorem digit_entropy_ge_cubicEntropyBits {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1) (n : ℕ) :
    cubicEntropyBits x * n ≤ finiteEntropy (digitPMF x n) (digitPMF_support_finite _ _) / log 2 := by
  calc
    _ = ((n : ℝ) * algebraicEntropyLowerBound x) / log 2 := by unfold cubicEntropyBits; ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (digit_entropy_ge_algebraicEntropyLowerBound hx hx0 hx1 n) (log_pos (by norm_num)).le

/-- The base-two exponential is exactly the natural exponential used by separation. -/
theorem cubicSeparationBits_rpow (x : ℝ) (n : ℕ) :
    (2 : ℝ) ^ (-(cubicSeparationBits x * n)) = exp (-degreeMahlerScale x * n) := by
  rw [rpow_def_of_pos (by norm_num)]
  congr 1
  unfold cubicSeparationBits
  field_simp
  <;> ring

/-- Distinct values of the actual finite digit law satisfy the required base-two separation. -/
theorem digitPMF_separation_cubicSeparationBits {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1) (n : ℕ)
    {a b : ℝ} (ha : a ∈ (digitPMF x n).support) (hb : b ∈ (digitPMF x n).support)
    (hab : a ≠ b) : (2 : ℝ) ^ (-(cubicSeparationBits x * n)) ≤ |a - b| := by
  rw [digitPMF, PMF.support_map] at ha hb
  obtain ⟨u, hu, rfl⟩ := ha
  obtain ⟨v, hv, rfl⟩ := hb
  rw [cubicSeparationBits_rpow]
  exact (digitSum_separation_degree_mahler_scale hx hx0 hx1 hab).le

/-- The cell-count logarithm in the working criterion has the required upper bound. -/
theorem cubic_cell_log_bound {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1) :
    log (2 / (1 - x) + 2) / log 2 ≤ cubicSeparationBits x + 2 := by
  have hg : 0 < 1 - x := sub_pos.mpr hx1
  have hden : 2 / (1 - x) + 2 ≤ 4 / (1 - x) := by
    apply (le_div_iff₀ hg).mpr
    field_simp
    nlinarith
  have hlog := log_le_log (by positivity : 0 < 2 / (1 - x) + 2) hden
  have hgap := log_inverse_gap_le_degree_mahler hx hx0 hx1
  have hd : (1 : ℝ) ≤ algebraicDegree x := by exact_mod_cast algebraicDegree_pos hx
  have hlog2 : log (2 : ℝ) ≤ 1 := by linarith [log_two_lt_d9]
  have hcost := mul_le_mul_of_nonneg_left hlog2 (sub_nonneg.mpr hd)
  have he : log (4 / (1 - x)) = 2 * log 2 + log (1 / (1 - x)) := by
    rw [log_div (by norm_num) hg.ne', log_div one_ne_zero hg.ne', log_one, log_four_eq]
    ring
  rw [he] at hlog
  apply (div_le_iff₀ (log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  unfold cubicSeparationBits
  rw [add_mul, div_mul_cancel₀ _ (log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  unfold degreeMahlerScale
  nlinarith

end LpSelfSimilar.Algebraic
