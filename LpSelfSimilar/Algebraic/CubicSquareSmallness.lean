module

public import LpSelfSimilar.Algebraic.CubicScaleBounds
public import LpSelfSimilar.Algebraic.CubicSquareEntropy
public import LpSelfSimilar.Analysis.CubicSmallness
public import LpSelfSimilar.Bernoulli.PackingParameters

@[expose] public section

/-!
# The complete cubic packing smallness inequality

Canonical degree, Mahler measure, entropy and gap estimates supply all inputs
to the two real-variable branch bounds. The conclusion is exactly the
smallness inequality at the parameters L and rho used in Proposition 1.3,
with the original non-strict cubic hypothesis and no additional estimates.
-/

open Real
open LpSelfSimilar.Analysis LpSelfSimilar.Bernoulli

namespace LpSelfSimilar.Algebraic

/-- The canonical cubic hypothesis supplies the squared-parameter range and logarithmic gap. -/
theorem cubic_square_range_and_gap {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1)
    (hcubic : 1 - (min 1 (log (mahlerMeasure x)) / degreeMahlerScale x) ^ 3 ≤ x) :
    1 / 2 < x ^ 2 ∧ x ^ 2 < 1 ∧ -log (x ^ 2) < 1 / 250 := by
  obtain ⟨hs, hB3, hDB, hcube, hB8, hB11, hsB⟩ := cubic_hypothesis_scale_bounds hx hx0 hx1 hcubic
  have hθ := cubic_squared_parameter_mem (sub_pos.mpr hx1) hB8 hcube
  have hχ := cubic_squared_log_gap_lt_one_div_250 (sub_pos.mpr hx1) hB8 hcube
  simpa only [sub_sub_cancel] using And.intro hθ.1 (And.intro hθ.2 hχ)

/-- The complete smallness condition, with all canonical arithmetic and entropy inputs discharged. -/
theorem cubic_square_packing_smallness {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1)
    (hcubic : 1 - (min 1 (log (mahlerMeasure x)) / degreeMahlerScale x) ^ 3 ≤ x) :
    (-log (x ^ 2)) *
        packingLogScale (cubicSeparationBits (x ^ 2) / cubicEntropyBits (x ^ 2)) ^ 2 ≤
      cubicEntropyBits (x ^ 2) / 2 := by
  let s := min 1 (log (mahlerMeasure x))
  let B := degreeMahlerScale x / s
  let ρ := cubicEntropyBits (x ^ 2)
  let J := cubicSeparationBits (x ^ 2) / ρ
  have hdata := cubic_hypothesis_scale_bounds hx hx0 hx1 hcubic
  change 0 < s ∧ 3 ≤ B ∧ degreeMahlerScale x ≤ B ∧ (1 - x) * B ^ 3 ≤ 1 ∧
    8 < B ∧ (log (mahlerMeasure x) < 2 → 11 < B) ∧ 3 * log B / B ≤ s at hdata
  obtain ⟨hs, hB3, hDB, hcube, hB8, hB11, hsB⟩ := hdata
  have hB0 : 0 < B := by linarith
  have hg : 0 < 1 - x := sub_pos.mpr hx1
  have hθ := cubic_square_range_and_gap hx hx0 hx1 hcubic
  have hθ0 : 0 < x ^ 2 := by linarith [hθ.1]
  have halg : IsAlgebraic ℚ (x ^ 2) := isAlgebraic_pow hx 2
  have hρ0 : 0 < ρ := cubicEntropyBits_pos halg hθ0 hθ.2.1
  have hρ1 : ρ ≤ 1 := cubicEntropyBits_le_one _
  have hL : 3 ≤ cubicSeparationBits (x ^ 2) := three_le_cubicSeparationBits halg hθ.1 hθ.2.1
  have hJ1 : 1 ≤ J := (le_div_iff₀ hρ0).mpr (by linarith)
  have hJ : J = degreeMahlerScale (x ^ 2) / algebraicEntropyLowerBound (x ^ 2) :=
    cubicSeparationBits_div_cubicEntropyBits _
  have hpowers := square_degree_mahler_estimates hx
  have hD2 := hpowers.2.2.2.2
  have hBs : B * s = degreeMahlerScale x := div_mul_cancel₀ _ hs.ne'
  change (-log (x ^ 2)) * log (150 * J) ^ 2 ≤ ρ / 2
  by_cases hm : log (mahlerMeasure (x ^ 2)) < 2
  · have hmx : log (mahlerMeasure x) < 2 := hpowers.2.2.1.trans_lt hm
    have hJbound : J ≤ (20 / 3 : ℝ) * B := by
      rw [hJ]
      apply (div_le_iff₀ (algebraicEntropyLowerBound_pos halg hθ0 hθ.2.1)).mpr
      have hh := algebraicEntropyLowerBound_square_ge hx
      change (3 / 10 : ℝ) * s ≤ algebraicEntropyLowerBound (x ^ 2) at hh
      have hmul := mul_le_mul_of_nonneg_left hh (show 0 ≤ (20 / 3 : ℝ) * B by positivity)
      nlinarith
    have hrho : 3 * s / (10 * log 2) ≤ ρ := cubicEntropyBits_square_ge hx
    have h := cubic_low_branch_smallness hg (hB11 hmx) hs hcube hsB hJ1 hJbound hrho
    simpa only [sub_sub_cancel] using h.le
  · have hh : algebraicEntropyLowerBound (x ^ 2) = 1 / 2 := by
      unfold algebraicEntropyLowerBound
      rw [if_neg hm]
    have hJbound : J ≤ 4 * B := by rw [hJ, hh]; nlinarith
    have hrho : ρ = 1 / (2 * log 2) := by
      change algebraicEntropyLowerBound (x ^ 2) / log 2 = _
      rw [hh]
      ring
    have h := cubic_high_branch_smallness hg hB8 hcube hJ1 hJbound
    simp only [sub_sub_cancel] at h
    rw [hrho]
    convert! h.le using 1 <;> ring

end LpSelfSimilar.Algebraic
