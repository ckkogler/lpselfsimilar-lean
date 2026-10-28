module

public import LpSelfSimilar.Bernoulli.ReservedTailIndex

@[expose] public section

/-!
# Exact angle and coordinate bounds for the reserved tail

The first angle on the full frequency band lies in `[sqrt(2),1.43)`.
Its natural digit index lies strictly below coordinate two, hence outside the
already packed digit windows. All bounds use the original logarithmic-gap and
frequency-width constants, with no extra tail-location hypothesis.
-/

namespace LpSelfSimilar.Bernoulli

/-- The exact numerical loss from the frequency width and parameter is below 1.43. -/
theorem reserved_tail_angle_ratio_lt {θ ε : ℝ} (hθ : (249 / 250 : ℝ) ≤ θ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 100000) :
    (1 + ε) * Real.sqrt 2 / (θ * (1 - ε)) < (143 / 100 : ℝ) := by
  have hs0 := Real.sqrt_nonneg (2 : ℝ)
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs1 : Real.sqrt 2 ≤ (1415 / 1000 : ℝ) := by nlinarith
  have hn := mul_le_mul (show 1 + ε ≤ (100001 / 100000 : ℝ) by linarith)
    hs1 hs0 (by norm_num : (0 : ℝ) ≤ 100001 / 100000)
  have hd := mul_le_mul hθ (show (99999 / 100000 : ℝ) ≤ 1 - ε by linarith)
    (by norm_num : (0 : ℝ) ≤ 99999 / 100000) (by linarith : 0 ≤ θ)
  have hd0 : 0 < θ * (1 - ε) := by positivity
  apply (div_lt_iff₀ hd0).mpr
  nlinarith

/-- Every first angle on the entire Fourier band has the required lower and upper bounds. -/
theorem reservedTailStart_angle_bounds {θ ε r : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hgap : -Real.log θ ≤ 1 / 250) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 100000)
    (hr : 0 < r) (hrχ : r ≤ -Real.log θ) (ξ : ℝ) (hξ : abs (|ξ| - 1) ≤ ε) :
    Real.sqrt 2 ≤ |ξ| * θ ^ reservedTailStart θ ε r / r ∧
      |ξ| * θ ^ reservedTailStart θ ε r / r < (143 / 100 : ℝ) := by
  have hs := reservedTailStart_spec hθ0 hθ1 hgap hε hr hrχ
  have hpow : 0 < θ ^ reservedTailStart θ ε r := pow_pos hθ0 _
  have hε1 : 0 < 1 - ε := by linarith
  have hξ' := abs_le.mp hξ
  have hξlo : 1 - ε ≤ |ξ| := by linarith [hξ'.1]
  have hξhi : |ξ| ≤ 1 + ε := by linarith [hξ'.2]
  constructor
  · apply (le_div_iff₀ hr).mpr
    have hlo := (div_le_iff₀ hε1).mp hs.1
    have hm := mul_le_mul_of_nonneg_left hξlo hpow.le
    nlinarith
  · have hq : θ ^ reservedTailStart θ ε r / r ≤ Real.sqrt 2 / (θ * (1 - ε)) := by
      apply (div_le_iff₀ hr).mpr
      calc
        _ ≤ _ := hs.2
        _ = _ := by ring
    calc
      _ = |ξ| * (θ ^ reservedTailStart θ ε r / r) := by ring
      _ ≤ (1 + ε) * (Real.sqrt 2 / (θ * (1 - ε))) :=
        mul_le_mul hξhi hq (by positivity) (by positivity)
      _ = (1 + ε) * Real.sqrt 2 / (θ * (1 - ε)) := by ring
      _ < _ := reserved_tail_angle_ratio_lt (reserved_tail_parameter_lower hθ0 hgap) hε0 hε

/-- At a dyadic frequency scale the selected tail begins strictly below coordinate two. -/
theorem reservedTailStart_coordinate_lt_two {θ ε R : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hgap : -Real.log θ ≤ 1 / 250) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 100000)
    (hrχ : (2 : ℝ) ^ (-R) ≤ -Real.log θ) :
    R - (-Real.log θ / Real.log 2) * reservedTailStart θ ε ((2 : ℝ) ^ (-R)) < 2 := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hr := Real.rpow_pos_of_pos h2 (-R)
  have hq := (reservedTailStart_angle_bounds hθ0 hθ1 hgap hε0 hε hr hrχ 1 (by simpa)).2
  simp only [abs_one, one_mul] at hq
  have hq0 := div_pos (pow_pos hθ0 (reservedTailStart θ ε ((2 : ℝ) ^ (-R)))) hr
  have hl := Real.log_lt_log hq0
    (show θ ^ reservedTailStart θ ε ((2 : ℝ) ^ (-R)) / (2 : ℝ) ^ (-R) < (2 : ℝ) ^ 2 by
      norm_num
      linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he : Real.log (θ ^ reservedTailStart θ ε ((2 : ℝ) ^ (-R)) / (2 : ℝ) ^ (-R)) =
      (R - (-Real.log θ / Real.log 2) * reservedTailStart θ ε ((2 : ℝ) ^ (-R))) * Real.log 2 := by
    rw [Real.log_div (pow_pos hθ0 _).ne' hr.ne', Real.log_pow, Real.log_rpow h2]
    field_simp
    <;> ring
  rw [he, Real.log_pow] at hl
  norm_num at hl
  nlinarith

end LpSelfSimilar.Bernoulli
