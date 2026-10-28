module

public import LpSelfSimilar.Entropy.CancellationRate
public import LpSelfSimilar.Analysis.PackingNumericalBounds
public import LpSelfSimilar.Analysis.GeometricPhaseLength

@[expose] public section

/-!
# Parameters of the multiscale Bernoulli digit packing

These are ordinary numerical definitions: `t=log(150J)`, the frequency width,
the integer length multiplier and starting length, and the target attenuation.
The bounds use only the explicit numerical hypotheses of the working criterion;
no entropy or regularity conclusion is encoded into a parameter.
-/

open LpSelfSimilar.Analysis LpSelfSimilar.Entropy

namespace LpSelfSimilar.Bernoulli

/-- Logarithmic cost of passing to the next family of block lengths. -/
noncomputable def packingLogScale (J : ℝ) : ℝ := Real.log (150 * J)

/-- Width of the frequency neighborhood used in the block construction. -/
noncomputable def packingFrequencyWidth (J : ℝ) : ℝ :=
  1 / (100000 * J * packingLogScale J)

/-- Integer multiplier separating the windows for successive block lengths. -/
noncomputable def packingLengthMultiplier (J : ℝ) : ℕ := ⌈9 * J⌉₊

/-- First block length, chosen large enough to absorb endpoint and phase-padding errors. -/
noncomputable def packingBaseLength (χ J : ℝ) : ℕ :=
  ⌈1000000 * J * packingLogScale J / χ⌉₊

/-- Required attenuation from one complete block-length family. -/
noncomputable def packingAttenuation (χ ρ L : ℝ) : ℝ :=
  (999 / 1000 : ℝ) / (χ / Real.log 2) *
    (bandCancellationRate ρ L - ρ / (1000 * packingLogScale (L / ρ)))

/-- Every admissible ratio has logarithmic scale strictly greater than six. -/
theorem six_lt_packingLogScale {J : ℝ} (hJ : 3 ≤ J) : 6 < packingLogScale J :=
  six_lt_log_four_hundred_fifty.trans_le (Real.log_le_log (by norm_num) (by linarith))

/-- The chosen frequency width is positive. -/
theorem packingFrequencyWidth_pos {J : ℝ} (hJ : 3 ≤ J) : 0 < packingFrequencyWidth J := by
  have ht := six_lt_packingLogScale hJ
  unfold packingFrequencyWidth
  positivity

/-- The frequency width is strictly below one hundred-thousandth. -/
theorem packingFrequencyWidth_lt {J : ℝ} (hJ : 3 ≤ J) :
    packingFrequencyWidth J < (1 / 100000 : ℝ) := by
  have ht := six_lt_packingLogScale hJ
  unfold packingFrequencyWidth
  apply one_div_lt_one_div_of_lt (by norm_num)
  nlinarith

/-- The integer length multiplier has the two exact bounds used in scale separation. -/
theorem packingLengthMultiplier_bounds {J : ℝ} (hJ : 3 ≤ J) :
    9 * J ≤ (packingLengthMultiplier J : ℝ) ∧ (packingLengthMultiplier J : ℝ) ≤ 10 * J := by
  have hlo : 9 * J ≤ (packingLengthMultiplier J : ℝ) := Nat.le_ceil _
  have hhi : (packingLengthMultiplier J : ℝ) < 9 * J + 1 :=
    Nat.ceil_lt_add_one (by linarith)
  exact ⟨hlo, by linarith⟩

/-- The multiplier is at least twenty-seven, so its logarithm is positive. -/
theorem twenty_seven_le_packingLengthMultiplier {J : ℝ} (hJ : 3 ≤ J) :
    27 ≤ packingLengthMultiplier J := by
  have h := (packingLengthMultiplier_bounds hJ).1
  have he : (27 : ℝ) ≤ (packingLengthMultiplier J : ℝ) := by linarith
  exact_mod_cast he

/-- The first length retains its defining lower bound without a rounding loss. -/
theorem packingBaseLength_lower_bound (χ J : ℝ) :
    1000000 * J * packingLogScale J / χ ≤ (packingBaseLength χ J : ℝ) := Nat.le_ceil _

/-- Every admissible first length is positive. -/
theorem packingBaseLength_pos {χ J : ℝ} (hχ : 0 < χ) (hJ : 3 ≤ J) :
    0 < packingBaseLength χ J := by
  have ht := six_lt_packingLogScale hJ
  have hl := packingBaseLength_lower_bound χ J
  have hp : (0 : ℝ) < (packingBaseLength χ J : ℝ) := lt_of_lt_of_le (by positivity) hl
  exact_mod_cast hp

/-- The quadratic smallness condition gives the strict gap-to-entropy bound used in packing. -/
theorem packing_gap_div_entropy_lt {χ ρ L : ℝ} (hχ : 0 < χ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hL : 3 ≤ L)
    (hsmall : χ * (packingLogScale (L / ρ)) ^ 2 ≤ ρ / 2) :
    χ / ρ < (1 / 70 : ℝ) := by
  have ht := six_lt_packingLogScale (three_le_separation_entropy_ratio hρ hρ1 hL)
  have hs : (36 : ℝ) < (packingLogScale (L / ρ)) ^ 2 := by nlinarith
  have hprod := mul_lt_mul_of_pos_left hs hχ
  apply (div_lt_iff₀ hρ).mpr
  nlinarith

end LpSelfSimilar.Bernoulli
