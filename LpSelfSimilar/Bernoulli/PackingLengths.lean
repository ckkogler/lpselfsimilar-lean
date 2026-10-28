module

public import LpSelfSimilar.Analysis.GeometricLengthCutoff
public import LpSelfSimilar.Bernoulli.PackingParameters

@[expose] public section

/-!
# The exact finite family of packing lengths

The lengths are `n₀ * N^k`, where `n₀` and `N` are the previously fixed packing
parameters. At scale `R ≥ R₀ = 4*(L+1)*n₀`, the logarithmic floor selects exactly
those lengths satisfying `4*(L+1)*n ≤ R`. The natural and integer floor formulas
agree, including when the scale ratio is an exact power of `N`.
-/

open LpSelfSimilar.Analysis LpSelfSimilar.Entropy

namespace LpSelfSimilar.Bernoulli

/-- The geometrically increasing block length at a natural scale index. -/
noncomputable def packingBlockLength (χ J : ℝ) (k : ℕ) : ℕ :=
  packingBaseLength χ J * packingLengthMultiplier J ^ k

/-- First logarithmic frequency scale where a complete length family fits. -/
noncomputable def packingScaleThreshold (χ ρ L : ℝ) : ℝ :=
  4 * (L + 1) * packingBaseLength χ (L / ρ)

/-- Number of complete length families available at logarithmic frequency scale `R`. -/
noncomputable def packingLengthCount (χ ρ L R : ℝ) : ℕ :=
  geometricLengthCount (packingLengthMultiplier (L / ρ) : ℝ)
    (R / packingScaleThreshold χ ρ L)

/-- The first usable frequency scale is strictly positive. -/
theorem packingScaleThreshold_pos {χ ρ L : ℝ} (hχ : 0 < χ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hL : 3 ≤ L) : 0 < packingScaleThreshold χ ρ L := by
  have hn := packingBaseLength_pos hχ (three_le_separation_entropy_ratio hρ hρ1 hL)
  unfold packingScaleThreshold
  positivity

/-- The count includes at least the initial length. -/
theorem packingLengthCount_pos (χ ρ L R : ℝ) : 0 < packingLengthCount χ ρ L R :=
  geometricLengthCount_pos _ _

/-- At usable scales, the length count is precisely the integer logarithmic-floor formula. -/
theorem packingLengthCount_intCast {χ ρ L R : ℝ} (hχ : 0 < χ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hL : 3 ≤ L) (hR : packingScaleThreshold χ ρ L ≤ R) :
    (packingLengthCount χ ρ L R : ℤ) =
      1 + ⌊Real.log (R / packingScaleThreshold χ ρ L) /
        Real.log (packingLengthMultiplier (L / ρ) : ℝ)⌋ := by
  have hN := twenty_seven_le_packingLengthMultiplier
    (three_le_separation_entropy_ratio hρ hρ1 hL)
  have hN1 : (1 : ℝ) < packingLengthMultiplier (L / ρ) := by
    exact_mod_cast (show 1 < packingLengthMultiplier (L / ρ) by omega)
  exact geometricLengthCount_intCast hN1
    ((one_le_div (packingScaleThreshold_pos hχ hρ hρ1 hL)).mpr hR)

/-- Every geometric length is no smaller than the fixed first length. -/
theorem packingBaseLength_le_blockLength (χ : ℝ) {J : ℝ} (hJ : 3 ≤ J) (k : ℕ) :
    packingBaseLength χ J ≤ packingBlockLength χ J k := by
  have hN := twenty_seven_le_packingLengthMultiplier hJ
  have hpow : 1 ≤ packingLengthMultiplier J ^ k :=
    one_le_pow₀ (by omega)
  unfold packingBlockLength
  simpa using Nat.mul_le_mul_left (packingBaseLength χ J) hpow

/-- All block lengths are positive under the numerical hypotheses. -/
theorem packingBlockLength_pos {χ J : ℝ} (hχ : 0 < χ) (hJ : 3 ≤ J) (k : ℕ) :
    0 < packingBlockLength χ J k :=
  (packingBaseLength_pos hχ hJ).trans_le (packingBaseLength_le_blockLength χ hJ k)

/-- Distinct ordered scale indices give at least one full multiplier of separation. -/
theorem packingBlockLength_step_le (χ : ℝ) {J : ℝ} (hJ : 3 ≤ J)
    {k l : ℕ} (hkl : k < l) :
    packingLengthMultiplier J * packingBlockLength χ J k ≤ packingBlockLength χ J l := by
  have hN := twenty_seven_le_packingLengthMultiplier hJ
  have hp : packingLengthMultiplier J ^ (k + 1) ≤ packingLengthMultiplier J ^ l :=
    pow_le_pow_right' (by omega) hkl
  have hm := Nat.mul_le_mul_left (packingBaseLength χ J) hp
  simpa only [packingBlockLength, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hm

/-- The finite length range is exactly the range allowed by the natural-start cutoff. -/
theorem lt_packingLengthCount_iff {χ ρ L R : ℝ} (hχ : 0 < χ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hL : 3 ≤ L) (hR : packingScaleThreshold χ ρ L ≤ R) (k : ℕ) :
    k < packingLengthCount χ ρ L R ↔
      4 * (L + 1) * packingBlockLength χ (L / ρ) k ≤ R := by
  have hN := twenty_seven_le_packingLengthMultiplier
    (three_le_separation_entropy_ratio hρ hρ1 hL)
  have hN1 : (1 : ℝ) < packingLengthMultiplier (L / ρ) := by
    exact_mod_cast (show 1 < packingLengthMultiplier (L / ρ) by omega)
  have hR0 := packingScaleThreshold_pos hχ hρ hρ1 hL
  rw [packingLengthCount, lt_geometricLengthCount_iff hN1 ((one_le_div hR0).mpr hR),
    le_div_iff₀ hR0]
  simp only [packingScaleThreshold, packingBlockLength, Nat.cast_mul, Nat.cast_pow]
  ring_nf

end LpSelfSimilar.Bernoulli
