module

public import LpSelfSimilar.Rational.MultiscaleBlocks
public import LpSelfSimilar.Analysis.GeometricBlockLengths
public import LpSelfSimilar.Analysis.EffectiveVarianceBudget

@[expose] public section

/-!
Rational Proposition 3.8. An absolute smallness condition on χ B^10 produces
the full higher-detail estimate at every sufficiently small scale. Deterministic
shifted grids, ceiling placement and the count of geometric block lengths supply
all hypotheses of the conditional-variance argument.
-/

open Real
open LpSelfSimilar.Gaussian LpSelfSimilar.Bernoulli

namespace LpSelfSimilar.Rational

/-- An absolute positive threshold, independent of the rational parameter. -/
noncomputable def effectiveDetailThreshold : ℝ :=
  min (1 / 200) (conditionalRadius ^ 2 * blockVarianceConstant / 100000000)

lemma effectiveDetailThreshold_pos : 0 < effectiveDetailThreshold := by
  unfold effectiveDetailThreshold
  have hε := conditionalRadius_pos
  have hc := blockVarianceConstant_pos
  positivity

/-- Full rational effective-detail estimate, including every allowed order. -/
theorem effective_detail {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : a.Coprime b)
    (hl0 : 1 / 2 ≤ (a : ℝ) / b) (hl1 : (a : ℝ) / b < 1)
    (hsmall : -log ((a : ℝ) / b) * complexity b ^ 10 ≤ effectiveDetailThreshold)
    {R : ℝ} (hR : 1000 * complexity b ^ 3 ≤ R) {k : ℕ}
    (hk : 1 ≤ k) (hkR : (k : ℝ) ≤ 10 * log R) :
    higherDetail (convolution ((a : ℝ) / b)) k (exp (-R)) ≤ (1 / 100 : ℝ) ^ k := by
  let B := complexity b
  let χ := -log ((a : ℝ) / b)
  let ε := conditionalRadius
  have hB : 2 ≤ B := two_le_complexity hb
  have hB0 : 0 < B := complexity_pos hb
  have hl : 0 < (a : ℝ) / b := by linarith
  have hχ : 0 < χ := neg_pos.mpr (log_neg hl hl1)
  have hB1 : 1 ≤ B := by linarith
  have hp19 : B ≤ B ^ 10 := by
    simpa using (pow_le_pow_right₀ hB1 (show 1 ≤ (10 : ℕ) by norm_num))
  have hp910 : B ^ 9 ≤ B ^ 10 := pow_le_pow_right₀ hB1 (by norm_num)
  have hχB : χ * B ≤ 1 / 200 :=
    (mul_le_mul_of_nonneg_left hp19 hχ.le).trans
      (hsmall.trans (min_le_left _ _))
  have hχmesh : χ ≤ 1 / (200 * B) := by
    have h := (le_div_iff₀ hB0).mpr hχB
    convert h using 1 <;> try rfl
    ring
  have hχ9 : χ * B ^ 9 ≤ ε ^ 2 * blockVarianceConstant / 100000000 :=
    (mul_le_mul_of_nonneg_left hp910 hχ.le).trans
      (hsmall.trans (min_le_right _ _))
  obtain ⟨m, n, hcount, hn, hnR, hsep⟩ := exists_geometric_block_lengths hB hR
  let T := R - log ε
  have hε : 0 < ε := conditionalRadius_pos
  have hε1 : ε ≤ 1 := conditionalRadius_le_one
  have hRT : R ≤ T := by
    have hlog : log ε ≤ 0 := log_nonpos hε.le hε1
    dsimp [T]
    linarith
  have hmesh : exp (-T) = ε * exp (-R) := by
    dsimp [T]
    rw [neg_sub, sub_eq_add_neg, exp_add, exp_log hε]
  have hbudget : 1001 * (k : ℝ) * exp (-R) ^ 2 ≤
      (m : ℝ) * (exp (-T) ^ 2 / 4 * (blockVarianceConstant / (χ * B ^ 7))) := by
    have h := effective_variance_budget hB0 hχ (Nat.cast_nonneg m) hχ9 hcount hkR
    have hmul := mul_le_mul_of_nonneg_right h (sq_nonneg (exp (-R)))
    rw [hmesh]
    convert hmul using 1 <;> try rfl
    ring
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  apply higherDetail_le_of_separated_lengths n ha hb hab hl0 hl1 hχmesh
    (exp_pos _) (by rw [hmesh]) hn (fun i ↦ (hnR i).trans hRT) hsep j
  simpa only [Fintype.card_fin] using hbudget

end LpSelfSimilar.Rational
