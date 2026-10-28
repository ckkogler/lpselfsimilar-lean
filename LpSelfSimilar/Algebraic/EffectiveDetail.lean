module

public import LpSelfSimilar.Algebraic.MultiscaleBlocks
public import LpSelfSimilar.Analysis.GeometricBlockLengths
public import LpSelfSimilar.Analysis.EffectiveVarianceBudget

@[expose] public section

/-!
Exact revised Proposition 3.8 for every algebraic parameter. The explicit input
chi B^10 <= 10^-100 gives higher detail <=100^-k for R>=10^6 B^3 and k<=10 log R.

We reuse a coarser proved count of geometric lengths than the paper's intermediate
count. Its extra B^2 loss is absorbed by the explicit threshold. Every selected
block law, disjointness statement, variance budget and unused-digit convolution
has been proved; no smoothing or entropy assumption enters this theorem.
-/

open Real
open LpSelfSimilar.Gaussian LpSelfSimilar.Bernoulli

namespace LpSelfSimilar.Algebraic

/-- Full revised Proposition 3.8, including every allowed order. -/
theorem effective_detail {l : ℝ} (hlalg : IsAlgebraic ℚ l)
    (hl0 : 1 / 2 ≤ l) (hl1 : l < 1)
    (hsmall : -log l * complexity l ^ 10 ≤ 1 / (10 : ℝ) ^ 100)
    {R : ℝ} (hR : (10 : ℝ) ^ 6 * complexity l ^ 3 ≤ R) {k : ℕ}
    (hk : 1 ≤ k) (hkR : (k : ℝ) ≤ 10 * log R) :
    higherDetail (convolution l) k (exp (-R)) ≤ (1 / 100 : ℝ) ^ k := by
  let B := complexity l
  let χ := -log l
  let ε : ℝ := 1 / 10000
  have hB3 : 3 ≤ B := three_le_complexity hlalg (by linarith) hl1
  have hB : 2 ≤ B := by linarith
  have hB0 : 0 < B := complexity_pos hlalg (by linarith) hl1
  have hl : 0 < l := by linarith
  have hχ : 0 < χ := neg_pos.mpr (log_neg hl hl1)
  have hB1 : 1 ≤ B := by linarith
  have hp19 : B ≤ B ^ 10 := by
    simpa using (pow_le_pow_right₀ hB1 (show 1 ≤ (10 : ℕ) by norm_num))
  have hp910 : B ^ 9 ≤ B ^ 10 := pow_le_pow_right₀ hB1 (by norm_num)
  have hχB : χ * B ≤ 1 / 200 :=
    (mul_le_mul_of_nonneg_left hp19 hχ.le).trans
      (hsmall.trans (by norm_num))
  have hχmesh : χ ≤ 1 / (200 * B) := by
    have h := (le_div_iff₀ hB0).mpr hχB
    convert h using 1 <;> try rfl
    ring
  have hχ9 : χ * B ^ 9 ≤ ε ^ 2 * (1 / (10 : ℝ) ^ 10) / 100000000 :=
    (mul_le_mul_of_nonneg_left hp910 hχ.le).trans
      (hsmall.trans (by norm_num [ε]))
  obtain ⟨m, n, hcount, hn, hnR, hsep⟩ := exists_geometric_block_lengths hB
    (show 1000 * B ^ 3 ≤ R by nlinarith [pow_nonneg hB0.le 3])
  let T := R - log ε
  have hε : 0 < ε := by norm_num [ε]
  have hε1 : ε ≤ 1 := by norm_num [ε]
  have hRT : R ≤ T := by
    have hlog : log ε ≤ 0 := log_nonpos hε.le hε1
    dsimp [T]
    linarith
  have hmesh : exp (-T) = ε * exp (-R) := by
    dsimp [T]
    rw [neg_sub, sub_eq_add_neg, exp_add, exp_log hε]
  have hbudget : 1001 * (k : ℝ) * exp (-R) ^ 2 ≤
      (m : ℝ) * (exp (-T) ^ 2 / 4 * ((1 / (10 : ℝ) ^ 10) / (χ * B ^ 7))) := by
    have h := effective_variance_budget hB0 hχ (Nat.cast_nonneg m) hχ9 hcount hkR
    have hmul := mul_le_mul_of_nonneg_right h (sq_nonneg (exp (-R)))
    rw [hmesh]
    convert hmul using 1 <;> try rfl
    ring
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  apply higherDetail_le_of_separated_lengths n hlalg hl0 hl1 hχmesh
    (exp_pos _) (by rw [hmesh]) hn (fun i ↦ (hnR i).trans hRT) hsep j
  simpa only [Fintype.card_fin] using hbudget

end LpSelfSimilar.Algebraic
