module

public import LpSelfSimilar.Rational.VarianceGrid
public import LpSelfSimilar.Bernoulli.BlockDetail
public import LpSelfSimilar.Bernoulli.BlockWindows
public import LpSelfSimilar.Bernoulli.BlockMesh

@[expose] public section

/-!
Combining separated rational digit lengths into actual independent Bernoulli
blocks. Each length supplies a deterministic grid; all chosen grids are joined
in a finite dependent sum. The variance budget is then fed to Lemma 3.3.
-/

open MeasureTheory Real Set
open LpSelfSimilar.Bernoulli LpSelfSimilar.Entropy LpSelfSimilar.Gaussian

namespace LpSelfSimilar.Rational

/-- The effective-detail input supplied by any finite collection of separated
lengths. All block laws, their independence and their variance are derived. -/
theorem higherDetail_le_of_separated_lengths {I : Type*} [Fintype I]
    (n : I → ℕ) {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : a.Coprime b)
    (hl0 : 1 / 2 ≤ (a : ℝ) / b) (hl1 : (a : ℝ) / b < 1)
    (hχsmall : -log ((a : ℝ) / b) ≤ 1 / (200 * complexity b))
    {T r : ℝ} (hr : 0 < r) (hmesh : exp (-T) ≤ conditionalRadius * r)
    (hn : ∀ i, 100 * complexity b ^ 2 ≤ (n i : ℝ))
    (hnT : ∀ i, 2 * complexity b * n i ≤ T)
    (hsep : ∀ i j, i ≠ j →
      400 * complexity b ^ 2 * (n i : ℝ) ≤ n j ∨
      400 * complexity b ^ 2 * (n j : ℝ) ≤ n i)
    (k : ℕ)
    (hbudget : 1001 * (k + 1 : ℕ) * r ^ 2 ≤
      Fintype.card I * (exp (-T) ^ 2 / 4 *
        (blockVarianceConstant / (-log ((a : ℝ) / b) * complexity b ^ 7)))) :
    higherDetail (convolution ((a : ℝ) / b)) (k + 1) r ≤ (1 / 100 : ℝ) ^ (k + 1) := by
  classical
  let l : ℝ := (a : ℝ) / b
  let χ := -log l
  let B := complexity b
  have hl : 0 < l := by dsimp [l]; linarith
  have hχ : 0 < χ := neg_pos.mpr (log_neg hl hl1)
  have hB : 0 < B := complexity_pos hb
  have hg (i : I) := exists_digit_variance_grid ha hb hab hl1 (hn i) hχ
  choose S t hbounds hvar using hg
  let J := (i : I) × {j : ℕ // j ∈ S i}
  let v (z : J) : ℝ := (n z.1 : ℝ) * χ * ((z.2.val : ℝ) + t z.1)
  let m (z : J) := blockStart χ T (v z)
  let len (z : J) := n z.1
  let s (z : J) := exp (-v z)
  have hv (z : J) : v z ∈ Icc ((n z.1 : ℝ) / (100 * B)) (2 * B * n z.1) :=
    hbounds z.1 z.2.val z.2.property
  have hvT (z : J) : v z ≤ T := (hv z).2.trans (hnT z.1)
  have hd : ∀ z ∈ (Finset.univ : Finset J), ∀ w ∈ Finset.univ, z ≠ w →
      Disjoint (Finset.Ico (m z) (m z + len z)) (Finset.Ico (m w) (m w + len w)) := by
    intro z _ w _ hzw
    by_cases he : z.1 = w.1
    · obtain ⟨i, j⟩ := z
      obtain ⟨i', j'⟩ := w
      dsimp only at he
      subst i'
      have hj : j.val ≠ j'.val := by
        intro heq
        apply hzw
        congr 1
        exact Subtype.ext heq
      rcases lt_or_gt_of_ne hj with hjlt | hjgt
      · exact blockStart_grid_disjoint hχ (n i) hjlt (hvT ⟨i, j'⟩)
      · exact (blockStart_grid_disjoint hχ (n i) hjgt (hvT ⟨i, j⟩)).symm
    · rcases hsep z.1 w.1 he with h | h
      · exact blockStart_disjoint_of_length_separation hχ hB hχsmall h
          (hv z) (hvT z) (hv w) (hvT w)
      · exact (blockStart_disjoint_of_length_separation hχ hB hχsmall h
          (hv w) (hvT w) (hv z) (hvT z)).symm
  have hsm (z : J) : l ^ m z * s z ≤ conditionalRadius * r :=
    (blockStart_power_mesh hl hl1 (hvT z)).2.trans hmesh
  have hsum (i : I) : exp (-T) ^ 2 / 4 * (blockVarianceConstant / (χ * B ^ 7)) ≤
      ∑ j : {j : ℕ // j ∈ S i}, (l ^ m ⟨i, j⟩ * s ⟨i, j⟩) ^ 2 *
        scaleVariance (digitPMF l (n i)) (digitPMF_support_finite _ _) (s ⟨i, j⟩) := by
    have hvsum := mul_le_mul_of_nonneg_left (hvar i)
      (by positivity : 0 ≤ exp (-T) ^ 2 / 4)
    rw [Finset.mul_sum] at hvsum
    have hsum' : (∑ j ∈ S i, exp (-T) ^ 2 / 4 *
        varianceOnLogScale (digitPMF l (n i)) (digitPMF_support_finite _ _)
          ((n i : ℝ) * χ * ((j : ℝ) + t i))) =
        ∑ j : {j : ℕ // j ∈ S i}, exp (-T) ^ 2 / 4 *
          scaleVariance (digitPMF l (n i)) (digitPMF_support_finite _ _) (s ⟨i, j⟩) := by
      simp [s, v, varianceOnLogScale]
      exact (Finset.sum_attach (S i) _).symm
    rw [hsum'] at hvsum
    apply hvsum.trans
    apply Finset.sum_le_sum
    intro j _
    exact placed_mesh_variance_lower hl0 hl1 (hvT ⟨i, j⟩)
      (scaleVariance_nonneg _ _ _)
  have htotal : 1001 * (k + 1 : ℕ) * r ^ 2 ≤
      ∑ z : J, (l ^ m z * s z) ^ 2 *
        scaleVariance (digitPMF l (len z)) (digitPMF_support_finite _ _) (s z) := by
    rw [Fintype.sum_sigma]
    have hsumall := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) ↦ hsum i)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsumall
    exact hbudget.trans hsumall
  exact higherDetail_le_of_disjoint_block_variance Finset.univ m len s hl hl1 hr hd
    (fun z ↦ exp_pos _) hsm k htotal

end LpSelfSimilar.Rational
