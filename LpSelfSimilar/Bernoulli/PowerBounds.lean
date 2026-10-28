module

public import LpSelfSimilar.Bernoulli.IntegrabilityExponent

@[expose] public section

/-! Elementary bounds for powers of a Bernoulli parameter and its Lp gain. -/

open Real

namespace LpSelfSimilar.Bernoulli

lemma logarithmic_contraction_le_twice_gap {l : ℝ} (hl0 : 1 / 2 ≤ l) (hl1 : l < 1) :
    -log l ≤ 2 * (1 - l) := by
  have hl : 0 < l := by linarith
  have h := one_sub_inv_le_log_of_pos hl
  have hinv : l⁻¹ - 1 ≤ 2 * (1 - l) := by
    have he : l⁻¹ - 1 = (1 - l) / l := by field_simp
    rw [he]
    apply (div_le_iff₀ hl).mpr
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - l) (by linarith : 0 ≤ 2 * l - 1)]
  linarith

lemma one_sub_mul_gap_le_pow {l : ℝ} (hl : 0 ≤ l) (k : ℕ) :
    1 - (k : ℝ) * (1 - l) ≤ l ^ k := by
  have h := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ l - 1) k
  simp only [add_sub_cancel] at h
  convert h using 1 <;> try rfl
  ring

lemma pow_le_self_of_pos {l : ℝ} (hl : 0 ≤ l) (hl1 : l ≤ 1) {k : ℕ} (hk : 1 ≤ k) :
    l ^ k ≤ l := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [pow_succ]
  simpa using mul_le_mul_of_nonneg_right (pow_le_one₀ hl hl1) hl

lemma integrabilityGain_antitone {u l : ℝ} (hu : 0 ≤ u) (hul : u ≤ l) (hl1 : l < 1) :
    integrabilityGain l ≤ integrabilityGain u := by
  have hg : 0 < 1 - l := by linarith
  have hgu : 0 < 1 - u := by linarith
  have hi : (1 - u)⁻¹ ≤ (1 - l)⁻¹ := inv_anti₀ hg (by linarith)
  have hlog := log_le_log (inv_pos.mpr hgu) hi
  have hlog0 : 0 ≤ log ((1 - u)⁻¹) := by
    rw [log_inv]
    exact neg_nonneg.mpr (log_nonpos hgu.le (by linarith))
  unfold integrabilityGain
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

end LpSelfSimilar.Bernoulli
