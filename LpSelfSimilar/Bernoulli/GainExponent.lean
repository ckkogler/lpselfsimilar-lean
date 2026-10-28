module

public import LpSelfSimilar.WeakReverseHolder.Constants

@[expose] public section

/-!
The exact Lemma 2.1 exponent for the Bernoulli small-set parameters. Retaining
the support diameter yields the same quantitative lower bound needed in
Proposition 3.1, with no asymptotic logarithmic estimates left implicit.
-/

open Real Set

namespace LpSelfSimilar.Bernoulli

noncomputable def gainVolumeFraction (l : ℝ) : ℝ := l * (1 - l) / (4 * 21 ^ 2)

noncomputable def gainExponent (l : ℝ) : ℝ :=
  lemmaExponent 1 (gainVolumeFraction l) (1 / 21 ^ 2)

lemma gainVolumeFraction_mem {l : ℝ} (hl : 0 < l) (hl1 : l < 1) :
    gainVolumeFraction l ∈ Ioo 0 1 := by
  constructor
  · dsimp [gainVolumeFraction]
    positivity
  · dsimp [gainVolumeFraction]
    norm_num
    nlinarith [sq_nonneg l]

/-- The paper's quantitative gain follows from the unchanged exact lemma exponent. -/
theorem gainExponent_lowerBound {l : ℝ} (hl0 : 1 / 2 ≤ l) (hl1 : l < 1) :
    1 + 1 / (10 * (1 + log ((1 - l)⁻¹))) ≤ gainExponent l := by
  have hl : 0 < l := by linarith
  have hg : 0 < 1 - l := by linarith
  have hε := gainVolumeFraction_mem hl hl1
  have h2 : log (2 : ℝ) ≤ 1 := by linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h2lo : (1 : ℝ) / 2 ≤ log 2 := by
    have h := one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have h16 : log (16 : ℝ) = 4 * log 2 := by
    have h := log_pow (2 : ℝ) 4
    norm_num at h
    exact h
  have h21 : (2 : ℝ) ≤ log 21 := by
    have h := log_le_log (by norm_num : (0 : ℝ) < 16) (by norm_num : (16 : ℝ) ≤ 21)
    rw [h16] at h
    linarith
  have h4 : log (4 : ℝ) = 2 * log 2 := by
    have h := log_pow (2 : ℝ) 2
    norm_num at h
    exact h
  have hlower : -log 2 ≤ log l := by
    have h := log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hl0
    norm_num [log_div] at h
    exact h
  have hL : 0 ≤ log ((1 - l)⁻¹) := by
    rw [log_inv]
    exact neg_nonneg.mpr (log_nonpos hg.le (by linarith))
  have hd : 0 < log (21 / gainVolumeFraction l) := by
    apply log_pos
    apply (lt_div_iff₀ hε.1).mpr
    linarith [hε.2]
  have hden : log (21 / gainVolumeFraction l) =
      log 4 + 3 * log 21 - log l + log ((1 - l)⁻¹) := by
    rw [gainVolumeFraction, log_div (by norm_num) (by positivity),
      log_div (mul_pos hl hg).ne' (by norm_num), log_mul hl.ne' hg.ne',
      log_mul (by norm_num) (by norm_num), log_pow, log_inv]
    norm_num
    ring
  have hbound : 2 * log (21 / gainVolumeFraction l) ≤
      log 21 * (10 * (1 + log ((1 - l)⁻¹))) := by
    rw [hden, h4]
    nlinarith [mul_nonneg (show 0 ≤ log 21 - 2 by linarith) hL]
  have hincr : 1 / (10 * (1 + log ((1 - l)⁻¹))) ≤
      log 21 / (2 * log (21 / gainVolumeFraction l)) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 10 * (1 + log ((1 - l)⁻¹)))
      (by positivity : 0 < 2 * log (21 / gainVolumeFraction l))).mpr
    simpa only [one_mul] using hbound
  unfold gainExponent lemmaExponent coveringConstant
  norm_num only [pow_one, show (1 : ℝ) / (21 * (1 / 21 ^ 2)) = 21 by norm_num]
  linarith

end LpSelfSimilar.Bernoulli
