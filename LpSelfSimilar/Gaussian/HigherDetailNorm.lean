module

public import LpSelfSimilar.Gaussian.HigherDetail

@[expose] public section

/-!
Convert higher detail at its normalized scale into an L1 norm bound at a
specified positive variance. The factor Q is retained so that it cancels in
ordinary-detail comparisons; Q at least one controls all higher powers.
-/

open MeasureTheory MeasureTheory.Measure Real

namespace LpSelfSimilar.Gaussian

lemma integral_abs_higherSmooth_le_of_higherDetail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {k : ℕ} (hk : 0 < k) {y δ : ℝ} (hy : 0 < y)
    (h : higherDetail μ k (sqrt (y / k)) ≤ δ) :
    (∫ x, |higherSmooth μ k y x|) ≤ δ * (k : ℝ) ^ k / (detailNormalization * y ^ k) := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hsq : (sqrt (y / k)) ^ 2 = y / k := sq_sqrt (by positivity)
  have hvar : (k : ℝ) * (sqrt (y / k)) ^ 2 = y := by rw [hsq]; field_simp
  have hpow : (sqrt (y / k)) ^ (2 * k) = y ^ k / (k : ℝ) ^ k := by
    rw [pow_mul, hsq, div_pow]
  unfold higherDetail at h
  rw [hvar, hpow] at h
  have hQ : detailNormalization ≤ detailNormalization ^ k :=
    le_self_pow₀ one_le_detailNormalization hk.ne'
  have hn : 0 ≤ ∫ x, |higherSmooth μ k y x| := integral_nonneg (fun _ ↦ abs_nonneg _)
  have h' : (y ^ k / (k : ℝ) ^ k) * detailNormalization *
      (∫ x, |higherSmooth μ k y x|) ≤ δ := by
    apply le_trans _ h
    gcongr
  apply (le_div_iff₀ (mul_pos detailNormalization_pos (pow_pos hy k))).2
  have h'' := (div_le_iff₀ (pow_pos hkR k)).mp
    (show (detailNormalization * (∫ x, |higherSmooth μ k y x|) * y ^ k) /
      (k : ℝ) ^ k ≤ δ by convert h' using 1 <;> ring)
  nlinarith [h'']

lemma integral_abs_higherSmooth_universal (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {k : ℕ} (hk : 0 < k) {y : ℝ} (hy : 0 < y) :
    (∫ x, |higherSmooth μ k y x|) ≤ (k : ℝ) ^ k / (detailNormalization * y ^ k) := by
  have hr : 0 < sqrt (y / k) := by positivity
  simpa only [one_mul] using integral_abs_higherSmooth_le_of_higherDetail μ hk hy
    (higherDetail_le_one μ hk hr)

end LpSelfSimilar.Gaussian
