module

public import LpSelfSimilar.Entropy.GraphQuantization
public import LpSelfSimilar.Geometry.FiniteIntervalQuantization

@[expose] public section

/-!
# Quantitative near-graph entropy for bounded finite laws

Actual half-open cell labels have entropy at most the logarithm of their number.
Combined with near/far duality, this gives the near-entropy lower bound used in
the scale budget. At dyadic exponent `j >= 0`, the error is at most
`j + log(hi-lo+2)/log 2`; the additive two remains inside the logarithm.
-/

open scoped BigOperators Classical

namespace LpSelfSimilar.Entropy

/-- A finite probability vector has entropy at most the logarithm of any cardinality bound. -/
theorem finite_probability_entropy_le_log_of_card_le {κ : Type*} [Fintype κ]
    (p : κ → ℝ) (hp : ∀ k, 0 ≤ p k) (hsum : ∑ k, p k = 1)
    (Z : ℝ) (hZ : 0 < Z) (hcard : (Fintype.card κ : ℝ) ≤ Z) :
    ∑ k, Real.negMulLog (p k) ≤ Real.log Z := by
  simpa using finite_entropy_le_log_partition Finset.univ p (fun _ ↦ 1)
    (fun k _ ↦ hp k) hsum (fun _ _ ↦ zero_lt_one) hZ (by simpa using hcard)

/-- The actual finite-cell partition gives a quantitative lower bound for near entropy. -/
theorem near_graphEntropyBits_ge_of_interval {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (lo hi a : ℝ) (hlohi : lo ≤ hi) (ha : 0 < a) (hz : ∀ i, z i ∈ Set.Icc lo hi) :
    (∑ i, Real.negMulLog (p i)) / Real.log 2 -
      Real.log ((hi - lo) / a + 1) / Real.log 2 ≤ graphEntropyBits (nearDistanceGraph z a) p := by
  obtain ⟨N, hN, hcard, label, hdiam⟩ :=
    Geometry.exists_finite_interval_quantization z lo hi a hlohi ha hz
  let q : Fin N → ℝ := fun k ↦ ∑ i, if label i = k then p i else 0
  have hq : ∀ k, 0 ≤ q k := fun k ↦ Finset.sum_nonneg (fun i _ ↦ by
    split_ifs
    · exact hp i
    · exact le_rfl)
  have hqsum : ∑ k, q k = 1 := by
    simp only [q]
    rw [Finset.sum_comm]
    simpa using hsum
  have hZ : 0 < (hi - lo) / a + 1 := by
    have := div_nonneg (sub_nonneg.mpr hlohi) ha.le
    linarith
  have hentropy := finite_probability_entropy_le_log_of_card_le q hq hqsum
    ((hi - lo) / a + 1) hZ (by simpa using hcard)
  have hbits := div_le_div_of_nonneg_right hentropy (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  have hnear := near_graphEntropyBits_ge_entropy_sub_label z a ha p hp hsum label hdiam
  dsimp [q] at hbits
  exact (sub_le_sub_left hbits _).trans hnear

/-- At a nonnegative dyadic scale, the entire cell-label error is `j + log(hi-lo+2)/log 2`. -/
theorem dyadic_near_graphEntropyBits_ge_of_interval {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (lo hi j : ℝ) (hlohi : lo ≤ hi) (hj : 0 ≤ j) (hz : ∀ i, z i ∈ Set.Icc lo hi) :
    (∑ i, Real.negMulLog (p i)) / Real.log 2 - j - Real.log (hi - lo + 2) / Real.log 2 ≤
      graphEntropyBits (nearDistanceGraph z ((2 : ℝ) ^ (-j))) p := by
  have hpw : 0 < (2 : ℝ) ^ j := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
  have hpw1 : 1 ≤ (2 : ℝ) ^ j := Real.one_le_rpow (by norm_num) hj
  have hD : 0 < hi - lo + 2 := by linarith
  have hR : 0 < (hi - lo) / (2 : ℝ) ^ (-j) + 1 := by
    have := div_nonneg (sub_nonneg.mpr hlohi) (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-j)).le
    linarith
  have hbound : (hi - lo) / (2 : ℝ) ^ (-j) + 1 ≤ (2 : ℝ) ^ j * (hi - lo + 2) := by
    rw [Real.rpow_neg (by norm_num), div_inv_eq_mul]
    nlinarith
  have hl := Real.log_le_log hR hbound
  rw [Real.log_mul hpw.ne' hD.ne', Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hl
  have hbits := div_le_div_of_nonneg_right hl (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  rw [add_div, mul_div_cancel_right₀ _ hlog] at hbits
  have hn := near_graphEntropyBits_ge_of_interval z p hp hsum lo hi ((2 : ℝ) ^ (-j))
    hlohi (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _) hz
  linarith

end LpSelfSimilar.Entropy
