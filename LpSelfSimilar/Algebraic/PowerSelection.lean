module

public import LpSelfSimilar.Algebraic.HigherIntegrability
public import LpSelfSimilar.Algebraic.ComplexityPowers
public import LpSelfSimilar.Analysis.LargeComplexity
public import LpSelfSimilar.Bernoulli.PowerBounds

@[expose] public section

/-!
Explicit power selection for the full algebraic Theorem 1.2, under the stronger
condition (1-lambda) B^100<2 used in the paper. The canonical complexity grows
at most linearly. Logarithmic concavity forces B>600, absorbing every numerical
loss and giving a power with the precise integrability needed for convolution.
-/

open Real
open LpSelfSimilar.Bernoulli

namespace LpSelfSimilar.Algebraic

/-- The power k=ceil(100B) stays above 1/2 and satisfies Proposition 3.1. -/
theorem exists_smoothing_power {l : ℝ} (hlalg : IsAlgebraic ℚ l)
    (hl0 : 1 / 2 ≤ l) (hl1 : l < 1)
    (hsmall : (1 - l) * complexity l ^ 100 < 2) :
    ∃ k : ℕ, 2 ≤ k ∧
      1 / 2 < l ^ k ∧ l ^ k < 1 ∧
      -log (l ^ k) * complexity (l ^ k) ^ 10 ≤ (1 / (10 : ℝ) ^ 100) ∧
      (k : ℝ) / ((k : ℝ) - 1) ≤ 1 + integrabilityGain (l ^ k) := by
  let B := complexity l
  let k : ℕ := ⌈100 * B⌉₊
  have hB : 3 ≤ B := three_le_complexity hlalg (by linarith) hl1
  have hB0 : 0 < B := complexity_pos hlalg (by linarith) hl1
  have hB1 : 1 ≤ B := by linarith
  have hl : 0 < l := by linarith
  have hg : 0 < 1 - l := by linarith
  have hklo : 100 * B ≤ (k : ℝ) := Nat.le_ceil _
  have hkhi : (k : ℝ) ≤ 101 * B := by
    have h := Nat.ceil_lt_add_one (by positivity : 0 ≤ 100 * B)
    dsimp [k]
    linarith
  have hk2 : 2 ≤ k := by
    have h : (2 : ℝ) ≤ k := by linarith
    exact_mod_cast h
  have hk1 : 1 ≤ k := by omega
  have hkpos : 0 < k := by omega
  have hlog := log_inverse_gap_le_complexity hlalg hl hl1
  have hB600 : 600 < B := six_hundred_lt_of_small_gap hB hg hlog hsmall
  have hfinal : (1 - l) * B ^ 21 ≤ (1 / (10 : ℝ) ^ 100) / (2 * 101 ^ 11) :=
    gap_power_twenty_one_bound hB600.le hg.le hsmall
  have hpowB : B ≤ B ^ 21 := by
    simpa using pow_le_pow_right₀ hB1 (show 1 ≤ (21 : ℕ) by norm_num)
  have hgapB : (1 - l) * B ≤ 1 / 1000 :=
    (mul_le_mul_of_nonneg_left hpowB hg.le).trans (hfinal.trans (by norm_num))
  have hkGap : (k : ℝ) * (1 - l) ≤ 101 / 1000 := by
    have h := mul_le_mul_of_nonneg_right hkhi hg.le
    linarith
  have hθhalf : (1 : ℝ) / 2 < l ^ k := by
    have h := one_sub_mul_gap_le_pow hl.le k
    linarith
  have hθ1 : l ^ k < 1 := pow_lt_one₀ hl.le hl1 (by omega)
  have hχ : 0 ≤ -log l := (neg_pos.mpr (log_neg hl hl1)).le
  have hχbound := logarithmic_contraction_le_twice_gap hl0 hl1
  have hcomplex := complexity_pow_le_mul hlalg hl hl1 hkpos
  have hBP : 0 ≤ complexity (l ^ k) :=
    (complexity_pos (isAlgebraic_pow hlalg k) (pow_pos hl k) hθ1).le
  have hθsmall : -log (l ^ k) * complexity (l ^ k) ^ 10 ≤ 1 / (10 : ℝ) ^ 100 := by
    calc
      _ = (k : ℝ) * (-log l) * complexity (l ^ k) ^ 10 := by rw [log_pow]; ring
      _ ≤ (k : ℝ) * (2 * (1 - l)) * ((k : ℝ) * B) ^ 10 := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hχbound (Nat.cast_nonneg k)
        · exact pow_le_pow_left₀ hBP hcomplex 10
        · positivity
        · positivity
      _ = 2 * (1 - l) * (k : ℝ) ^ 11 * B ^ 10 := by ring
      _ ≤ 2 * (1 - l) * (101 * B) ^ 11 * B ^ 10 := by gcongr
      _ = (2 * 101 ^ 11) * ((1 - l) * B ^ 21) := by ring
      _ ≤ (1 / (10 : ℝ) ^ 100) := by
        have h := (le_div_iff₀ (by norm_num : (0 : ℝ) < 2 * 101 ^ 11)).mp hfinal
        nlinarith
  have hgain : 1 / (20 * B) ≤ integrabilityGain l := by
    unfold integrabilityGain
    apply one_div_le_one_div_of_le
    · have h := integrabilityGain_pos hl.le hl1
      have hL : 0 ≤ log ((1 - l)⁻¹) := by
        rw [log_inv]
        exact neg_nonneg.mpr (log_nonpos hg.le (by linarith))
      positivity
    · change 10 * (1 + log ((1 - l)⁻¹)) ≤ 20 * B
      rw [one_div] at hlog
      linarith
  have hgainθ := (integrabilityGain_antitone (pow_pos hl k).le
    (pow_le_self_of_pos hl.le hl1.le hk1) hl1)
  have hkreal : (1 : ℝ) < k := by exact_mod_cast hk2
  have hfrac : 1 / ((k : ℝ) - 1) ≤ 1 / (20 * B) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  refine ⟨k, hk2, hθhalf, hθ1, hθsmall, ?_⟩
  have he : (k : ℝ) / ((k : ℝ) - 1) = 1 + 1 / ((k : ℝ) - 1) := by
    field_simp [sub_ne_zero.mpr hkreal.ne']
    <;> ring
  rw [he]
  linarith [hfrac.trans (hgain.trans hgainθ)]

end LpSelfSimilar.Algebraic
