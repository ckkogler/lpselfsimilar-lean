module

public import LpSelfSimilar.Rational.HigherIntegrability
public import LpSelfSimilar.Rational.Parameters
public import LpSelfSimilar.Bernoulli.PowerBounds

@[expose] public section

/-!
Selection of a rational power for the final convolution argument. The threshold
is absolute, the rational complexity grows at most linearly, and all losses are
absorbed in the exact exponent fifty of the corollary's parameter condition.
-/

open Real
open LpSelfSimilar.Bernoulli

namespace LpSelfSimilar.Rational

noncomputable def powerThreshold : ℝ :=
  min (1 / 1000) (higherIntegrabilityThreshold / (2 * 101 ^ 11))

lemma powerThreshold_pos : 0 < powerThreshold := by
  have h := higherIntegrabilityThreshold_pos
  unfold powerThreshold
  positivity

/-- The power k=ceil(100B) stays above 1/2 and satisfies Proposition 3.1. -/
theorem exists_smoothing_power {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hl0 : 1 / 2 ≤ (a : ℝ) / b) (hl1 : (a : ℝ) / b < 1)
    (hsmall : (1 - (a : ℝ) / b) * complexity b ^ 50 ≤ powerThreshold) :
    ∃ k : ℕ, 2 ≤ k ∧
      1 / 2 < ((a : ℝ) / b) ^ k ∧ ((a : ℝ) / b) ^ k < 1 ∧
      -log (((a : ℝ) / b) ^ k) * complexity (b ^ k) ^ 10 ≤ higherIntegrabilityThreshold ∧
      (k : ℝ) / ((k : ℝ) - 1) ≤ 1 + integrabilityGain (((a : ℝ) / b) ^ k) := by
  let l : ℝ := (a : ℝ) / b
  let B := complexity b
  let k : ℕ := ⌈100 * B⌉₊
  have hB : 2 ≤ B := two_le_complexity hb
  have hB0 : 0 < B := complexity_pos hb
  have hB1 : 1 ≤ B := by linarith
  have hl : 0 < l := by dsimp [l]; linarith
  have hg : 0 < 1 - l := by dsimp [l]; linarith
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
  have hpowB : B ≤ B ^ 50 := by
    simpa using pow_le_pow_right₀ hB1 (show 1 ≤ (50 : ℕ) by norm_num)
  have hgapB : (1 - l) * B ≤ 1 / 1000 :=
    (mul_le_mul_of_nonneg_left hpowB hg.le).trans (hsmall.trans (min_le_left _ _))
  have hkGap : (k : ℝ) * (1 - l) ≤ 101 / 1000 := by
    have h := mul_le_mul_of_nonneg_right hkhi hg.le
    linarith
  have hθhalf : (1 : ℝ) / 2 < l ^ k := by
    have h := one_sub_mul_gap_le_pow hl.le k
    linarith
  have hθ1 : l ^ k < 1 := pow_lt_one₀ hl.le hl1 (by omega)
  have hχ : 0 ≤ -log l := (neg_pos.mpr (log_neg hl hl1)).le
  have hχbound := logarithmic_contraction_le_twice_gap hl0 hl1
  have hcomplex := complexity_pow_le hb hk1
  have hbpow : 2 ≤ b ^ k := hb.trans (by
    simpa using pow_le_pow_right₀ (show 1 ≤ b by omega) hk1)
  have hBP : 0 ≤ complexity (b ^ k) := (complexity_pos hbpow).le
  have hθsmall : -log (l ^ k) * complexity (b ^ k) ^ 10 ≤ higherIntegrabilityThreshold := by
    have hB2150 : B ^ 21 ≤ B ^ 50 := pow_le_pow_right₀ hB1 (by norm_num)
    have hfinal : (1 - l) * B ^ 50 ≤ higherIntegrabilityThreshold / (2 * 101 ^ 11) :=
      hsmall.trans (min_le_right _ _)
    calc
      _ = (k : ℝ) * (-log l) * complexity (b ^ k) ^ 10 := by rw [log_pow]; ring
      _ ≤ (k : ℝ) * (2 * (1 - l)) * ((k : ℝ) * B) ^ 10 := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hχbound (Nat.cast_nonneg k)
        · exact pow_le_pow_left₀ hBP hcomplex 10
        · positivity
        · positivity
      _ = 2 * (1 - l) * (k : ℝ) ^ 11 * B ^ 10 := by ring
      _ ≤ 2 * (1 - l) * (101 * B) ^ 11 * B ^ 10 := by gcongr
      _ = (2 * 101 ^ 11) * ((1 - l) * B ^ 21) := by ring
      _ ≤ (2 * 101 ^ 11) * ((1 - l) * B ^ 50) := by gcongr
      _ ≤ higherIntegrabilityThreshold := by
        have h := (le_div_iff₀ (by norm_num : (0 : ℝ) < 2 * 101 ^ 11)).mp hfinal
        nlinarith
  have hablt : a < b := by
    exact_mod_cast (div_lt_one (by positivity : (0 : ℝ) < b)).mp hl1
  have hlog := log_inverse_gap_le hb hablt
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

end LpSelfSimilar.Rational
