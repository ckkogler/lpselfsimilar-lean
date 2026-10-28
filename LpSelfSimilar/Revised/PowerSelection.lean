module

public import LpSelfSimilar.Algebraic.ComplexityPowers
public import LpSelfSimilar.Algebraic.GapEstimate
public import LpSelfSimilar.Analysis.LargeComplexity
public import LpSelfSimilar.Bernoulli.PowerBounds
public import LpSelfSimilar.Analysis.ExponentialTailNumerics

/-!
# The revised logarithmic power selection

The proof of Theorem 1.2 in Kittle–Kogler selects
`floor (20 - 20 log (1-lambda))`. The following estimates verify that exact
choice. The final smallness estimate also follows from the preserved stronger
polynomial gap bound; no choice of a different integer is substituted.
-/

@[expose] public section

open Real Set
open LpSelfSimilar.Algebraic LpSelfSimilar.Bernoulli

namespace LpSelfSimilar.Revised

/-- The exact integer chosen in the revised proof of Theorem 1.2. -/
noncomputable def smoothingPower (l : ℝ) : ℕ := ⌊20 - 20 * log (1 - l)⌋₊

/-- The logarithmic gap bounds used in the revised exponent-100 argument. -/
theorem logarithmic_gap_bounds {l : ℝ} (halg : IsAlgebraic ℚ l)
    (hl0 : 1 / 2 < l) (hl1 : l < 1)
    (hsmall : (1 - l) * complexity l ^ 100 ≤ 1) :
    100 * log (complexity l) ≤ -log (1 - l) ∧
      -log (1 - l) ≤ complexity l ∧
      400 < -log (1 - l) ∧
      complexity l ^ 10 ≤ exp (-log (1 - l) / 10) := by
  have hl : 0 < l := by linarith
  have hg : 0 < 1 - l := by linarith
  have hB0 := complexity_pos halg hl hl1
  have hB3 := three_le_complexity halg hl hl1
  have hlog := log_inverse_gap_le_complexity halg hl hl1
  have hB600 := six_hundred_lt_of_small_gap hB3 hg hlog (by linarith)
  have hlogprod := log_le_log (mul_pos hg (pow_pos hB0 100)) hsmall
  rw [log_one, log_mul hg.ne' (pow_pos hB0 100).ne', log_pow] at hlogprod
  norm_num only [Nat.cast_ofNat] at hlogprod
  have hlo : 100 * log (complexity l) ≤ -log (1 - l) := by linarith
  have hup : -log (1 - l) ≤ complexity l := by
    simpa only [one_div, log_inv] using hlog
  have hlogB : 4 < log (complexity l) := by
    have hh := log_le_log (by norm_num : (0 : ℝ) < 2 ^ 6)
      (by linarith : (2 : ℝ) ^ 6 ≤ complexity l)
    rw [log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith [log_two_gt_d9]
  refine ⟨hlo, hup, by linarith, ?_⟩
  rw [← exp_log (pow_pos hB0 10), log_pow]
  apply exp_le_exp.mpr
  norm_num only [Nat.cast_ofNat]
  linarith

/-- The revised floor choice has the exact exponent gain and smallness needed
for Proposition 3.1 and Young's inequality. -/
theorem smoothingPower_spec {l : ℝ} (halg : IsAlgebraic ℚ l)
    (hl0 : 1 / 2 < l) (hl1 : l < 1)
    (hsmall : (1 - l) * complexity l ^ 100 ≤ 1) :
    2 ≤ smoothingPower l ∧
      11 - 10 * log (1 - l) ≤ (smoothingPower l : ℝ) ∧
      (smoothingPower l : ℝ) ≤ 20 - 20 * log (1 - l) ∧
      1 / 2 < l ^ smoothingPower l ∧ l ^ smoothingPower l < 1 ∧
      -log (l ^ smoothingPower l) * complexity (l ^ smoothingPower l) ^ 10 ≤
        1 / (10 : ℝ) ^ 100 ∧
      (smoothingPower l : ℝ) / ((smoothingPower l : ℝ) - 1) ≤
        1 + integrabilityGain (l ^ smoothingPower l) := by
  let B := complexity l
  let k := smoothingPower l
  have hl : 0 < l := by linarith
  have hg : 0 < 1 - l := by linarith
  have hB : 3 ≤ B := three_le_complexity halg hl hl1
  have hB0 : 0 < B := complexity_pos halg hl hl1
  have hbounds := logarithmic_gap_bounds halg hl0 hl1 hsmall
  have ht : 0 < -log (1 - l) := by linarith [hbounds.2.2.1]
  have hkhi : (k : ℝ) ≤ 20 - 20 * log (1 - l) :=
    Nat.floor_le (by linarith)
  have hklo : 20 - 20 * log (1 - l) < (k : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hkgain : 11 - 10 * log (1 - l) ≤ (k : ℝ) := by linarith
  have hk2 : 2 ≤ k := by
    have hh : (2 : ℝ) ≤ k := by linarith
    exact_mod_cast hh
  have hkpos : 0 < k := by omega
  have hkB : (k : ℝ) ≤ 101 * B := by linarith [hbounds.2.1]
  have hlog := log_inverse_gap_le_complexity halg hl hl1
  have hB600 : 600 < B := six_hundred_lt_of_small_gap hB hg hlog (by linarith)
  have hfinal : (1 - l) * B ^ 21 ≤ (1 / (10 : ℝ) ^ 100) / (2 * 101 ^ 11) :=
    gap_power_twenty_one_bound hB600.le hg.le (by linarith)
  have hpowB : B ≤ B ^ 21 := by
    simpa using pow_le_pow_right₀ (by linarith : 1 ≤ B)
      (show 1 ≤ (21 : ℕ) by norm_num)
  have hgapB : (1 - l) * B ≤ 1 / 1000 :=
    (mul_le_mul_of_nonneg_left hpowB hg.le).trans (hfinal.trans (by norm_num))
  have hkGap : (k : ℝ) * (1 - l) ≤ 101 / 1000 := by
    have hh := mul_le_mul_of_nonneg_right hkB hg.le
    linarith
  have hθhalf : (1 : ℝ) / 2 < l ^ k := by
    have hh := one_sub_mul_gap_le_pow hl.le k
    linarith
  have hθ1 : l ^ k < 1 := pow_lt_one₀ hl.le hl1 hkpos.ne'
  have hχbound := logarithmic_contraction_le_twice_gap hl0.le hl1
  have hcomplex := complexity_pow_le_mul halg hl hl1 hkpos
  have hBP : 0 ≤ complexity (l ^ k) :=
    (complexity_pos (isAlgebraic_pow halg k) (pow_pos hl k) hθ1).le
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
      _ ≤ 1 / (10 : ℝ) ^ 100 := by
        have hh := (le_div_iff₀ (by norm_num : (0 : ℝ) < 2 * 101 ^ 11)).mp hfinal
        nlinarith
  have hgain : 1 / ((k : ℝ) - 1) ≤ integrabilityGain l := by
    unfold integrabilityGain
    rw [log_inv]
    apply one_div_le_one_div_of_le
    · linarith
    · linarith
  have hgainθ := integrabilityGain_antitone (pow_pos hl k).le
    (pow_le_self_of_pos hl.le hl1.le (by omega : 1 ≤ k)) hl1
  have hkreal : (1 : ℝ) < k := by exact_mod_cast hk2
  have he : (k : ℝ) / ((k : ℝ) - 1) = 1 + 1 / ((k : ℝ) - 1) := by
    field_simp [sub_ne_zero.mpr hkreal.ne']
    ring
  refine ⟨hk2, hkgain, hkhi, hθhalf, hθ1, hθsmall, ?_⟩
  rw [he]
  linarith

/-- The exponential-polynomial majorant displayed in the proof of (3.3),
for the actual revised power choice. -/
theorem smoothingPower_cost_bound {l : ℝ} (halg : IsAlgebraic ℚ l)
    (hl0 : 1 / 2 < l) (hl1 : l < 1)
    (hsmall : (1 - l) * complexity l ^ 100 ≤ 1) :
    -log (l ^ smoothingPower l) * complexity (l ^ smoothingPower l) ^ 10 ≤
      2 * (20 : ℝ) ^ 11 * (1 - log (1 - l)) ^ 11 * exp (9 * log (1 - l) / 10) := by
  let k := smoothingPower l
  let t := -log (1 - l)
  have hl : 0 < l := by linarith
  have hg : 0 < 1 - l := by linarith
  have hspec := smoothingPower_spec halg hl0 hl1 hsmall
  have hk : 0 < k := by omega
  have hθ1 : l ^ k < 1 := hspec.2.2.2.2.1
  have hB0 := complexity_pos halg hl hl1
  have hBP : 0 ≤ complexity (l ^ k) :=
    (complexity_pos (isAlgebraic_pow halg k) (pow_pos hl k) hθ1).le
  have hcomplex := complexity_pow_le_mul halg hl hl1 hk
  have hχbound := logarithmic_contraction_le_twice_gap hl0.le hl1
  have hbounds := logarithmic_gap_bounds halg hl0 hl1 hsmall
  have ht0 : 0 < t := by dsimp [t]; linarith [hbounds.2.2.1]
  have hkbound : (k : ℝ) ≤ 20 * (1 + t) := by
    dsimp [k, t]
    linarith [hspec.2.2.1]
  have hgap : 1 - l = exp (-t) := by simp [t, exp_log hg]
  have hBpow : complexity l ^ 10 ≤ exp (t / 10) := hbounds.2.2.2
  calc
    _ = (k : ℝ) * (-log l) * complexity (l ^ k) ^ 10 := by rw [log_pow]; ring
    _ ≤ (k : ℝ) * (2 * (1 - l)) * ((k : ℝ) * complexity l) ^ 10 := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hχbound (Nat.cast_nonneg k)
      · exact pow_le_pow_left₀ hBP hcomplex 10
      · positivity
      · positivity
    _ = 2 * (1 - l) * (k : ℝ) ^ 11 * complexity l ^ 10 := by ring
    _ ≤ 2 * (1 - l) * (20 * (1 + t)) ^ 11 * exp (t / 10) := by gcongr
    _ = 2 * (20 : ℝ) ^ 11 * (1 + t) ^ 11 * exp (-9 * t / 10) := by
      rw [hgap]
      have he : exp (-t) * exp (t / 10) = exp (-9 * t / 10) := by
        rw [← exp_add]
        congr 1
        ring
      calc
        _ = (2 * (20 : ℝ) ^ 11 * (1 + t) ^ 11) * (exp (-t) * exp (t / 10)) := by ring
        _ = _ := by rw [he]
    _ = _ := by dsimp [t]; congr 2; ring

/-- The exponential-polynomial expression in the revised proof decreases
throughout the stated range `t ≥ 400`. -/
theorem power_selection_profile_antitone :
    AntitoneOn (fun t : ℝ ↦ (1 + t) ^ 11 * exp (-9 * t / 10)) (Ici 400) := by
  have hd (t : ℝ) : HasDerivAt (fun x : ℝ ↦ (1 + x) ^ 11 * exp (-9 * x / 10))
      ((1 + t) ^ 10 * (11 - (9 / 10) * (1 + t)) * exp (-9 * t / 10)) t := by
    convert! (((hasDerivAt_id t).const_add 1).pow 11).mul
      ((((hasDerivAt_id t).const_mul (-9)).div_const 10).exp) using 1
    simp only [Pi.pow_apply, id_eq]
    ring
  apply antitoneOn_of_deriv_nonpos (convex_Ici 400)
  · fun_prop
  · intro t ht
    exact (hd t).differentiableAt.differentiableWithinAt
  · intro t ht
    have ht' : 400 ≤ t := interior_subset ht
    rw [(hd t).deriv]
    apply mul_nonpos_of_nonpos_of_nonneg _ (exp_pos _).le
    exact mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (by linarith) 10) (by linarith)

/-- The exact numerical endpoint displayed in the revised proof. -/
theorem power_selection_exponential_endpoint :
    2 * (20 : ℝ) ^ 11 * 401 ^ 11 * exp (-360) < 1 / (10 : ℝ) ^ 100 := by
  have he : (27 / 10 : ℝ) ^ 360 ≤ exp 360 :=
    Analysis.rational_pow_le_exp_nat 360
  have hnum : 2 * (20 : ℝ) ^ 11 * 401 ^ 11 * (10 : ℝ) ^ 100 < exp 360 :=
    lt_of_lt_of_le (by
      rw [show (360 : ℕ) = 180 * 2 by norm_num, pow_mul]
      norm_num) he
  rw [exp_neg, ← div_eq_mul_inv]
  exact (div_lt_div_iff₀ (exp_pos 360) (by norm_num : (0 : ℝ) < 10 ^ 100)).mpr
    (by simpa only [one_mul] using hnum)

/-- The uniform exponential numerical bound used to establish (3.3). -/
theorem power_selection_exponential_bound {t : ℝ} (ht : 400 ≤ t) :
    2 * (20 : ℝ) ^ 11 * (1 + t) ^ 11 * exp (-9 * t / 10) <
      1 / (10 : ℝ) ^ 100 := by
  have h := power_selection_profile_antitone (show (400 : ℝ) ∈ Ici 400 by simp)
    (show t ∈ Ici 400 from ht) ht
  dsimp only at h
  rw [show (1 + (400 : ℝ)) = 401 by norm_num,
    show (-9 * (400 : ℝ) / 10) = -360 by norm_num] at h
  calc
    _ = (2 * (20 : ℝ) ^ 11) * ((1 + t) ^ 11 * exp (-9 * t / 10)) := by ring
    _ ≤ (2 * (20 : ℝ) ^ 11) * (401 ^ 11 * exp (-360)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = 2 * (20 : ℝ) ^ 11 * 401 ^ 11 * exp (-360) := by ring
    _ < 1 / (10 : ℝ) ^ 100 := power_selection_exponential_endpoint

end LpSelfSimilar.Revised
