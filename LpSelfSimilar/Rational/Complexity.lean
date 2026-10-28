module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
The rational complexity used in place of the degree/Mahler complexity of
Section 3. Every logarithm is a real natural logarithm. Bounds are uniform in
the numerator and denominator; in particular the power bound controls the
digit splitting step without appealing to algebraic heights.
-/

namespace LpSelfSimilar.Rational

/-- For a reduced rational parameter `a/b`, its Section 3 complexity. -/
noncomputable def complexity (b : ℕ) : ℝ :=
  (2 + Real.log (b : ℝ)) / min 1 (Real.log (b : ℝ))

lemma log_denominator_pos {b : ℕ} (hb : 2 ≤ b) : 0 < Real.log (b : ℝ) :=
  Real.log_pos (by exact_mod_cast hb)

lemma complexity_pos {b : ℕ} (hb : 2 ≤ b) : 0 < complexity b := by
  have h := log_denominator_pos hb
  exact div_pos (by linarith) (lt_min zero_lt_one h)

lemma log_denominator_le_complexity {b : ℕ} (hb : 2 ≤ b) :
    Real.log (b : ℝ) ≤ complexity b := by
  have h := log_denominator_pos hb
  apply (le_div_iff₀ (lt_min zero_lt_one h)).mpr
  have hmul := mul_le_mul_of_nonneg_left (min_le_left 1 (Real.log (b : ℝ))) h.le
  linarith

lemma two_le_complexity {b : ℕ} (hb : 2 ≤ b) : 2 ≤ complexity b := by
  have h := log_denominator_pos hb
  apply (le_div_iff₀ (lt_min zero_lt_one h)).mpr
  have hm := min_le_left 1 (Real.log (b : ℝ))
  linarith

/-- Passing to a positive power multiplies complexity by at most that power. -/
lemma complexity_pow_le {b k : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) :
    complexity (b ^ k) ≤ (k : ℝ) * complexity b := by
  have hlog := log_denominator_pos hb
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hden : 0 < min 1 (Real.log (b : ℝ)) := lt_min zero_lt_one hlog
  have hlogpow : Real.log ((b ^ k : ℕ) : ℝ) = k * Real.log (b : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
  have hmono : min 1 (Real.log (b : ℝ)) ≤ min 1 ((k : ℝ) * Real.log (b : ℝ)) := by
    apply min_le_min le_rfl
    nlinarith
  unfold complexity
  rw [hlogpow]
  calc
    (2 + (k : ℝ) * Real.log (b : ℝ)) / min 1 ((k : ℝ) * Real.log (b : ℝ)) ≤
        (2 + (k : ℝ) * Real.log (b : ℝ)) / min 1 (Real.log (b : ℝ)) :=
      div_le_div_of_nonneg_left (by positivity) hden hmono
    _ ≤ (k : ℝ) * ((2 + Real.log (b : ℝ)) / min 1 (Real.log (b : ℝ))) := by
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ hden.le
      nlinarith

/-- A reduced parameter in `(1/2,1)` has numerator at least two and denominator
at least three. The integer inequalities make the boundary cases explicit. -/
lemma numerator_denominator_bounds {a b : ℕ} (hb : 0 < b)
    (hhalf : (1 : ℝ) / 2 < (a : ℝ) / b) (hone : (a : ℝ) / b < 1) :
    2 ≤ a ∧ 3 ≤ b := by
  have hb' : (0 : ℝ) < b := by positivity
  have hab : a < b := by exact_mod_cast (div_lt_one hb').mp hone
  have hba : (b : ℝ) < 2 * a := by
    have h := (lt_div_iff₀ hb').mp hhalf
    linarith
  have hba' : b < 2 * a := by exact_mod_cast hba
  omega

lemma log_inverse_gap_le {a b : ℕ} (hb : 2 ≤ b) (hab : a < b) :
    Real.log (1 / (1 - (a : ℝ) / b)) ≤ complexity b := by
  have hb' : (0 : ℝ) < b := by positivity
  have hgap : 0 < 1 - (a : ℝ) / b := sub_pos.mpr ((div_lt_one hb').mpr (by exact_mod_cast hab))
  have hdiff : (a : ℝ) + 1 ≤ b := by exact_mod_cast hab
  have hinv : 1 / (1 - (a : ℝ) / b) ≤ (b : ℝ) := by
    apply (div_le_iff₀ hgap).mpr
    have hcancel := div_mul_cancel₀ (a : ℝ) hb'.ne'
    nlinarith
  exact (Real.log_le_log (by positivity) hinv).trans (log_denominator_le_complexity hb)

/-- A fixed comparison factor, independent of every rational parameter. -/
noncomputable def complexityFactor : ℝ :=
  (2 / Real.log 2 + 1) / min 1 (Real.log 2)

lemma complexityFactor_pos : 0 < complexityFactor := by
  have h : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact div_pos (by positivity) (lt_min zero_lt_one h)

lemma complexity_le_factor_mul_log {b : ℕ} (hb : 2 ≤ b) :
    complexity b ≤ complexityFactor * Real.log (b : ℝ) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log (b : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hb)
  have hm : 0 < min 1 (Real.log 2) := lt_min zero_lt_one h2
  have hb' : 0 < Real.log (b : ℝ) := h2.trans_le hlog
  calc
    complexity b ≤ (2 + Real.log (b : ℝ)) / min 1 (Real.log 2) :=
      div_le_div_of_nonneg_left (by positivity) hm (min_le_min le_rfl hlog)
    _ ≤ ((2 / Real.log 2 + 1) * Real.log (b : ℝ)) / min 1 (Real.log 2) := by
      apply div_le_div_of_nonneg_right _ hm.le
      have hmul := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 2 / Real.log 2)
      rw [div_mul_cancel₀ _ h2.ne'] at hmul
      nlinarith
    _ = complexityFactor * Real.log (b : ℝ) := by unfold complexityFactor; ring

/-- Conversion of the exact exponent-50 hypothesis to the rational complexity
condition. The chosen constant depends only on the single target threshold,
not on either integer parameter. -/
lemma exists_uniform_constant_for_complexity (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ (p q : ℕ), 2 ≤ q →
      (p : ℝ) ≤ c * q / (Real.log (q : ℝ)) ^ 50 →
      ((p : ℝ) / q) * complexity q ^ 50 < c₀ := by
  let c := c₀ / (2 * complexityFactor ^ 50)
  have hD := complexityFactor_pos
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  intro p q hq hp
  have hq' : (0 : ℝ) < q := by positivity
  have hlog := log_denominator_pos hq
  have hB := complexity_pos hq
  have hp' : (p : ℝ) / q ≤ c / (Real.log (q : ℝ)) ^ 50 := by
    apply (div_le_iff₀ hq').mpr
    simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hp
  calc
    ((p : ℝ) / q) * complexity q ^ 50 ≤
        (c / (Real.log (q : ℝ)) ^ 50) * (complexityFactor * Real.log (q : ℝ)) ^ 50 :=
      mul_le_mul hp' (pow_le_pow_left₀ hB.le (complexity_le_factor_mul_log hq) _)
        (by positivity) (by positivity)
    _ = c₀ / 2 := by dsimp [c]; field_simp
    _ < c₀ := by linarith

end LpSelfSimilar.Rational
