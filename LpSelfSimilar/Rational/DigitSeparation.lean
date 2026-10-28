module

public import LpSelfSimilar.Bernoulli.Digits
public import Mathlib.Data.Nat.ModEq

@[expose] public section

/-!
Elementary separation for reduced rational Bernoulli parameters. Clearing
denominators gives an integer numerator. Reducing modulo the numerator of the
parameter recovers the first binary digit; induction recovers the entire word.
This replaces the rational-root argument in Lemma 3.6 without algebraic entropy
input. Signed sums are obtained by the affine change from zero/one digits.
-/

open scoped BigOperators
open LpSelfSimilar.Bernoulli

namespace LpSelfSimilar.Rational

/-- The integer numerator after clearing `b^(n-1)` in a binary digit sum. -/
def wordNumerator (a b : ℕ) : {n : ℕ} → (Fin n → Bool) → ℕ
  | 0, _ => 0
  | n + 1, w => (if w 0 then 1 else 0) * b ^ n +
      a * wordNumerator a b (fun j ↦ w j.succ)

lemma wordNumerator_injective {a b : ℕ} (ha : 2 ≤ a) (hab : a.Coprime b)
    (n : ℕ) : Function.Injective (@wordNumerator a b n) := by
  induction n with
  | zero => intro u v _; exact Subsingleton.elim _ _
  | succ n ih =>
    intro u v huv
    have hmod : (if u 0 then 1 else 0) * b ^ n ≡
        (if v 0 then 1 else 0) * b ^ n [MOD a] := by
      have h := congrArg (fun t ↦ t % a) huv
      simpa [wordNumerator, Nat.add_mod, Nat.ModEq] using h
    have hbit := hmod.cancel_right_of_coprime (hab.pow_right n)
    have hhead : u 0 = v 0 := by
      cases hu : u 0 <;> cases hv : v 0 <;> try rfl
      all_goals simp [hu, hv, Nat.ModEq, Nat.mod_eq_of_lt (by omega : 1 < a)] at hbit
    have htail : (fun j : Fin n ↦ u j.succ) = (fun j : Fin n ↦ v j.succ) := by
      apply ih
      simp only [wordNumerator, hhead, Nat.add_right_inj] at huv
      exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < a) huv
    funext j
    refine Fin.cases hhead (fun i ↦ congrFun htail i) j

lemma bitSum_mul_denominator (a b : ℕ) (hb : 0 < b) {n : ℕ}
    (w : Fin n → Bool) :
    bitSum ((a : ℝ) / b) w * (b : ℝ) ^ (n - 1) = wordNumerator a b w := by
  induction n with
  | zero => simp [bitSum, wordNumerator]
  | succ n ih =>
    cases n with
    | zero => simp [bitSum_succ, bitSum_zero, wordNumerator]
    | succ n =>
      rw [bitSum_succ, wordNumerator]
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
      have hcast : ((if w 0 then 1 else 0 : ℕ) : ℝ) = if w 0 then 1 else 0 := by
        cases w 0 <;> simp
      rw [hcast]
      have ht := ih (fun j ↦ w j.succ)
      simp only [Nat.add_sub_cancel] at ht
      rw [← ht, pow_succ]
      have hb' : (b : ℝ) ≠ 0 := by positivity
      field_simp
      <;> ring

/-- Distinct words have distinct real sums for a reduced rational parameter
whose numerator is at least two. This includes every rational in `(1/2,1)`. -/
lemma digitSum_injective {a b : ℕ} (ha : 2 ≤ a) (hb : 0 < b)
    (hab : a.Coprime b) (n : ℕ) :
    Function.Injective (digitSum ((a : ℝ) / b) (n := n)) := by
  intro u v h
  have hbit : bitSum ((a : ℝ) / b) u = bitSum ((a : ℝ) / b) v := by
    rw [digitSum_eq_two_mul_bitSum_sub, digitSum_eq_two_mul_bitSum_sub] at h
    linarith
  apply wordNumerator_injective ha hab n
  have hnum := congrArg (fun x : ℝ ↦ x * (b : ℝ) ^ (n - 1)) hbit
  rw [bitSum_mul_denominator a b hb, bitSum_mul_denominator a b hb] at hnum
  exact_mod_cast hnum

/-- The paper's separation bound `2 b^(1-n)`, written without a negative
natural exponent. For the empty word the distinctness hypothesis is impossible. -/
lemma digitSum_separation {a b : ℕ} (ha : 2 ≤ a) (hb : 0 < b)
    (hab : a.Coprime b) {n : ℕ} {u v : Fin n → Bool} (huv : u ≠ v) :
    2 / (b : ℝ) ^ (n - 1) ≤ |digitSum ((a : ℝ) / b) u - digitSum ((a : ℝ) / b) v| := by
  have hne : wordNumerator a b u ≠ wordNumerator a b v :=
    fun h ↦ huv (wordNumerator_injective ha hab n h)
  have hgap : 1 ≤ |(wordNumerator a b u : ℝ) - wordNumerator a b v| := by
    rcases lt_or_gt_of_ne hne with h | h
    · have h' : (wordNumerator a b u : ℝ) + 1 ≤ wordNumerator a b v := by
        exact_mod_cast h
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have h' : (wordNumerator a b v : ℝ) + 1 ≤ wordNumerator a b u := by
        exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]
      linarith
  have hden : 0 < (b : ℝ) ^ (n - 1) := by positivity
  apply (div_le_iff₀ hden).mpr
  rw [← abs_of_pos hden, ← abs_mul]
  have heq : (digitSum ((a : ℝ) / b) u - digitSum ((a : ℝ) / b) v) *
      (b : ℝ) ^ (n - 1) =
      2 * ((wordNumerator a b u : ℝ) - wordNumerator a b v) := by
    rw [digitSum_eq_two_mul_bitSum_sub, digitSum_eq_two_mul_bitSum_sub,
      show ∀ x y z t : ℝ, ((2*x-t)-(2*y-t))*z = 2*(x*z-y*z) by intros; ring,
      bitSum_mul_denominator a b hb, bitSum_mul_denominator a b hb]
  rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

end LpSelfSimilar.Rational
