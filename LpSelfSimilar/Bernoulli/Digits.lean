module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Tactic

@[expose] public section

/-!
Finite and infinite fair-sign expansions. This module contains the deterministic
identities underlying Bernoulli convolutions; probability enters in Construction.
The digits are Booleans, with false representing -1 and true representing +1.
-/

open scoped BigOperators

namespace LpSelfSimilar.Bernoulli

/-- The sign associated to a binary digit. -/
def sign (e : Bool) : ℝ := if e then 1 else -1

@[simp] lemma sign_false : sign false = -1 := rfl
@[simp] lemma sign_true : sign true = 1 := rfl
@[simp] lemma abs_sign (e : Bool) : |sign e| = 1 := by cases e <;> norm_num [sign]
@[simp] lemma norm_sign (e : Bool) : ‖sign e‖ = 1 := abs_sign e

/-- A finite signed digit sum, with the lowest power first. -/
noncomputable def digitSum (r : ℝ) {n : ℕ} (w : Fin n → Bool) : ℝ :=
  ∑ j, sign (w j) * r ^ (j : ℕ)

/-- The same finite expansion with digits zero and one. -/
noncomputable def bitSum (r : ℝ) {n : ℕ} (w : Fin n → Bool) : ℝ :=
  ∑ j, (if w j then 1 else 0) * r ^ (j : ℕ)

lemma digitSum_eq_two_mul_bitSum_sub (r : ℝ) {n : ℕ} (w : Fin n → Bool) :
    digitSum r w = 2 * bitSum r w - ∑ j : Fin n, r ^ (j : ℕ) := by
  rw [digitSum, bitSum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  cases w j <;> simp [sign] <;> ring

@[simp] lemma bitSum_zero (r : ℝ) (w : Fin 0 → Bool) : bitSum r w = 0 := by
  simp [bitSum]

lemma bitSum_succ (r : ℝ) {n : ℕ} (w : Fin (n + 1) → Bool) :
    bitSum r w = (if w 0 then 1 else 0) + r * bitSum r (fun j ↦ w j.succ) := by
  rw [bitSum, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
  rw [bitSum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The random series whose law is the Bernoulli convolution. -/
noncomputable def series (r : ℝ) (w : ℕ → Bool) : ℝ :=
  ∑' j, sign (w j) * r ^ j

lemma summable_sign_mul_pow {r : ℝ} (hr : |r| < 1) (w : ℕ → Bool) :
    Summable (fun j ↦ sign (w j) * r ^ j) := by
  apply Summable.of_norm
  simpa [norm_mul, norm_pow] using summable_geometric_of_lt_one (abs_nonneg r) hr

lemma abs_series_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (w : ℕ → Bool) :
    |series r w| ≤ (1 - r)⁻¹ := by
  have hs : Summable (fun j ↦ ‖sign (w j) * r ^ j‖) := by
    simpa [norm_mul, norm_pow, abs_of_nonneg hr0] using
      summable_geometric_of_lt_one hr0 hr1
  calc
    |series r w| ≤ ∑' j, ‖sign (w j) * r ^ j‖ := norm_tsum_le_tsum_norm hs
    _ = (1 - r)⁻¹ := by
      simp only [norm_mul, norm_pow, Real.norm_eq_abs, abs_sign, one_mul,
        abs_of_nonneg hr0]
      exact tsum_geometric_of_lt_one hr0 hr1

lemma series_eq_head_add_tail {r : ℝ} (hr : |r| < 1) (w : ℕ → Bool) :
    series r w = sign (w 0) + r * series r (fun j ↦ w (j + 1)) := by
  rw [series, (summable_sign_mul_pow hr w).tsum_eq_zero_add]
  simp only [pow_zero, mul_one]
  congr 1
  rw [series, ← tsum_mul_left]
  apply tsum_congr
  intro j
  rw [pow_succ]
  ring

end LpSelfSimilar.Bernoulli
