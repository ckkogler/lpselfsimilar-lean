module

public import LpSelfSimilar.Bernoulli.Digits
public import Mathlib.Algebra.Polynomial.OfFn

@[expose] public section

/-!
Integer polynomials encoding finite Bernoulli words and their differences.

Binary digits give coefficients zero and one. Their difference therefore has
coefficients in {-1,0,1}; the signed digit difference is twice its evaluation.
Polynomial injectivity is unconditional, while injectivity after evaluation
depends on the parameter and is deliberately kept separate.
-/

open Polynomial

namespace LpSelfSimilar.Bernoulli

/-- The integer polynomial whose coefficients are the binary digits of a word. -/
noncomputable def wordPolynomial {n : ℕ} (w : Fin n → Bool) : ℤ[X] :=
  ofFn n (fun j ↦ if w j then 1 else 0)

/-- Half the signed digit difference, before evaluating at a parameter. -/
noncomputable def differencePolynomial {n : ℕ} (u v : Fin n → Bool) : ℤ[X] :=
  wordPolynomial u - wordPolynomial v

lemma wordPolynomial_coeff {n : ℕ} (w : Fin n → Bool) (j : Fin n) :
    (wordPolynomial w).coeff j = if w j then 1 else 0 :=
  ofFn_coeff_eq_val_of_lt _ j.isLt

lemma wordPolynomial_coeff_of_ge {n : ℕ} (w : Fin n → Bool) {j : ℕ} (hj : n ≤ j) :
    (wordPolynomial w).coeff j = 0 := ofFn_coeff_eq_zero_of_ge _ hj

lemma wordPolynomial_natDegree_lt {n : ℕ} (hn : 1 ≤ n) (w : Fin n → Bool) :
    (wordPolynomial w).natDegree < n := ofFn_natDegree_lt hn _

lemma differencePolynomial_natDegree_lt {n : ℕ} (hn : 1 ≤ n) (u v : Fin n → Bool) :
    (differencePolynomial u v).natDegree < n :=
  (natDegree_sub_le (wordPolynomial u) (wordPolynomial v)).trans_lt
    (max_lt (wordPolynomial_natDegree_lt hn u)
    (wordPolynomial_natDegree_lt hn v))

lemma wordPolynomial_aeval (x : ℝ) {n : ℕ} (w : Fin n → Bool) :
    aeval x (wordPolynomial w) = bitSum x w := by
  rw [wordPolynomial, ofFn_eq_sum_monomial, map_sum, bitSum]
  apply Finset.sum_congr rfl
  intro j _
  rw [aeval_monomial]
  cases w j <;> simp

lemma digitSum_sub_eq_two_mul_aeval (x : ℝ) {n : ℕ} (u v : Fin n → Bool) :
    digitSum x u - digitSum x v = 2 * aeval x (differencePolynomial u v) := by
  rw [differencePolynomial, map_sub, wordPolynomial_aeval, wordPolynomial_aeval,
    digitSum_eq_two_mul_bitSum_sub, digitSum_eq_two_mul_bitSum_sub]
  ring

lemma differencePolynomial_coeff_abs_le {n : ℕ} (u v : Fin n → Bool) (j : ℕ) :
    |(differencePolynomial u v).coeff j| ≤ 1 := by
  rw [differencePolynomial, coeff_sub]
  by_cases hj : j < n
  · rw [wordPolynomial_coeff u ⟨j, hj⟩, wordPolynomial_coeff v ⟨j, hj⟩]
    cases u ⟨j, hj⟩ <;> cases v ⟨j, hj⟩ <;> norm_num
  · rw [wordPolynomial_coeff_of_ge u (Nat.le_of_not_gt hj),
      wordPolynomial_coeff_of_ge v (Nat.le_of_not_gt hj)]
    norm_num

lemma wordPolynomial_injective (n : ℕ) : Function.Injective (wordPolynomial (n := n)) := by
  intro u v huv
  funext j
  have h := congrArg (fun p : ℤ[X] ↦ p.coeff j) huv
  rw [wordPolynomial_coeff, wordPolynomial_coeff] at h
  cases hu : u j <;> cases hv : v j <;> simp_all

lemma differencePolynomial_ne_zero {n : ℕ} {u v : Fin n → Bool} (huv : u ≠ v) :
    differencePolynomial u v ≠ 0 := by
  intro h
  exact huv (wordPolynomial_injective n (sub_eq_zero.mp h))

end LpSelfSimilar.Bernoulli
