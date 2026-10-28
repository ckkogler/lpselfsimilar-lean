module

public import LpSelfSimilar.Bernoulli.FiniteLaw
public import LpSelfSimilar.Entropy.UniformWordSubset
public import Mathlib.Logic.Equiv.Set

@[expose] public section

/-!
Sparse digit injectivity gives a quantitative entropy lower bound for the whole
Bernoulli word. Selected indices are the actual multiples j*k within the word,
with the uniform product law justified by the reusable subset theorem. For long
words we retain floor(n/k) digits; short nonempty words retain one digit. Both
rounding cases are included in the exact n/(8B) estimate when k<=2B.
-/

open MeasureTheory ProbabilityTheory
open LpSelfSimilar.Entropy

namespace LpSelfSimilar.Bernoulli

/-- Retaining m digits at spacing k gives at least m*log(2) entropy. -/
theorem digit_entropy_ge_sparse_length {r : ℝ} {k m n : ℕ} (hk : 0 < k)
    (hmn : m * k ≤ n) (hinj : Function.Injective (digitSum (r ^ k) (n := m))) :
    (m : ℝ) * Real.log 2 ≤ finiteEntropy (digitPMF r n) (digitPMF_support_finite _ _) := by
  classical
  let f : Fin m → Fin n := fun j ↦ ⟨j * k,
    (Nat.mul_lt_mul_of_pos_right j.isLt hk).trans_le hmn⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact Nat.eq_of_mul_eq_mul_right hk (congrArg Fin.val hij)
  let P : Fin n → Prop := fun i ↦ i ∈ Set.range f
  let : Fintype {i : Fin n // P i} := Subtype.fintype P
  let e : Fin m ≃ {i : Fin n // P i} := Equiv.ofInjective f hf
  have hsum (w : {i : Fin n // P i} → Bool) :
      (∑ i : {i : Fin n // P i}, sign (w i) * r ^ ((i : Fin n) : ℕ)) =
        digitSum (r ^ k) (fun j ↦ w (e j)) := by
    rw [← e.sum_comp (fun i ↦ sign (w i) * r ^ ((i : Fin n) : ℕ)), digitSum]
    apply Finset.sum_congr rfl
    intro j _
    change sign (w (e j)) * r ^ ((j : ℕ) * k) = sign (w (e j)) * (r ^ k) ^ (j : ℕ)
    rw [← pow_mul, Nat.mul_comm]
  have hsub : Function.Injective (fun w : {i : Fin n // P i} → Bool ↦
      ∑ i : {i : Fin n // P i}, sign (w i) * r ^ ((i : Fin n) : ℕ)) := by
    intro u v huv
    simp only [hsum] at huv
    have h := hinj huv
    funext i
    simpa using congrFun h (e.symm i)
  have h := entropy_uniform_word_ge_log_card_subset P
    (fun (i : Fin n) d ↦ sign d * r ^ (i : ℕ)) hsub
  have hcard : Fintype.card {i : Fin n // P i} = m := by
    simpa using (Fintype.card_congr e).symm
  have hstat : (fun w : Fin n → Bool ↦ ∑ i, sign (w i) * r ^ (i : ℕ)) = digitSum r := rfl
  simpa only [hstat, digitPMF, Fintype.card_fun, Fintype.card_bool, hcard, Nat.cast_pow,
    Nat.cast_ofNat, Real.log_pow] using h

lemma digitSum_one_injective (r : ℝ) : Function.Injective (digitSum r (n := 1)) := by
  intro u v huv
  funext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  have he : sign (u 0) = sign (v 0) := by simpa [digitSum] using huv
  cases hu : u 0 <;> cases hv : v 0 <;> simp_all [sign] <;> norm_num at *

lemma digit_entropy_ge_log_two {r : ℝ} {n : ℕ} (hn : 0 < n) :
    Real.log 2 ≤ finiteEntropy (digitPMF r n) (digitPMF_support_finite _ _) := by
  have h := digit_entropy_ge_sparse_length (r := r) (m := 1) (k := 1)
    (by omega) (by omega : 1 * 1 ≤ n) (by simpa using digitSum_one_injective r)
  simpa using h

/-- Elementary lower bound, including short and empty words. The paper's
constant eight follows only from k<=2B and log(2)>=1/2. -/
theorem digit_entropy_ge_div_eight_of_sparse_injectivity {r B : ℝ} (hB : 0 < B)
    {k : ℕ} (hk : 0 < k) (hkB : (k : ℝ) ≤ 2 * B)
    (hinj : ∀ n : ℕ, Function.Injective (digitSum (r ^ k) (n := n))) (n : ℕ) :
    (n : ℝ) / (8 * B) ≤ finiteEntropy (digitPMF r n) (digitPMF_support_finite _ _) := by
  have hlog : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
    rw [Real.log_inv] at h
    norm_num at h
    linarith
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using finiteEntropy_nonneg (digitPMF r 0) (digitPMF_support_finite _ _)
  by_cases hnk : n < k
  · have hnB : (n : ℝ) ≤ 2 * B := (by exact_mod_cast hnk.le : (n : ℝ) ≤ k).trans hkB
    apply le_trans _ (digit_entropy_ge_log_two hn)
    apply (div_le_iff₀ (by positivity : 0 < 8 * B)).mpr
    nlinarith
  · have hkn : k ≤ n := Nat.le_of_not_gt hnk
    have hm1 : 1 ≤ n / k := (Nat.le_div_iff_mul_le hk).mpr (by simpa using hkn)
    have hnround : n ≤ 2 * k * (n / k) := by
      have hmod := Nat.mod_lt n hk
      have hdiv := Nat.mod_add_div n k
      have hkm : k ≤ k * (n / k) := by nlinarith
      nlinarith
    have hnreal : (n : ℝ) ≤ 4 * B * (n / k : ℕ) := by
      have hnr : (n : ℝ) ≤ 2 * (k : ℝ) * (n / k : ℕ) := by exact_mod_cast hnround
      have hmul := mul_le_mul_of_nonneg_right hkB (Nat.cast_nonneg (n / k) : (0 : ℝ) ≤ _)
      nlinarith
    calc
      (n : ℝ) / (8 * B) ≤ (n / k : ℕ) / (2 : ℝ) := by
        apply (div_le_iff₀ (by positivity : 0 < 8 * B)).mpr
        nlinarith
      _ ≤ (n / k : ℕ) * Real.log 2 := by
        have h := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (n / k) : (0 : ℝ) ≤ _)
        nlinarith
      _ ≤ _ := digit_entropy_ge_sparse_length hk (Nat.div_mul_le_self n k) (hinj (n / k))

end LpSelfSimilar.Bernoulli
