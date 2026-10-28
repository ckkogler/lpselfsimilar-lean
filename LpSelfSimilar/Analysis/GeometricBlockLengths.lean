module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
A finite collection of geometrically separated integer lengths. An explicit
floor of a logarithmic ratio supplies enough scales for effective detail, with
coarse absolute constants that preserve the paper's later exponent bounds.
-/

open Real

namespace LpSelfSimilar

/-- At logarithmic scale R, there are at least log R/(2000B²) usable lengths. -/
theorem exists_geometric_block_lengths {B R : ℝ} (hB : 2 ≤ B)
    (hR : 1000 * B ^ 3 ≤ R) :
    ∃ (m : ℕ) (n : Fin m → ℕ),
      log R / (2000 * B ^ 2) ≤ (m : ℝ) ∧
      (∀ i, 100 * B ^ 2 ≤ (n i : ℝ)) ∧
      (∀ i, 2 * B * n i ≤ R) ∧
      (∀ i j, i ≠ j →
        400 * B ^ 2 * (n i : ℝ) ≤ n j ∨
        400 * B ^ 2 * (n j : ℝ) ≤ n i) := by
  let N : ℕ := ⌈400 * B ^ 2⌉₊
  have hB0 : 0 < B := by linarith
  have hBsq : 1 ≤ B ^ 2 := by nlinarith
  have hNlo : 400 * B ^ 2 ≤ (N : ℝ) := Nat.le_ceil _
  have hNhi : (N : ℝ) ≤ 401 * B ^ 2 := by
    have h := Nat.ceil_lt_add_one (by positivity : 0 ≤ 400 * B ^ 2)
    dsimp [N]
    linarith
  have hN1 : (1 : ℝ) < N := by nlinarith
  have hN0 : 0 < (N : ℝ) := by linarith
  have hNnat : 1 ≤ N := by exact_mod_cast hN1.le
  have hLN : 0 < log (N : ℝ) := log_pos hN1
  have hR0 : 0 < R := (by positivity : 0 < 1000 * B ^ 3).trans_le hR
  let M := R / (2 * B)
  have hNM : (N : ℝ) ≤ M := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * B)).mpr
    have h := mul_le_mul_of_nonneg_right hNhi (by positivity : 0 ≤ 2 * B)
    nlinarith [pow_pos hB0 3]
  have hM0 : 0 < M := hN0.trans_le hNM
  let H := log M / log (N : ℝ)
  have hH1 : 1 ≤ H := by
    apply (le_div_iff₀ hLN).mpr
    simpa using log_le_log hN0 hNM
  let m : ℕ := ⌊H⌋₊
  have hm1 : 1 ≤ m := Nat.floor_pos.mpr hH1
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hmle : (m : ℝ) ≤ H := Nat.floor_le (by linarith)
  have hHle : H ≤ 2 * (m : ℝ) := by
    have h := Nat.lt_floor_add_one H
    dsimp [m]
    linarith
  have hNm : (N : ℝ) ^ m ≤ M := by
    apply (log_le_log_iff (pow_pos hN0 _) hM0).mp
    rw [log_pow]
    exact (le_div_iff₀ hLN).mp hmle
  have hRsq : (2 * B) ^ 2 ≤ R := by
    nlinarith [mul_nonneg (show 0 ≤ 1000 * B - 4 by linarith) (sq_nonneg B)]
  have hLM : log R / 2 ≤ log M := by
    have h := log_le_log (by positivity : 0 < (2 * B) ^ 2) hRsq
    rw [log_pow] at h
    dsimp [M]
    rw [log_div hR0.ne' (by positivity : 2 * B ≠ 0)]
    norm_num at h
    linarith
  have hLNhi : log (N : ℝ) ≤ 401 * B ^ 2 :=
    (log_le_sub_one_of_pos hN0).trans (by linarith)
  have hcount : log R / (2000 * B ^ 2) ≤ (m : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2000 * B ^ 2)).mpr
    have h1 := (div_le_iff₀ hLN).mp hHle
    have h2 := mul_le_mul_of_nonneg_left hLNhi (by positivity : 0 ≤ 2 * (m : ℝ))
    nlinarith [mul_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m) (sq_nonneg B)]
  let n (i : Fin m) := N ^ (i.val + 1)
  have hnlo (i : Fin m) : (N : ℝ) ≤ n i := by
    dsimp [n]
    rw [Nat.cast_pow]
    exact (pow_one (N : ℝ)).symm.trans_le
      (pow_le_pow_right₀ hN1.le (by omega))
  have hnupper (i : Fin m) : 2 * B * n i ≤ R := by
    have hpow : (n i : ℝ) ≤ (N : ℝ) ^ m := by
      dsimp [n]
      rw [Nat.cast_pow]
      exact pow_le_pow_right₀ hN1.le i.isLt
    have h := (le_div_iff₀ (by positivity : 0 < 2 * B)).mp (hpow.trans hNm)
    nlinarith
  have hsep {i j : Fin m} (hij : i < j) : 400 * B ^ 2 * (n i : ℝ) ≤ n j := by
    have hgap : i.val + 1 + 1 ≤ j.val + 1 := by exact_mod_cast Nat.succ_le_succ hij
    calc
      _ ≤ (N : ℝ) * (N : ℝ) ^ (i.val + 1) := by
        dsimp [n]
        rw [Nat.cast_pow]
        exact mul_le_mul_of_nonneg_right hNlo (by positivity)
      _ = (N : ℝ) ^ (i.val + 1 + 1) := by ring
      _ ≤ _ := by
        dsimp [n]
        rw [Nat.cast_pow]
        exact pow_le_pow_right₀ hN1.le hgap
  refine ⟨m, n, hcount, ?_, hnupper, ?_⟩
  · intro i
    exact (by nlinarith : 100 * B ^ 2 ≤ (N : ℝ)).trans (hnlo i)
  · intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact Or.inl (hsep h)
    · exact Or.inr (hsep h)

end LpSelfSimilar
