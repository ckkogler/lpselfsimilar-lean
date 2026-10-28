module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

/-!
The explicit Young exponents for n out of k factors. The recurrence ends at
L^k after k-1 factors, conjugate to the last input space L^(k/(k-1)).
-/

namespace LpSelfSimilar

noncomputable def convolutionExponent (k n : ℕ) : ℝ := (k : ℝ) / ((k : ℝ) - n)

lemma convolutionExponent_pos {k n : ℕ} (hn : n < k) : 0 < convolutionExponent k n := by
  have h : (n : ℝ) < k := by exact_mod_cast hn
  unfold convolutionExponent
  exact div_pos (by linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]) (by linarith)

lemma one_le_convolutionExponent {k n : ℕ} (hn : n < k) : 1 ≤ convolutionExponent k n := by
  have h : (n : ℝ) < k := by exact_mod_cast hn
  unfold convolutionExponent
  exact (le_div_iff₀ (by linarith)).mpr (by simp)

lemma convolutionExponent_mono {k m n : ℕ} (hmn : m ≤ n) (hn : n < k) :
    convolutionExponent k m ≤ convolutionExponent k n := by
  have h : (n : ℝ) < k := by exact_mod_cast hn
  unfold convolutionExponent
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg k) (by linarith)
    (by
      have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
      linarith)

lemma convolutionExponent_young {k n : ℕ} (hn : 1 ≤ n) (hnk : n + 1 < k) :
    1 / convolutionExponent k n + 1 / convolutionExponent k 1 =
      1 + 1 / convolutionExponent k (n + 1) := by
  have hk : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  unfold convolutionExponent
  simp only [one_div_div, Nat.cast_add, Nat.cast_one]
  field_simp
  <;> ring

lemma convolutionExponent_pred {k : ℕ} (hk : 1 ≤ k) : convolutionExponent k (k - 1) = k := by
  unfold convolutionExponent
  rw [Nat.cast_sub hk, Nat.cast_one]
  simp

lemma convolutionExponent_conjugate {k : ℕ} (hk : 2 ≤ k) :
    1 / (k : ℝ) + 1 / convolutionExponent k 1 = 1 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  unfold convolutionExponent
  simp only [one_div_div, Nat.cast_one]
  field_simp
  <;> ring

end LpSelfSimilar
