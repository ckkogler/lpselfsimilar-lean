module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic

@[expose] public section

/-!
Ceiling arithmetic for placing digit blocks at a target logarithmic scale.
A grid in source logarithmic scale becomes disjoint digit intervals, and each
used digit lies in an explicitly controlled scale window.
-/

open Real Set

namespace LpSelfSimilar.Bernoulli

/-- The starting digit that moves source scale exp(-v) just below exp(-T). -/
noncomputable def blockStart (χ T v : ℝ) : ℕ := ⌈(T - v) / χ⌉₊

lemma blockStart_bounds {χ T v : ℝ} (hχ : 0 < χ) (hv : v ≤ T) :
    T - v ≤ χ * (blockStart χ T v : ℝ) ∧
      χ * (blockStart χ T v : ℝ) < T - v + χ := by
  have h0 : 0 ≤ (T - v) / χ := div_nonneg (sub_nonneg.mpr hv) hχ.le
  have hlo := Nat.le_ceil ((T - v) / χ)
  have hhi := Nat.ceil_lt_add_one h0
  constructor
  · have h := (div_le_iff₀ hχ).mp hlo
    dsimp [blockStart]
    nlinarith
  · have h := mul_lt_mul_of_pos_left hhi hχ
    dsimp [blockStart]
    field_simp at h
    nlinarith

lemma blockStart_scaled_mesh {χ T v : ℝ} (hχ : 0 < χ) (hv : v ≤ T) :
    exp (-χ) * exp (-T) ≤ exp (-χ * blockStart χ T v) * exp (-v) ∧
      exp (-χ * blockStart χ T v) * exp (-v) ≤ exp (-T) := by
  have hb := blockStart_bounds hχ hv
  simp only [← exp_add]
  constructor <;> apply exp_le_exp.mpr <;> nlinarith [hb.1, hb.2]

/-- Every digit in a block lies in the source-scale window enlarged by nχ. -/
lemma blockStart_digit_window {χ T v : ℝ} (hχ : 0 < χ) (hv : v ≤ T)
    {n j : ℕ} (hj : j ∈ Finset.Ico (blockStart χ T v) (blockStart χ T v + n)) :
    v - (n : ℝ) * χ < T - (j : ℝ) * χ ∧ T - (j : ℝ) * χ ≤ v := by
  have hb := blockStart_bounds hχ hv
  have hmem := Finset.mem_Ico.mp hj
  have hlo : (blockStart χ T v : ℝ) ≤ j := Nat.cast_le.mpr hmem.1
  have hhi : (j : ℝ) + 1 ≤ (blockStart χ T v : ℝ) + n := by
    exact_mod_cast hmem.2
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hhi hχ.le, hb.2]
  · nlinarith [mul_le_mul_of_nonneg_right hlo hχ.le, hb.1]

/-- Adjacent source grid indices leave at least one whole block between starts. -/
lemma blockStart_grid_gap {χ T t : ℝ} (hχ : 0 < χ) (n : ℕ) {i j : ℕ}
    (hij : i < j) (hv : (n : ℝ) * χ * ((j : ℝ) + t) ≤ T) :
    blockStart χ T ((n : ℝ) * χ * ((j : ℝ) + t)) + n ≤
      blockStart χ T ((n : ℝ) * χ * ((i : ℝ) + t)) := by
  have h0 : 0 ≤ (T - (n : ℝ) * χ * ((j : ℝ) + t)) / χ := by positivity
  have he : (T - (n : ℝ) * χ * ((i : ℝ) + t)) / χ =
      (T - (n : ℝ) * χ * ((j : ℝ) + t)) / χ + ((n * (j - i) : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_sub hij.le]
    field_simp
    ring
  unfold blockStart
  rw [he, Nat.ceil_add_natCast h0]
  have hgap : 1 ≤ j - i := by omega
  have hn : n ≤ n * (j - i) := by nlinarith
  omega

lemma blockStart_grid_disjoint {χ T t : ℝ} (hχ : 0 < χ) (n : ℕ) {i j : ℕ}
    (hij : i < j) (hv : (n : ℝ) * χ * ((j : ℝ) + t) ≤ T) :
    Disjoint
      (Finset.Ico (blockStart χ T ((n : ℝ) * χ * ((i : ℝ) + t)))
        (blockStart χ T ((n : ℝ) * χ * ((i : ℝ) + t)) + n))
      (Finset.Ico (blockStart χ T ((n : ℝ) * χ * ((j : ℝ) + t)))
        (blockStart χ T ((n : ℝ) * χ * ((j : ℝ) + t)) + n)) := by
  have hgap := blockStart_grid_gap hχ n hij hv
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hx' := Finset.mem_Ico.mp hx
  have hy' := Finset.mem_Ico.mp hy
  omega

end LpSelfSimilar.Bernoulli
