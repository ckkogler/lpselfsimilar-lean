module

public import Mathlib.Analysis.Polynomial.CauchyBound
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
A complex root of a nonzero integer polynomial with coefficients in {-1,0,1}
has modulus strictly less than two. Cauchy's root bound proves this uniformly in
the degree. It supplies an elementary digit-injectivity criterion at a sufficiently
expanding conjugate, with no entropy or Gaussian input.
-/

open Polynomial

namespace LpSelfSimilar

theorem norm_lt_two_of_height_one_root {p : ℤ[X]} (hp : p ≠ 0)
    (hcoeff : ∀ i, |p.coeff i| ≤ 1) {z : ℂ} (hz : aeval z p = 0) : ‖z‖ < 2 := by
  let P := p.map (Int.castRingHom ℂ)
  have hP : P ≠ 0 := (Polynomial.map_ne_zero_iff (Int.castRingHom ℂ).injective_int).mpr hp
  have hl : |p.leadingCoeff| = 1 := by
    have hn := leadingCoeff_ne_zero.mpr hp
    have hb := hcoeff p.natDegree
    change |p.leadingCoeff| ≤ 1 at hb
    have ha := abs_pos.mpr hn
    omega
  have hnorm (i : ℕ) : ‖P.coeff i‖₊ ≤ 1 := by
    have h : ‖P.coeff i‖ ≤ (1 : ℝ) := by
      simp only [P, coeff_map, Int.coe_castRingHom, Complex.norm_intCast]
      exact_mod_cast hcoeff i
    exact_mod_cast h
  have hlead : ‖P.leadingCoeff‖₊ = 1 := by
    have h : ‖P.leadingCoeff‖ = (1 : ℝ) := by
      change ‖(p.map (Int.castRingHom ℂ)).leadingCoeff‖ = (1 : ℝ)
      rw [leadingCoeff_map_of_injective (Int.castRingHom ℂ).injective_int]
      simp only [Int.coe_castRingHom, Complex.norm_intCast]
      exact_mod_cast hl
    exact NNReal.eq h
  have hbound : P.cauchyBound ≤ 2 := by
    rw [cauchyBound, hlead, div_one]
    have hsup : (Finset.range P.natDegree).sup (fun i ↦ ‖P.coeff i‖₊) ≤ 1 :=
      Finset.sup_le (fun i _ ↦ hnorm i)
    calc
      _ ≤ (1 : NNReal) + 1 := add_le_add hsup le_rfl
      _ = 2 := by norm_num
  have hroot : P.IsRoot z := by
    simpa only [P, IsRoot, eval_map, ← algebraMap_int_eq, ← aeval_def] using hz
  have h := hroot.norm_lt_cauchyBound hP |>.trans_le hbound
  exact_mod_cast h

end LpSelfSimilar
