module

public import LpSelfSimilar.Algebraic.ContractingRootSet
public import LpSelfSimilar.Geometry.ConjugatePairs

@[expose] public section

/-!
# Canonical real contracting roots and nonreal pairs

The real and upper-half-plane subsets of the canonical contracting root set
index the real spectral blocks. Their moduli reproduce the inverse Mahler
measure exactly: real roots contribute absolute real values and conjugate
pairs contribute squared complex moduli.
-/

open Polynomial
open scoped ComplexConjugate

namespace LpSelfSimilar.Algebraic

noncomputable def realContractingRoots (x : ℝ) : Finset ℂ :=
  (contractingRootSet x).filter (fun z => z.im = 0)

noncomputable def upperContractingRoots (x : ℝ) : Finset ℂ :=
  (contractingRootSet x).filter (fun z => 0 < z.im)

@[simp] theorem mem_realContractingRoots {x : ℝ} {z : ℂ} :
    z ∈ realContractingRoots x ↔ z ∈ contractingConjugates x ∧ z.im = 0 := by
  classical
  simp only [realContractingRoots, Finset.mem_filter, mem_contractingRootSet]

@[simp] theorem mem_upperContractingRoots {x : ℝ} {z : ℂ} :
    z ∈ upperContractingRoots x ↔ z ∈ contractingConjugates x ∧ 0 < z.im := by
  classical
  simp only [upperContractingRoots, Finset.mem_filter, mem_contractingRootSet]

theorem realContractingRoot_ofReal_re (x : ℝ) (z : realContractingRoots x) :
    (z.val.re : ℂ) = z.val := by
  apply Complex.ext
  · rfl
  · exact (mem_realContractingRoots.mp z.property).2.symm

theorem realContractingRoot_norm (x : ℝ) (z : realContractingRoots x) :
    ‖z.val‖ = |z.val.re| := by
  calc
    ‖z.val‖ = ‖(z.val.re : ℂ)‖ := congrArg norm (realContractingRoot_ofReal_re x z).symm
    _ = |z.val.re| := by rw [Complex.norm_real, Real.norm_eq_abs]

theorem realContractingRoot_re_ne_zero {x : ℝ} (hx : IsAlgebraic ℚ x) (hx0 : x ≠ 0)
    (z : realContractingRoots x) : z.val.re ≠ 0 := by
  intro hz
  have hn := contractingConjugate_ne_zero hx hx0 (mem_realContractingRoots.mp z.property).1
  apply hn
  rw [← realContractingRoot_ofReal_re x z, hz, Complex.ofReal_zero]

theorem upperContractingRoot_ne_zero {x : ℝ} (z : upperContractingRoots x) : z.val ≠ 0 := by
  intro hz
  have hi := (mem_upperContractingRoots.mp z.property).2
  rw [hz, Complex.zero_im] at hi
  exact lt_irrefl _ hi

/-- The real subset is nonempty because it contains the original real parameter. -/
theorem realContractingRoots_nonempty {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1) : (realContractingRoots x).Nonempty := by
  refine ⟨(x : ℂ), mem_realContractingRoots.mpr ?_⟩
  exact ⟨self_mem_contractingConjugates hx hx0 hx1, rfl⟩

/-- Exact determinant modulus of the real blocks, counted once per conjugate pair. -/
theorem prod_real_upper_contracting_norms {x : ℝ} (hx : IsAlgebraicUnit x) :
    (∏ z : realContractingRoots x, |z.val.re|) *
      (∏ z : upperContractingRoots x, ‖z.val‖ ^ 2) = (mahlerMeasure x)⁻¹ := by
  classical
  have h := Geometry.prod_conjugate_pairs (contractingRootSet x)
    (fun z => conj_mem_contractingRootSet_iff) (fun z => ‖z‖)
  simp only [Complex.norm_conj, ← pow_two] at h
  have hr : (∏ z : realContractingRoots x, |z.val.re|) =
      ∏ z ∈ realContractingRoots x, ‖z‖ := by
    calc
      _ = ∏ z : realContractingRoots x, ‖z.val‖ :=
        Finset.prod_congr rfl (fun z _ => (realContractingRoot_norm x z).symm)
      _ = _ := Finset.prod_coe_sort (realContractingRoots x) (fun z : ℂ => ‖z‖)
  have hu := Finset.prod_coe_sort (upperContractingRoots x) (fun z : ℂ => ‖z‖ ^ 2)
  rw [hr, hu]
  exact h.symm.trans (prod_contractingRootSet_norms hx)

end LpSelfSimilar.Algebraic
