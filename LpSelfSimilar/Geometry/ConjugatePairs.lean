module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Real roots and upper-half-plane conjugate pairs

Every finite conjugation-invariant complex set splits into its real points and
pairs indexed by its upper-half-plane points. Exact sum and product formulas
retain each nonreal point once, without imposing an ordering on the set.
-/

open scoped ComplexConjugate

namespace LpSelfSimilar.Geometry

/-- The imaginary-part trichotomy partitions any finite complex set. -/
theorem complex_finset_split (S : Finset ℂ) :
    S = S.filter (fun z => z.im = 0) ∪
      (S.filter (fun z => 0 < z.im) ∪ S.filter (fun z => z.im < 0)) := by
  classical
  ext z
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · intro hz
    rcases lt_trichotomy (0 : ℝ) z.im with h | h | h
    · exact Or.inr (Or.inl ⟨hz, h⟩)
    · exact Or.inl ⟨hz, h.symm⟩
    · exact Or.inr (Or.inr ⟨hz, h⟩)
  · rintro (h | h | h) <;> exact h.1

/-- Conjugation bijects the upper and lower halves of a conjugation-invariant set. -/
theorem negative_filter_eq_conj_image (S : Finset ℂ)
    (hS : ∀ z : ℂ, conj z ∈ S ↔ z ∈ S) :
    S.filter (fun z => z.im < 0) =
      (S.filter (fun z => 0 < z.im)).image conj := by
  classical
  ext z
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hz, hi⟩
    exact ⟨conj z, ⟨(hS z).mpr hz, by simpa only [Complex.conj_im] using neg_pos.mpr hi⟩,
      Complex.conj_conj z⟩
  · rintro ⟨w, ⟨hw, hi⟩, rfl⟩
    exact ⟨(hS w).mpr hw, by simpa only [Complex.conj_im] using neg_neg_of_pos hi⟩

theorem complex_finset_split_disjoint (S : Finset ℂ) :
    Disjoint (S.filter (fun z => z.im = 0))
      (S.filter (fun z => 0 < z.im) ∪ S.filter (fun z => z.im < 0)) ∧
    Disjoint (S.filter (fun z => 0 < z.im)) (S.filter (fun z => z.im < 0)) := by
  classical
  constructor
  · apply Finset.disjoint_left.mpr
    intro z hz hw
    have hz0 := (Finset.mem_filter.mp hz).2
    rcases Finset.mem_union.mp hw with h | h
    · have := (Finset.mem_filter.mp h).2; linarith
    · have := (Finset.mem_filter.mp h).2; linarith
  · apply Finset.disjoint_left.mpr
    intro z hz hw
    have := (Finset.mem_filter.mp hz).2
    have := (Finset.mem_filter.mp hw).2
    linarith

/-- Every nonreal conjugate pair contributes exactly two factors. -/
theorem prod_conjugate_pairs {M : Type*} [CommMonoid M] (S : Finset ℂ)
    (hS : ∀ z : ℂ, conj z ∈ S ↔ z ∈ S) (f : ℂ → M) :
    ∏ z ∈ S, f z = (∏ z ∈ S.filter (fun z => z.im = 0), f z) *
      ∏ z ∈ S.filter (fun z => 0 < z.im), f z * f (conj z) := by
  classical
  obtain ⟨hd0, hd1⟩ := complex_finset_split_disjoint S
  calc
    _ = ∏ z ∈ S.filter (fun z => z.im = 0) ∪
        (S.filter (fun z => 0 < z.im) ∪ S.filter (fun z => z.im < 0)), f z :=
      congrArg (fun T : Finset ℂ => ∏ z ∈ T, f z) (complex_finset_split S)
    _ = (∏ z ∈ S.filter (fun z => z.im = 0), f z) *
        ((∏ z ∈ S.filter (fun z => 0 < z.im), f z) *
          ∏ z ∈ S.filter (fun z => z.im < 0), f z) := by
      rw [Finset.prod_union hd0, Finset.prod_union hd1]
    _ = _ := by
      rw [negative_filter_eq_conj_image S hS, Finset.prod_image]
      · rw [Finset.prod_mul_distrib]
      · intro z hz w hw h
        exact Complex.conjAe.injective h

/-- Additive version of the exact conjugate-pair decomposition. -/
theorem sum_conjugate_pairs {M : Type*} [AddCommMonoid M] (S : Finset ℂ)
    (hS : ∀ z : ℂ, conj z ∈ S ↔ z ∈ S) (f : ℂ → M) :
    ∑ z ∈ S, f z = (∑ z ∈ S.filter (fun z => z.im = 0), f z) +
      ∑ z ∈ S.filter (fun z => 0 < z.im), (f z + f (conj z)) := by
  classical
  obtain ⟨hd0, hd1⟩ := complex_finset_split_disjoint S
  calc
    _ = ∑ z ∈ S.filter (fun z => z.im = 0) ∪
        (S.filter (fun z => 0 < z.im) ∪ S.filter (fun z => z.im < 0)), f z :=
      congrArg (fun T : Finset ℂ => ∑ z ∈ T, f z) (complex_finset_split S)
    _ = (∑ z ∈ S.filter (fun z => z.im = 0), f z) +
        ((∑ z ∈ S.filter (fun z => 0 < z.im), f z) +
          ∑ z ∈ S.filter (fun z => z.im < 0), f z) := by
      rw [Finset.sum_union hd0, Finset.sum_union hd1]
    _ = _ := by
      rw [negative_filter_eq_conj_image S hS, Finset.sum_image]
      · rw [Finset.sum_add_distrib]
      · intro z hz w hw h
        exact Complex.conjAe.injective h

end LpSelfSimilar.Geometry
