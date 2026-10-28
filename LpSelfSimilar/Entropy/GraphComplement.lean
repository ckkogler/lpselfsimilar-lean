module

public import LpSelfSimilar.Entropy.GraphEntropy
public import LpSelfSimilar.Entropy.FiniteCoverInformation

@[expose] public section

/-!
# Complementary graph coverage inequalities

An independent set of a graph and an independent set of its complement meet in
at most one vertex. Extending this elementary bound twice by convexity gives
the scalar-product bound for arbitrary coverage vectors. Gibbs' inequality then
gives the entropy lower bound, with null probabilities removed only from the
finite sum and not by imposing a strict-positivity hypothesis on the input law.
-/

open Set
open scoped BigOperators

namespace LpSelfSimilar.Entropy

/-- A linear bound on independent-set indicators holds on their entire polytope. -/
theorem independentSetPolytope_sum_le {ι : Type*} [Fintype ι]
    (G : SimpleGraph ι) (w : ι → ℝ) (c : ℝ)
    (hs : ∀ s : Finset ι, G.IsIndepSet (s : Set ι) → (∑ i ∈ s, w i) ≤ c)
    {x : ι → ℝ} (hx : x ∈ independentSetPolytope G) :
    (∑ i, w i * x i) ≤ c := by
  classical
  have hlin : IsLinearMap ℝ (fun x : ι → ℝ ↦ ∑ i, w i * x i) := by
    constructor
    · intro x y
      simp [mul_add, Finset.sum_add_distrib]
    · intro a x
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
  apply convexHull_min (t := {x : ι → ℝ | (∑ i, w i * x i) ≤ c}) ?_
    (convex_halfSpace_le hlin c) hx
  rintro _ ⟨s, rfl⟩
  change (∑ i, w i * vertexSetIndicator s.val i) ≤ c
  simpa [vertexSetIndicator, mul_ite] using hs s.val s.property

/-- Complementary independent-set coverages have scalar product at most one. -/
theorem independentSetPolytope_compl_dot_le_one {ι : Type*} [Fintype ι]
    (G : SimpleGraph ι) {x y : ι → ℝ}
    (hx : x ∈ independentSetPolytope G) (hy : y ∈ independentSetPolytope Gᶜ) :
    (∑ i, x i * y i) ≤ 1 := by
  classical
  have hsets (s t : Finset ι) (hs : G.IsIndepSet (s : Set ι))
      (ht : Gᶜ.IsIndepSet (t : Set ι)) : (∑ i ∈ t, vertexSetIndicator s i) ≤ 1 := by
    have hc : (t.filter (fun i ↦ i ∈ s)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      obtain ⟨hit, his⟩ := Finset.mem_filter.mp hi
      obtain ⟨hjt, hjs⟩ := Finset.mem_filter.mp hj
      by_contra hij
      have htcl : G.IsClique (t : Set ι) := by simpa using ht
      exact hs his hjs hij (htcl hit hjt hij)
    have he : t.filter (fun i ↦ i ∈ s) = t ∩ s := by ext i; simp
    rw [he] at hc
    simpa [vertexSetIndicator] using (show ((t ∩ s).card : ℝ) ≤ 1 by exact_mod_cast hc)
  have hs (s : Finset ι) (hsi : G.IsIndepSet (s : Set ι)) : (∑ i ∈ s, y i) ≤ 1 := by
    have h := independentSetPolytope_sum_le Gᶜ (vertexSetIndicator s) 1
      (fun t ht ↦ hsets s t hsi ht) hy
    simpa [vertexSetIndicator, ite_mul] using h
  simpa [mul_comm] using independentSetPolytope_sum_le G y 1 hs hx

/-- Complementary coverage costs bound entropy even when probabilities vanish. -/
theorem finite_entropy_le_coverage_cost_add_on_support {ι : Type*} [Fintype ι]
    (p x y : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (hx0 : ∀ i, p i ≠ 0 → 0 < x i) (hy0 : ∀ i, p i ≠ 0 → 0 < y i)
    (hxy : ∑ i, x i * y i ≤ 1) :
    (∑ i, Real.negMulLog (p i)) ≤ graphCoverageCost p x + graphCoverageCost p y := by
  classical
  let s := Finset.univ.filter (fun i ↦ p i ≠ 0)
  have hrestrict (f : ι → ℝ) (hf : ∀ i, p i = 0 → f i = 0) :
      (∑ i ∈ s, f i) = ∑ i, f i := by
    simp only [s, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hpi : p i = 0
    · simp [hpi, hf i hpi]
    · simp [hpi]
  have hps : ∑ i ∈ s, p i = 1 := (hrestrict p (fun i hi ↦ hi)).trans hsum
  have hbound : (∑ i ∈ s, x i * y i) ≤ 1 := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ ↦ mul_nonneg (hx i) (hy i))) hxy
  have h := finite_entropy_le_coverage_cost_add s p x y (fun i _ ↦ hp i) hps
    (fun i hi ↦ hx0 i (Finset.mem_filter.mp hi).2)
    (fun i hi ↦ hy0 i (Finset.mem_filter.mp hi).2) hbound
  rw [hrestrict (fun i ↦ Real.negMulLog (p i)) (by intros; simp_all),
      hrestrict (fun i ↦ p i * (-Real.log (x i))) (by intros; simp_all),
      hrestrict (fun i ↦ p i * (-Real.log (y i))) (by intros; simp_all)] at h
  exact h

/-- For every graph, its entropy plus the complement's entropy bounds the law's entropy. -/
theorem entropy_le_graphEntropy_add_compl {ι : Type*} [Fintype ι]
    (G : SimpleGraph ι) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (∑ i, Real.negMulLog (p i)) ≤ graphEntropy G p + graphEntropy Gᶜ p := by
  obtain ⟨x, hx, hx0, hxe, _⟩ := exists_graphEntropy_minimizer G p hp
  obtain ⟨y, hy, hy0, hye, _⟩ := exists_graphEntropy_minimizer Gᶜ p hp
  rw [← hxe, ← hye]
  exact finite_entropy_le_coverage_cost_add_on_support p x y hp hsum
    (fun i ↦ (independentSetPolytope_coordinate_bounds G hx i).1)
    (fun i ↦ (independentSetPolytope_coordinate_bounds Gᶜ hy i).1) hx0 hy0
    (independentSetPolytope_compl_dot_le_one G hx hy)

end LpSelfSimilar.Entropy
