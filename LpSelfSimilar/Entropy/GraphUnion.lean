module

public import LpSelfSimilar.Entropy.GraphEntropy

@[expose] public section

/-!
# Entropy subadditivity for a union of finite graphs

Intersect an independent set from each graph. The intersection is independent
in their union, and independent sampling multiplies the vertex coverages. We
prove polytope membership by extending this indicator identity twice through
convex hulls. Logarithmic costs then add, proving entropy subadditivity without
strict positivity of the input probabilities.
-/

open Set
open scoped BigOperators

namespace LpSelfSimilar.Entropy

/-- Products of coverages are coverages for the union graph. -/
theorem independentSetPolytope_mul_mem_sup {ι : Type*} (G H : SimpleGraph ι)
    {x y : ι → ℝ} (hx : x ∈ independentSetPolytope G) (hy : y ∈ independentSetPolytope H) :
    (fun i ↦ x i * y i) ∈ independentSetPolytope (G ⊔ H) := by
  classical
  have hlin (w : ι → ℝ) : IsLinearMap ℝ (fun v : ι → ℝ ↦ fun i ↦ v i * w i) := by
    constructor
    · intro u v
      ext i
      simp [add_mul]
    · intro a v
      ext i
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  have hconv (w : ι → ℝ) : Convex ℝ
      ((fun v : ι → ℝ ↦ fun i ↦ v i * w i) ⁻¹' independentSetPolytope (G ⊔ H)) :=
    (convex_independentSetPolytope (G ⊔ H)).is_linear_preimage (hlin w)
  have hsub : independentSetPolytope G ⊆
      (fun v : ι → ℝ ↦ fun i ↦ v i * y i) ⁻¹' independentSetPolytope (G ⊔ H) := by
    apply convexHull_min ?_ (hconv y)
    rintro _ ⟨s, rfl⟩
    have hsubH : independentSetPolytope H ⊆
        (fun v : ι → ℝ ↦ fun i ↦ v i * vertexSetIndicator s.val i) ⁻¹'
          independentSetPolytope (G ⊔ H) := by
      apply convexHull_min ?_ (hconv (vertexSetIndicator s.val))
      rintro _ ⟨t, rfl⟩
      have hi : (G ⊔ H).IsIndepSet ((s.val ∩ t.val : Finset ι) : Set ι) := by
        intro i hi j hj hij hadj
        obtain ⟨his, hit⟩ := Finset.mem_inter.mp hi
        obtain ⟨hjs, hjt⟩ := Finset.mem_inter.mp hj
        rcases hadj with hadj | hadj
        · exact s.property his hjs hij hadj
        · exact t.property hit hjt hij hadj
      have he : (fun i ↦ vertexSetIndicator t.val i * vertexSetIndicator s.val i) =
          vertexSetIndicator (s.val ∩ t.val) := by
        ext i
        by_cases hs : i ∈ s.val <;> by_cases ht : i ∈ t.val <;>
          simp [vertexSetIndicator, hs, ht]
      change (fun i ↦ vertexSetIndicator t.val i * vertexSetIndicator s.val i) ∈
        independentSetPolytope (G ⊔ H)
      rw [he]
      exact vertexSetIndicator_mem_polytope (G ⊔ H) _ hi
    simpa [mul_comm] using hsubH hy
  exact hsub hx

/-- Products of positive-on-support coverages add logarithmic costs exactly. -/
theorem graphCoverageCost_mul_eq_add {ι : Type*} [Fintype ι] (p x y : ι → ℝ)
    (hx : ∀ i, p i ≠ 0 → 0 < x i) (hy : ∀ i, p i ≠ 0 → 0 < y i) :
    graphCoverageCost p (fun i ↦ x i * y i) = graphCoverageCost p x + graphCoverageCost p y := by
  unfold graphCoverageCost
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hpi : p i = 0
  · simp [hpi]
  · rw [Real.log_mul (hx i hpi).ne' (hy i hpi).ne']
    ring

/-- Entropy is subadditive under graph union, with no positive-mass restriction. -/
theorem graphEntropy_sup_le_add {ι : Type*} [Fintype ι]
    (G H : SimpleGraph ι) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) :
    graphEntropy (G ⊔ H) p ≤ graphEntropy G p + graphEntropy H p := by
  obtain ⟨x, hx, hx0, hxe, _⟩ := exists_graphEntropy_minimizer G p hp
  obtain ⟨y, hy, hy0, hye, _⟩ := exists_graphEntropy_minimizer H p hp
  obtain ⟨z, _, _, hze, hmin⟩ := exists_graphEntropy_minimizer (G ⊔ H) p hp
  have h := hmin (fun i ↦ x i * y i) (independentSetPolytope_mul_mem_sup G H hx hy)
    (fun i hi ↦ mul_pos (hx0 i hi) (hy0 i hi))
  rwa [hze, graphCoverageCost_mul_eq_add p x y hx0 hy0, hxe, hye] at h

end LpSelfSimilar.Entropy
