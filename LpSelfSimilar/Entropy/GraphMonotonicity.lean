module

public import LpSelfSimilar.Entropy.GraphEntropyBits

@[expose] public section

/-!
# Graph-entropy comparison and decreasing dyadic scales

Adding edges removes independent sets, so it can only increase graph entropy.
The edgeless graph has the constant-one coverage and hence zero entropy. These
facts make near-graph entropy decrease as the dyadic scale exponent increases.
-/

open Set

namespace LpSelfSimilar.Entropy

/-- Adding edges shrinks the independent-set polytope. -/
theorem independentSetPolytope_antitone {ι : Type*} {G H : SimpleGraph ι} (hGH : G ≤ H) :
    independentSetPolytope H ⊆ independentSetPolytope G := by
  apply convexHull_mono
  rintro _ ⟨s, rfl⟩
  refine ⟨⟨s.val, ?_⟩, rfl⟩
  intro i hi j hj hij hAdj
  exact s.property hi hj hij (hGH hAdj)

/-- Any feasible supported coverage bounds the attained graph-entropy minimum. -/
theorem graphEntropy_le_coverageCost {ι : Type*} [Fintype ι]
    (G : SimpleGraph ι) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    {x : ι → ℝ} (hx : x ∈ independentSetPolytope G) (hx0 : ∀ i, p i ≠ 0 → 0 < x i) :
    graphEntropy G p ≤ graphCoverageCost p x := by
  obtain ⟨y, hy, hy0, he, hmin⟩ := exists_graphEntropy_minimizer G p hp
  rw [← he]
  exact hmin x hx hx0

/-- Adding edges can only increase graph entropy. -/
theorem graphEntropy_mono {ι : Type*} [Fintype ι] {G H : SimpleGraph ι}
    (hGH : G ≤ H) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) : graphEntropy G p ≤ graphEntropy H p := by
  obtain ⟨x, hx, hx0, he, _⟩ := exists_graphEntropy_minimizer H p hp
  rw [← he]
  exact graphEntropy_le_coverageCost G p hp (independentSetPolytope_antitone hGH hx) hx0

/-- The edgeless graph has zero graph entropy. -/
theorem graphEntropy_bot {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) : graphEntropy (⊥ : SimpleGraph ι) p = 0 := by
  classical
  have hx : (fun _ : ι ↦ (1 : ℝ)) ∈ independentSetPolytope (⊥ : SimpleGraph ι) := by
    convert vertexSetIndicator_mem_polytope (⊥ : SimpleGraph ι) Finset.univ
      (by intro i hi j hj hij; simp) using 1
    ext i
    simp [vertexSetIndicator]
  apply le_antisymm ?_ (graphEntropy_nonneg ⊥ p hp)
  simpa [graphCoverageCost] using graphEntropy_le_coverageCost (⊥ : SimpleGraph ι) p hp hx
    (fun _ _ ↦ zero_lt_one)

/-- Increasing the distance threshold adds near-graph edges. -/
theorem nearDistanceGraph_mono_radius {ι : Type*} (z : ι → ℝ) {a b : ℝ} (hab : a ≤ b) :
    nearDistanceGraph z a ≤ nearDistanceGraph z b := by
  intro i j hij
  exact ⟨hij.1, hij.2.trans_le hab⟩

/-- Near-graph entropy in bits is decreasing in the dyadic scale exponent. -/
theorem antitone_dyadic_near_graphEntropyBits {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) :
    Antitone (fun j : ℝ ↦ graphEntropyBits (nearDistanceGraph z ((2 : ℝ) ^ (-j))) p) := by
  intro a b hab
  apply div_le_div_of_nonneg_right ?_ (Real.log_nonneg (by norm_num))
  apply graphEntropy_mono ?_ p hp
  apply nearDistanceGraph_mono_radius
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_neg hab)

end LpSelfSimilar.Entropy
