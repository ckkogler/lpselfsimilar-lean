module

public import LpSelfSimilar.Entropy.CanonicalGraphCover
public import LpSelfSimilar.Entropy.GraphEntropy
public import LpSelfSimilar.Entropy.FiniteCoverNonnegative
public import LpSelfSimilar.Entropy.DistanceBandGraph

@[expose] public section

/-!
# Entropy lower bounds for the attained canonical conditional maximum

Represent a graph-entropy optimizer on the fixed independent-set label family.
Its coverage-normalized joint array belongs to the compact feasible space used
for the conditional maximum. The supported Gibbs inequality gives the lower
bound, and complementary near/far duality supplies the distance-band increment.
-/

open scoped BigOperators

namespace LpSelfSimilar.Entropy

/-- The attained conditional maximum retains at least entropy minus graph entropy. -/
theorem entropy_sub_graphEntropy_le_graphConditionalEntropy {ι : Type*} [Fintype ι]
    (G : SimpleGraph ι) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (∑ i, Real.negMulLog (p i)) - graphEntropy G p ≤ graphConditionalEntropy G p := by
  classical
  obtain ⟨x, hx, hx0, hxe, _⟩ := exists_graphEntropy_minimizer G p hp
  obtain ⟨W, hW, hWsum, hcov⟩ := exists_canonical_cover_of_mem_independentSetPolytope G hx
  let cover := graphIndependentCover G
  let u : ι → Finset ι → ℝ := finiteCoverJoint Finset.univ p W cover
  have hc : ∀ i ∈ Finset.univ, p i ≠ 0 → 0 < finiteCoverWeight Finset.univ W cover i := by
    intro i _ hi
    change 0 < finiteCoverWeight Finset.univ W (graphIndependentCover G) i
    rw [hcov]
    exact hx0 i hi
  have hu : u ∈ supportedJointSpace p (graphIndependentCover G) := by
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      exact finiteCoverJoint_nonneg Finset.univ p W cover (hp i) (fun j _ ↦ hW j)
        (Finset.mem_univ j)
    · intro i
      exact sum_finiteCoverJoint_eq Finset.univ p W cover i (hc i (Finset.mem_univ i))
    · intro i j hi
      exact finiteCoverJoint_eq_zero_of_not_mem Finset.univ p W cover hi
  have h := finiteCover_joint_sub_label_entropy_ge_of_nonneg Finset.univ Finset.univ p W cover
    (fun i _ ↦ hp i) hsum (fun j _ ↦ hW j) hWsum.le hc
  have hlog : (∑ i, p i * Real.log (finiteCoverWeight Finset.univ W cover i)) =
      -graphEntropy G p := by
    change (∑ i, p i * Real.log (finiteCoverWeight Finset.univ W (graphIndependentCover G) i)) = _
    rw [hcov, ← hxe]
    simp [graphCoverageCost, mul_neg]
  rw [hlog] at h
  change (∑ i, Real.negMulLog (p i)) - graphEntropy G p ≤ jointConditionalEntropy u at h
  exact h.trans (jointConditionalEntropy_le_graphConditionalEntropy G p hp hu)

/-- Exact single-scale band increment for the attained canonical conditional maximum. -/
theorem near_difference_le_band_graphConditionalEntropy {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (a : ℝ) (ha : 0 < a) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    graphEntropy (nearDistanceGraph z (16 * a)) p - graphEntropy (nearDistanceGraph z a) p ≤
      graphConditionalEntropy (distanceBandGraph z a (16 * a))ᶜ p :=
  (entropy_sub_band_compl_ge_near_difference z a (16 * a) (by positivity) p hp hsum).trans
    (entropy_sub_graphEntropy_le_graphConditionalEntropy _ p hp hsum)

end LpSelfSimilar.Entropy
