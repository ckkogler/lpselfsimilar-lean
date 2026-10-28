module

public import LpSelfSimilar.Entropy.GraphMonotonicity

@[expose] public section

/-!
# Graph entropy bounded by an independent-cell label

A partition into independent sets gives a deterministic supported joint law.
Its joint entropy is the original point entropy, so the variational inequality
bounds graph entropy by the entropy of the partition label. Applying near/far
duality yields the quantization lower bound for near-graph entropy.
-/

open scoped BigOperators

namespace LpSelfSimilar.Entropy

/-- The entropy of any independent-cell label bounds graph entropy from above. -/
theorem graphEntropy_le_independent_label_entropy {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ] (G : SimpleGraph ι) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (label : ι → κ)
    (hindep : ∀ i j, i ≠ j → label i = label j → ¬ G.Adj i j) :
    graphEntropy G p ≤ ∑ k, Real.negMulLog (∑ i, if label i = k then p i else 0) := by
  classical
  let cover : κ → Finset ι := fun k ↦ Finset.univ.filter (fun i ↦ label i = k)
  let u : ι → κ → ℝ := fun i k ↦ if label i = k then p i else 0
  have hu : u ∈ supportedJointSpace p cover := by
    refine ⟨?_, ?_, ?_⟩
    · intro i k
      dsimp [u]
      split_ifs
      · exact hp i
      · exact le_rfl
    · intro i
      simp [u]
    · intro i k hi
      have hne : label i ≠ k := by simpa [cover] using hi
      simp [u, hne]
  have hcover : ∀ k, G.IsIndepSet (cover k : Set ι) := by
    intro k i hi j hj hij
    have hi' : label i = k := (Finset.mem_filter.mp hi).2
    have hj' : label j = k := (Finset.mem_filter.mp hj).2
    exact hindep i j hij (hi'.trans hj'.symm)
  have h := jointConditionalEntropy_le_entropy_sub_graphEntropy G p cover hcover hu hsum
  have he : (∑ i, ∑ k, Real.negMulLog (u i k)) = ∑ i, Real.negMulLog (p i) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [u, apply_ite Real.negMulLog]
  unfold jointConditionalEntropy at h
  rw [he] at h
  dsimp [u] at h
  linarith

/-- A cell partition of diameter strictly below `a` supplies the near-entropy lower bound. -/
theorem near_graphEntropyBits_ge_entropy_sub_label {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ] (z : ι → ℝ) (a : ℝ) (ha : 0 < a)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (label : ι → κ)
    (hdiam : ∀ i j, label i = label j → |z i - z j| < a) :
    (∑ i, Real.negMulLog (p i)) / Real.log 2 -
      (∑ k, Real.negMulLog (∑ i, if label i = k then p i else 0)) / Real.log 2 ≤
      graphEntropyBits (nearDistanceGraph z a) p := by
  classical
  have hb := graphEntropy_le_independent_label_entropy (nearDistanceGraph z a)ᶜ p hp hsum
    label (fun i j hij he hAdj ↦ hAdj.2 ⟨hij, hdiam i j he⟩)
  have hbits : graphEntropyBits (nearDistanceGraph z a)ᶜ p ≤
      (∑ k, Real.negMulLog (∑ i, if label i = k then p i else 0)) / Real.log 2 :=
    div_le_div_of_nonneg_right hb (Real.log_nonneg (by norm_num))
  have hd := graphEntropyBits_near_add_compl z a ha p hp hsum
  linarith

end LpSelfSimilar.Entropy
