module

public import LpSelfSimilar.Entropy.FiniteJointEntropy
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-!
# Compact spaces of supported finite joint laws

Fix the point marginal and the allowed support of each label. The nonnegative
joint arrays with these constraints form a compact set: every entry is bounded
by its row marginal. The conditional entropy is the continuous difference of
joint and label entropies, including zero columns. Its maximum is therefore
attained whenever the allowed supports cover all points.
-/

open Set
open scoped BigOperators

namespace LpSelfSimilar.Entropy

/-- Nonnegative joint arrays with fixed point marginal and specified label supports. -/
def supportedJointSpace {ι κ : Type*} [Fintype κ]
    (p : ι → ℝ) (cover : κ → Finset ι) : Set (ι → κ → ℝ) :=
  {u | (∀ i j, 0 ≤ u i j) ∧ (∀ i, ∑ j, u i j = p i) ∧
    (∀ i j, i ∉ cover j → u i j = 0)}

/-- Conditional entropy as a continuous joint-minus-label expression. -/
noncomputable def jointConditionalEntropy {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u : ι → κ → ℝ) : ℝ :=
  (∑ i, ∑ j, Real.negMulLog (u i j)) - ∑ j, Real.negMulLog (∑ i, u i j)

theorem isClosed_supportedJointSpace {ι κ : Type*} [Fintype κ]
    (p : ι → ℝ) (cover : κ → Finset ι) : IsClosed (supportedJointSpace p cover) := by
  have hev (i : ι) (j : κ) : Continuous (fun u : ι → κ → ℝ ↦ u i j) :=
    (continuous_apply j).comp (continuous_apply i)
  have hnonneg : IsClosed {u : ι → κ → ℝ | ∀ i j, 0 ≤ u i j} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun i ↦ isClosed_iInter (fun j ↦ isClosed_le continuous_const (hev i j)))
  have hrow : IsClosed {u : ι → κ → ℝ | ∀ i, ∑ j, u i j = p i} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro i
    exact isClosed_eq (continuous_finsetSum _ (fun j _ ↦ hev i j)) continuous_const
  have hsupp : IsClosed {u : ι → κ → ℝ | ∀ i j, i ∉ cover j → u i j = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun i ↦ isClosed_iInter (fun j ↦
      isClosed_iInter (fun _ ↦ isClosed_eq (hev i j) continuous_const)))
  simpa only [supportedJointSpace, Set.ofPred_and] using hnonneg.inter (hrow.inter hsupp)

/-- Compactness comes from the entrywise bounds by the prescribed row mass. -/
theorem isCompact_supportedJointSpace {ι κ : Type*} [Fintype κ]
    (p : ι → ℝ) (cover : κ → Finset ι) : IsCompact (supportedJointSpace p cover) := by
  apply (isCompact_Icc : IsCompact (Icc (0 : ι → κ → ℝ) (fun i _ ↦ p i))).of_isClosed_subset
    (isClosed_supportedJointSpace p cover)
  intro u hu
  refine ⟨hu.1, ?_⟩
  intro i j
  calc
    u i j ≤ ∑ k, u i k := Finset.single_le_sum (fun k _ ↦ hu.1 i k) (Finset.mem_univ j)
    _ = p i := hu.2.1 i

/-- Assign each point's mass to one allowed label to construct a feasible joint law. -/
theorem supportedJointSpace_nonempty {ι κ : Type*} [Fintype κ]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (cover : κ → Finset ι)
    (hcover : ∀ i, ∃ j, i ∈ cover j) : (supportedJointSpace p cover).Nonempty := by
  classical
  choose label hlabel using hcover
  refine ⟨fun i j ↦ if j = label i then p i else 0, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    dsimp
    split_ifs
    · exact hp i
    · exact le_rfl
  · intro i
    simp
  · intro i j hj
    have hne : j ≠ label i := fun he ↦ hj (he ▸ hlabel i)
    simp [hne]

theorem continuous_jointConditionalEntropy {ι κ : Type*} [Fintype ι] [Fintype κ] :
    Continuous (jointConditionalEntropy : (ι → κ → ℝ) → ℝ) := by
  unfold jointConditionalEntropy
  fun_prop

/-- The greatest achievable conditional entropy is attained by an actual joint law. -/
theorem exists_jointConditionalEntropy_maximizer {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (cover : κ → Finset ι)
    (hcover : ∀ i, ∃ j, i ∈ cover j) :
    ∃ u ∈ supportedJointSpace p cover, ∀ v ∈ supportedJointSpace p cover,
      jointConditionalEntropy v ≤ jointConditionalEntropy u := by
  obtain ⟨u, hu, hmax⟩ := (isCompact_supportedJointSpace p cover).exists_isMaxOn
    (supportedJointSpace_nonempty p hp cover hcover) continuous_jointConditionalEntropy.continuousOn
  exact ⟨u, hu, fun v hv ↦ hmax hv⟩

/-- The continuous objective equals the expected entropy of the actual conditional vectors. -/
theorem jointConditionalEntropy_eq_expected_entropy {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u : ι → κ → ℝ) (hu : ∀ i j, 0 ≤ u i j) :
    jointConditionalEntropy u =
      ∑ j, (∑ i, u i j) * ∑ i, Real.negMulLog (u i j / ∑ k, u k j) := by
  symm
  exact finite_conditional_entropy_chain Finset.univ Finset.univ u (fun i _ j _ ↦ hu i j)

end LpSelfSimilar.Entropy
