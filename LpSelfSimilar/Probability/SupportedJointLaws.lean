module

public import LpSelfSimilar.Probability.RealProbabilityVector
public import LpSelfSimilar.Entropy.SupportedJointConditionals

@[expose] public section

/-!
# Actual conditional probability measures from finite joint arrays

Positive columns give their normalized real-vector law. Null columns are assigned
`dirac 0`, so every label has a probability measure; their zero label mass removes
this arbitrary fallback from all mixtures. Averaging with the original column
masses recovers the original atom law exactly.
-/

open MeasureTheory
open scoped BigOperators ENNReal
open LpSelfSimilar.Entropy

namespace LpSelfSimilar.FiniteProbability

/-- The conditional real probability law of a column, with `dirac 0` at a null column. -/
noncomputable def jointConditionalLaw {ι κ : Type*} [Fintype ι]
    (u : ι → κ → ℝ) (hu : ∀ i j, 0 ≤ u i j) (z : ι → ℝ) (j : κ) : Measure ℝ := by
  classical
  exact if hj : 0 < jointLabelWeight u j then
    realVectorLaw (jointConditionalWeight u j) (jointConditionalWeight_nonneg u hu j)
      (sum_jointConditionalWeight_eq_one u j hj) z
    else Measure.dirac 0

instance jointConditionalLaw_isProbabilityMeasure {ι κ : Type*} [Fintype ι]
    (u : ι → κ → ℝ) (hu : ∀ i j, 0 ≤ u i j) (z : ι → ℝ) (j : κ) :
    IsProbabilityMeasure (jointConditionalLaw u hu z j) := by
  classical
  unfold jointConditionalLaw
  split_ifs <;> infer_instance

/-- Every conditional law, including the null-label fallback, has total mass one. -/
theorem jointConditionalLaw_univ {ι κ : Type*} [Fintype ι]
    (u : ι → κ → ℝ) (hu : ∀ i j, 0 ≤ u i j) (z : ι → ℝ) (j : κ) :
    jointConditionalLaw u hu z j Set.univ = 1 := measure_univ

/-- Weighting a conditional law by its original column mass recovers the column's atom measure. -/
theorem jointConditionalLaw_weighted_eq_sum_dirac {ι κ : Type*} [Fintype ι]
    (u : ι → κ → ℝ) (hu : ∀ i j, 0 ≤ u i j) (z : ι → ℝ) (j : κ) :
    ENNReal.ofReal (jointLabelWeight u j) • jointConditionalLaw u hu z j =
      ∑ i, ENNReal.ofReal (u i j) • Measure.dirac (z i) := by
  classical
  by_cases hj : 0 < jointLabelWeight u j
  · rw [jointConditionalLaw, dif_pos hj, realVectorLaw_eq_sum_dirac, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [smul_smul, ← ENNReal.ofReal_mul hj.le, jointLabelWeight_mul_conditional_eq u hu j i]
  · have hq : jointLabelWeight u j = 0 := by
      have hn := jointLabelWeight_nonneg u hu j
      linarith
    have hz (i : ι) : u i j = 0 := by
      have he := jointLabelWeight_mul_conditional_eq u hu j i
      rw [hq, zero_mul] at he
      exact he.symm
    simp only [hq, hz, ENNReal.ofReal_zero, zero_smul, Finset.sum_const_zero]

/-- The actual conditional probability measures reconstruct the prescribed point law exactly. -/
theorem realVectorLaw_eq_jointConditional_mixture {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (cover : κ → Finset ι) {u : ι → κ → ℝ} (hu : u ∈ supportedJointSpace p cover)
    (z : ι → ℝ) :
    realVectorLaw p hp hpsum z =
      ∑ j, ENNReal.ofReal (jointLabelWeight u j) • jointConditionalLaw u hu.1 z j := by
  classical
  rw [realVectorLaw_eq_sum_dirac]
  symm
  simp_rw [jointConditionalLaw_weighted_eq_sum_dirac]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_smul, ← ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ hu.1 i j), hu.2.1 i]

end LpSelfSimilar.FiniteProbability
