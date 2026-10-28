module

public import LpSelfSimilar.Probability.PairPMF
public import Mathlib.Probability.Distributions.Uniform

@[expose] public section

/-!
Uniform finite probability laws under reindexing and independent pairing.

These identities let a finite digit word be split at any coordinate while
retaining the actual uniform word law. They will justify discarding all other
digits in the finite matrix-entropy telescope, with no independence assumption.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped ENNReal

namespace LpSelfSimilar

lemma uniformPMF_map_equiv {α β : Type*} [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] (e : α ≃ β) :
    (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype β := by
  classical
  ext b
  rw [PMF.map_apply, tsum_eq_single (e.symm b)]
  · simp [PMF.uniformOfFintype_apply, Fintype.card_congr e]
  · intro a ha
    have hne : b ≠ e a := fun h ↦ ha (by simpa using congrArg e.symm h.symm)
    simp [hne]

lemma pairPMF_uniform {α β : Type*} [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β] :
    pairPMF (PMF.uniformOfFintype α) (PMF.uniformOfFintype β) =
      PMF.uniformOfFintype (α × β) := by
  ext ⟨a, b⟩
  simp only [pairPMF_apply, PMF.uniformOfFintype_apply, Fintype.card_prod,
    Nat.cast_mul]
  rw [ENNReal.mul_inv (by simp) (by simp)]

end LpSelfSimilar
