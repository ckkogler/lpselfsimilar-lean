module

public import LpSelfSimilar.Entropy.FiniteAdditiveChannel

@[expose] public section

/-!
The sharp discrete upper bound on finite-signal channel information.

Input labels need not give distinct signal values. Restricting the values to
their finite range and pushing forward the PMF shows that the upper bound is
the Shannon entropy of the actual signal law, not the entropy of its labels.
This distinction is necessary for algebraic-unit digit sums, where collisions
can occur even though the sign words themselves are distinct.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory InformationTheory
open scoped ENNReal

namespace LpSelfSimilar.Entropy

/-- Information is bounded by the entropy of actual signal values, with all
collisions merged through the pushforward PMF. -/
theorem additiveInformation_le_signal_entropy {ι E : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [AddMonoid E] [MeasurableSpace E] [MeasurableSingletonClass E] [MeasurableAdd₂ E]
    (p : PMF ι) (X : ι → E) (ρ : Measure E) [IsProbabilityMeasure ρ] :
    additiveInformation p X ρ ≤
      finiteEntropy (p.map X) (by simpa using (Set.toFinite p.support).image X) := by
  classical
  let R := Set.range X
  let : Fintype R := (Set.finite_range X).fintype
  let f : ι → R := fun i ↦ ⟨X i, ⟨i, rfl⟩⟩
  let K : Kernel R E := (additiveNoiseKernel ρ).comap Subtype.val measurable_subtype_coe
  have hK : (additiveNoiseKernel ρ).comap X (measurable_of_countable X) =
      K.comap f (measurable_of_countable f) := by
    ext i : 1
    rfl
  have hmap : (p.map f).map (Subtype.val : R → E) = p.map X := by
    rw [PMF.map_comp]
    rfl
  have hH := finiteEntropy_map_of_injective (p.map f) (Set.toFinite _)
    (Subtype.val_injective : Function.Injective (Subtype.val : R → E))
  simp only [hmap] at hH
  unfold additiveInformation
  rw [hK, finiteInformation_comap_map]
  exact (finiteInformation_toReal_le_entropy (p.map f) K).trans_eq hH.symm

end LpSelfSimilar.Entropy
