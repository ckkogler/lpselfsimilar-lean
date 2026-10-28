module

public import LpSelfSimilar.Probability.SupportedJointLaws
public import LpSelfSimilar.Geometry.FiniteDiameterTranslation

@[expose] public section

/-!
# Support statements for actual finite conditional measures

A set containing every nonzero atom has full probability. Translating the atoms
therefore gives a full-mass interval for the actual mapped measure. At null
conditional labels the fallback `dirac 0` already lies in every `[0,D]` with
`D >= 0`, so the statement covers every label.
-/

open MeasureTheory
open scoped BigOperators ENNReal
open LpSelfSimilar.Entropy

namespace LpSelfSimilar.FiniteProbability

/-- A measurable set containing all nonzero atoms has probability one. -/
theorem realVectorLaw_apply_of_support {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (z : ι → ℝ)
    (s : Set ℝ) (hs : MeasurableSet s) (hsupport : ∀ i, p i ≠ 0 → z i ∈ s) :
    realVectorLaw p hp hsum z s = 1 := by
  classical
  rw [realVectorLaw_apply p hp hsum z s hs]
  calc
    _ = ∑ i, ENNReal.ofReal (p i) := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hpi : p i = 0
      · simp [hpi]
      · exact Set.indicator_of_mem (hsupport i hpi) _
    _ = 1 := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ hp i), hsum]
      simp

/-- Translating a finite atom support translates the actual probability measure into the interval. -/
theorem realVectorLaw_map_sub_Icc {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (z : ι → ℝ)
    (b D : ℝ) (hsupport : ∀ i, p i ≠ 0 → 0 ≤ z i - b ∧ z i - b ≤ D) :
    ((realVectorLaw p hp hsum z).map (fun x ↦ x - b)) (Set.Icc 0 D) = 1 := by
  have hm : Measurable (fun x : ℝ ↦ x - b) := by fun_prop
  rw [Measure.map_apply hm measurableSet_Icc]
  apply realVectorLaw_apply_of_support p hp hsum z _ (hm measurableSet_Icc)
  intro i hi
  exact hsupport i hi

/-- Every conditional probability law admits the translated interval, including null labels. -/
theorem jointConditionalLaw_exists_translated_interval {ι κ : Type*} [Fintype ι]
    (u : ι → κ → ℝ) (hu : ∀ i j, 0 ≤ u i j) (z : ι → ℝ) (j : κ)
    {D : ℝ} (hD : 0 ≤ D)
    (hdiam : ∀ i, jointConditionalWeight u j i ≠ 0 →
      ∀ l, jointConditionalWeight u j l ≠ 0 → |z i - z l| ≤ D) :
    ∃ b : ℝ, ((jointConditionalLaw u hu z j).map (fun x ↦ x - b)) (Set.Icc 0 D) = 1 := by
  classical
  by_cases hj : 0 < jointLabelWeight u j
  · obtain ⟨b, hb⟩ := Geometry.exists_translation_of_nonzero_diameter
      (jointConditionalWeight u j) z hdiam
    refine ⟨b, ?_⟩
    rw [jointConditionalLaw, dif_pos hj]
    exact realVectorLaw_map_sub_Icc _ _ _ z b D hb
  · refine ⟨0, ?_⟩
    simp only [jointConditionalLaw, dif_neg hj, sub_zero]
    rw [Measure.map_dirac' (f := fun x : ℝ ↦ x) measurable_id 0,
      Measure.dirac_apply' _ measurableSet_Icc]
    simp [Set.indicator_apply, hD]

end LpSelfSimilar.FiniteProbability
