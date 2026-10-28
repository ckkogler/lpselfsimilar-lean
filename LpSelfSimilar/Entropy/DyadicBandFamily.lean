module

public import LpSelfSimilar.Entropy.JointCancellationBounds
public import LpSelfSimilar.Entropy.DistanceBandScaleBudget

@[expose] public section

/-!
# Actual maximizing joint laws across dyadic scales

The family records the measurable joint arrays, their prescribed marginal and
band supports, and their attained entropy. Its cancellation is the expectation
under these same label weights. This keeps the cancellation budget connected to
the actual conditional laws needed later for independent digit blocks.
-/

open MeasureTheory Set
open scoped BigOperators

namespace LpSelfSimilar.Entropy

/-- A measurable family of actual entropy-maximizing joint laws at every dyadic scale. -/
structure MaximizingBandFamily {ι : Type*} [Fintype ι] (z p : ι → ℝ) where
  joint : ℝ → ι → Finset ι → ℝ
  measurable_joint : Measurable joint
  supported : ∀ j, joint j ∈ supportedJointSpace p
    (graphIndependentCover (distanceBandGraph z ((2 : ℝ) ^ (-j))
      (16 * (2 : ℝ) ^ (-j)))ᶜ)
  entropy_eq : ∀ j, jointConditionalEntropy (joint j) / Real.log 2 =
    distanceBandConditionalEntropyBits z ((2 : ℝ) ^ (-j)) p

/-- Such a family exists; its measurability follows from the finite number of band graphs. -/
theorem nonempty_maximizingBandFamily {ι : Type*} [Fintype ι]
    (z p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) : Nonempty (MaximizingBandFamily z p) := by
  obtain ⟨u, hu, hs, he⟩ := exists_measurable_distanceBand_maximizer z p hp
  have hm : Measurable (fun j : ℝ ↦ (2 : ℝ) ^ (-j)) :=
    measurable_const.pow measurable_id.neg
  exact ⟨⟨fun j ↦ u ((2 : ℝ) ^ (-j)), hu.comp hm, fun j ↦ hs _, fun j ↦ he _⟩⟩

/-- Expected cancellation uses the original column probabilities of the maximizing joint law. -/
noncomputable def MaximizingBandFamily.cancellation {ι : Type*} [Fintype ι]
    {z p : ι → ℝ} (F : MaximizingBandFamily z p) (j : ℝ) : ℝ :=
  jointExpectedCancellation (F.joint j)

/-- The cancellation function is measurable without another choice or regularity assumption. -/
theorem MaximizingBandFamily.measurable_cancellation {ι : Type*} [Fintype ι]
    {z p : ι → ℝ} (F : MaximizingBandFamily z p) : Measurable F.cancellation :=
  measurable_jointExpectedCancellation F.measurable_joint

/-- The exact range of the averaged cancellation, uniformly in the scale. -/
theorem MaximizingBandFamily.cancellation_mem_Icc {ι : Type*} [Fintype ι]
    {z p : ι → ℝ} (F : MaximizingBandFamily z p) (hsum : ∑ i, p i = 1) (j : ℝ) :
    F.cancellation j ∈ Icc 0 (1 - Real.sqrt (7 / 16)) := by
  refine ⟨jointExpectedCancellation_nonneg _ (F.supported j).1, ?_⟩
  exact jointExpectedCancellation_le_sixteen_atom_bound p _ (F.supported j) hsum
    (bandIndependentCover_card_le_sixteen z _ (Real.rpow_pos_of_pos (by norm_num) _))

/-- Boundedness proves integrability on every bounded interval. -/
theorem MaximizingBandFamily.intervalIntegrable_cancellation {ι : Type*} [Fintype ι]
    {z p : ι → ℝ} (F : MaximizingBandFamily z p) (hsum : ∑ i, p i = 1) (a b : ℝ) :
    IntervalIntegrable F.cancellation volume a b := by
  apply (intervalIntegrable_const (c := (1 : ℝ))).mono_fun'
    F.measurable_cancellation.aestronglyMeasurable
  filter_upwards [] with j
  have hr := F.cancellation_mem_Icc hsum j
  rw [Real.norm_eq_abs, abs_of_nonneg hr.1]
  exact hr.2.trans (sub_le_self 1 (Real.sqrt_nonneg _))

/-- The entropy inequality holds for these same maximizing laws, at every scale and every slope. -/
theorem MaximizingBandFamily.entropy_le_cancellation {ι : Type*} [Fintype ι]
    {z p : ι → ℝ} (F : MaximizingBandFamily z p) (hsum : ∑ i, p i = 1)
    {α : ℝ} (hα : 0 < α) (j : ℝ) :
    distanceBandConditionalEntropyBits z ((2 : ℝ) ^ (-j)) p ≤ α * F.cancellation j +
      Real.log (1 + 15 * (2 : ℝ) ^ (-α * (13 / 40 : ℝ))) / Real.log 2 := by
  rw [← F.entropy_eq j]
  exact supportedJoint_entropy_le_expected_cancellation p _ (F.supported j) hsum
    (bandIndependentCover_card_le_sixteen z _ (Real.rpow_pos_of_pos (by norm_num) _)) hα

end LpSelfSimilar.Entropy
