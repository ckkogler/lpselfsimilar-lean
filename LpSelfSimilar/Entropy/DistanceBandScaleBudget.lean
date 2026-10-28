module

public import LpSelfSimilar.Entropy.MeasurableGraphChoices
public import LpSelfSimilar.Entropy.GraphSeparationScale
public import LpSelfSimilar.Analysis.DecreasingScaleBudget

@[expose] public section

/-!
# The integrated finite distance-band entropy budget

The band entropy is a measurable function with finite range, hence integrable on
every bounded scale interval. Its single-scale lower bound is the backward
four-step increment of decreasing near-graph entropy. Separation kills the final
tail, leaving four times the entropy at the initial scale.
-/

open MeasureTheory Set
open scoped BigOperators

namespace LpSelfSimilar.Entropy

/-- Any measurable real function of a fixed finite graph family is locally integrable. -/
theorem intervalIntegrable_function_of_finite_graph {ι : Type*} [Fintype ι]
    (g : ℝ → SimpleGraph ι) (F : SimpleGraph ι → ℝ)
    (hm : Measurable (fun x ↦ F (g x))) (a b : ℝ) :
    IntervalIntegrable (fun x ↦ F (g x)) volume a b := by
  classical
  let M : ℝ := ∑ G : SimpleGraph ι, ‖F G‖
  apply (intervalIntegrable_const (c := M)).mono_fun' hm.aestronglyMeasurable
  filter_upwards [] with x
  exact Finset.single_le_sum (fun G _ ↦ norm_nonneg (F G)) (Finset.mem_univ (g x))

/-- The attained band entropy at dyadic scales is measurable. -/
theorem measurable_dyadic_distanceBandConditionalEntropyBits {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (p : ι → ℝ) :
    Measurable (fun j : ℝ ↦ distanceBandConditionalEntropyBits z ((2 : ℝ) ^ (-j)) p) := by
  apply (measurable_distanceBandConditionalEntropyBits z p).comp
  exact measurable_const.pow measurable_id.neg

/-- No integrability assumption is needed for the finite distance-band maximum. -/
theorem intervalIntegrable_dyadic_distanceBandConditionalEntropyBits {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (p : ι → ℝ) (a b : ℝ) :
    IntervalIntegrable (fun j : ℝ ↦
      distanceBandConditionalEntropyBits z ((2 : ℝ) ^ (-j)) p) volume a b :=
  intervalIntegrable_function_of_finite_graph
    (fun j ↦ distanceBandGraph z ((2 : ℝ) ^ (-j)) (16 * (2 : ℝ) ^ (-j)))
    (fun G ↦ graphConditionalEntropyBits Gᶜ p)
    (measurable_dyadic_distanceBandConditionalEntropyBits z p) a b

/-- Exact telescoping budget, with four dyadic scale units and the separation endpoint included. -/
theorem four_mul_near_entropy_le_distanceBand_integral {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (a b : ℝ) (hab : a ≤ b)
    (hsep : ∀ i k, i ≠ k → (2 : ℝ) ^ (-b) ≤ |z i - z k|) :
    4 * graphEntropyBits (nearDistanceGraph z ((2 : ℝ) ^ (-a))) p ≤
      ∫ j in a..b + 4, distanceBandConditionalEntropyBits z ((2 : ℝ) ^ (-j)) p := by
  apply Analysis.initial_value_le_integral_of_backward_difference
    (fun j ↦ graphEntropyBits (nearDistanceGraph z ((2 : ℝ) ^ (-j))) p)
    _ (antitone_dyadic_near_graphEntropyBits z p hp) a b 4 hab (by norm_num)
    (fun j hj ↦ dyadic_near_graphEntropyBits_eq_zero_of_separated z p hp b hsep hj)
    (intervalIntegrable_dyadic_distanceBandConditionalEntropyBits z p a (b + 4))
  intro j hj
  have he : (2 : ℝ) ^ (-(j - 4)) = 16 * (2 : ℝ) ^ (-j) := by
    rw [show -(j - 4) = (4 : ℝ) + -j by ring, Real.rpow_add (by norm_num)]
    norm_num
  simpa only [he] using near_difference_le_distanceBandConditionalEntropyBits z
    ((2 : ℝ) ^ (-j)) (Real.rpow_pos_of_pos (by norm_num) _) p hp hsum

end LpSelfSimilar.Entropy
