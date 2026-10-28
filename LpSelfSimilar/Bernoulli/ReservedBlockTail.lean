module

public import LpSelfSimilar.Bernoulli.BlockLaw
public import Mathlib.Tactic

@[expose] public section

/-!
# Keeping a specified infinite tail separate from finite blocks

A coordinate cutoff puts every selected digit before a specified tail index.
The remaining finite prefix and the entire infinite tail are then retained as
separate probability factors. This refines the existing disjoint-block identity
without assuming any independence or discarding unused digits.
-/

open MeasureTheory MeasureTheory.Measure

namespace LpSelfSimilar.Bernoulli

/-- A nonempty block above a coordinate cutoff ends before a tail below that cutoff. -/
theorem block_endpoint_le_of_coordinate_cutoff {R κ C : ℝ} (hκ : 0 ≤ κ)
    (start len tail : ℕ) (hlen : 0 < len)
    (hblock : ∀ d < len, C < R - κ * (start + d : ℕ))
    (htail : R - κ * tail ≤ C) : start + len ≤ tail := by
  by_contra he
  have hl : tail ≤ start + (len - 1) := by omega
  have hc := hblock (len - 1) (by omega)
  have hm := mul_le_mul_of_nonneg_left
    (show (tail : ℝ) ≤ (start + (len - 1) : ℕ) by exact_mod_cast hl) hκ
  linarith

/-- Blocks ending before a specified tail split off with an actual unused-prefix probability law. -/
theorem convolution_disjoint_blocks_before {I : Type*} [DecidableEq I] (S : Finset I)
    (start len : I → ℕ) {θ : ℝ} (hθ : |θ| < 1) (tail : ℕ)
    (hend : ∀ i ∈ S, start i + len i ≤ tail)
    (hd : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint
      (Finset.Ico (start i) (start i + len i)) (Finset.Ico (start j) (start j + len j))) :
    ∃ η : Measure ℝ, IsProbabilityMeasure η ∧
      convolution θ =
        (finsetConvolution S (fun i ↦ (blockPMF θ (start i) (len i)).toMeasure) ∗ η) ∗
          (convolution θ).map (fun x ↦ θ ^ tail * x) := by
  classical
  let A := S.biUnion (fun i ↦ Finset.Ico (start i) (start i + len i))
  have hsub : A ⊆ Finset.range tail := by
    intro d hd'
    obtain ⟨i, hi, hdi⟩ := Finset.mem_biUnion.mp hd'
    exact Finset.mem_range.mpr ((Finset.mem_Ico.mp hdi).2.trans_le (hend i hi))
  let η := finsetConvolution (Finset.range tail \ A) (fun d ↦ signLaw (θ ^ d))
  have hA : finsetConvolution A (fun d ↦ signLaw (θ ^ d)) =
      finsetConvolution S (fun i ↦ (blockPMF θ (start i) (len i)).toMeasure) := by
    dsimp only [A]
    rw [finsetConvolution_biUnion S _ _ hd]
    apply finsetConvolution_congr
    intro i _
    exact finsetConvolution_block θ (start i) (len i)
  refine ⟨η, inferInstance, ?_⟩
  calc
    convolution θ = (digitPMF θ tail).toMeasure ∗
        (convolution θ).map (fun x ↦ θ ^ tail * x) := convolution_prefix_tail hθ tail
    _ = _ := by
      rw [← finsetConvolution_prefix,
        finsetConvolution_split (Finset.range tail) A _ hsub, hA]

end LpSelfSimilar.Bernoulli
