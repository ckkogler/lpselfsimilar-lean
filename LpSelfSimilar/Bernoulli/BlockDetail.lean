module

public import LpSelfSimilar.Bernoulli.BlockLaw
public import LpSelfSimilar.Entropy.GridDilation
public import LpSelfSimilar.Entropy.GridDetail

@[expose] public section

/-!
The effective-detail criterion for disjoint Bernoulli blocks. It combines the
actual digit-block convolution law, dilation of normalized conditional variance,
and the finite conditional-variance theorem, including all unused digits.
-/

open MeasureTheory MeasureTheory.Measure
open LpSelfSimilar.Entropy LpSelfSimilar.Gaussian

namespace LpSelfSimilar.Bernoulli

/-- Proved block variance controls higher detail of the full Bernoulli law. -/
theorem higherDetail_le_of_disjoint_block_variance {I : Type*} [DecidableEq I]
    (S : Finset I) (start length : I → ℕ) (s : I → ℝ)
    {l r : ℝ} (hl0 : 0 < l) (hl1 : l < 1) (hr : 0 < r)
    (hd : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint
      (Finset.Ico (start i) (start i + length i))
      (Finset.Ico (start j) (start j + length j)))
    (hs : ∀ i, 0 < s i)
    (hsmall : ∀ i, l ^ start i * s i ≤ conditionalRadius * r)
    (k : ℕ)
    (hbudget : 1001 * (k + 1 : ℕ) * r ^ 2 ≤
      ∑ i ∈ S, (l ^ start i * s i) ^ 2 *
        scaleVariance (digitPMF l (length i)) (digitPMF_support_finite _ _) (s i)) :
    higherDetail (convolution l) (k + 1) r ≤ (1 / 100 : ℝ) ^ (k + 1) := by
  let p (i : I) := blockPMF l (start i) (length i)
  let hp (i : I) := blockPMF_support_finite l (start i) (length i)
  let σ (i : I) := l ^ start i * s i
  have hv (i : I) : scaleVariance (p i) (hp i) (σ i) =
      scaleVariance (digitPMF l (length i)) (digitPMF_support_finite _ _) (s i) := by
    exact scaleVariance_dilation _ _ (pow_pos hl0 (start i)) (s i)
  have hb : 1001 * (k + 1 : ℕ) * r ^ 2 ≤
      ∑ i ∈ S, σ i ^ 2 * scaleVariance (p i) (hp i) (σ i) := by
    simp_rw [hv]
    exact hbudget
  have hdetail := higherDetail_le_of_scaleVariance S p hp σ hr
    (fun i ↦ mul_pos (pow_pos hl0 _) (hs i)) hsmall k hb
  obtain ⟨ρ, hρ, heq⟩ := convolution_disjoint_blocks S start length
    (by rwa [abs_of_pos hl0]) hd
  letI : IsProbabilityMeasure ρ := hρ
  rw [heq, conv_comm]
  exact (higherDetail_conv_le_right ρ (finsetConvolution S (fun i ↦ (p i).toMeasure))
    (Nat.succ_pos k) hr).trans hdetail

end LpSelfSimilar.Bernoulli
