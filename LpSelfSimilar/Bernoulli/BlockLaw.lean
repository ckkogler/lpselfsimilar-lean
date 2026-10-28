module

public import LpSelfSimilar.Probability.MapProbability

public import LpSelfSimilar.Bernoulli.ScaledDigits
public import LpSelfSimilar.Bernoulli.PrefixTail
public import LpSelfSimilar.Probability.ConvolutionPartitions

@[expose] public section

/-!
The actual law of a finite digit block and exact decomposition into disjoint
blocks plus unused digits. Finite convolution regrouping accounts for every
digit; the remaining infinite tail is the previously proved prefix/tail factor.
-/

open MeasureTheory MeasureTheory.Measure

namespace LpSelfSimilar.Bernoulli

/-- The finite law of digits starting at `m`, with `n` terms. -/
noncomputable def blockPMF (l : ℝ) (m n : ℕ) : PMF ℝ :=
  (digitPMF l n).map (fun x ↦ l ^ m * x)

lemma blockPMF_support_finite (l : ℝ) (m n : ℕ) : (blockPMF l m n).support.Finite := by
  simpa only [blockPMF, PMF.support_map] using
    (digitPMF_support_finite l n).image (fun x ↦ l ^ m * x)

lemma image_fin_block (m n : ℕ) :
    (Finset.univ : Finset (Fin n)).image (fun j : Fin n ↦ m + (j : ℕ)) =
      Finset.Ico m (m + n) := by
  ext k
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_Ico]
  constructor
  · rintro ⟨j, rfl⟩
    have hj := j.isLt
    omega
  · intro hk
    refine ⟨⟨k - m, by omega⟩, ?_⟩
    dsimp only
    omega

/-- A block's finite PMF equals convolution of its actual individual digit laws. -/
lemma finsetConvolution_block (l : ℝ) (m n : ℕ) :
    finsetConvolution (Finset.Ico m (m + n)) (fun j ↦ signLaw (l ^ j)) =
      (blockPMF l m n).toMeasure := by
  rw [← image_fin_block m n, finsetConvolution_image _ _
    (show Function.Injective (fun j : Fin n ↦ m + (j : ℕ)) from by
      intro i j hij
      exact Fin.ext (Nat.add_left_cancel hij)), finsetConvolution_univ_fin]
  simp_rw [pow_add]
  rw [← scaled_prefix_law]
  rw [blockPMF, ← PMF.toMeasure_map (fun x : ℝ ↦ l ^ m * x) (digitPMF l n) (by fun_prop), ← digitSum_law]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

lemma finsetConvolution_prefix (l : ℝ) (n : ℕ) :
    finsetConvolution (Finset.range n) (fun j ↦ signLaw (l ^ j)) = (digitPMF l n).toMeasure := by
  have h := finsetConvolution_block l 0 n
  simp only [Nat.Ico_zero_eq_range, zero_add, blockPMF, pow_zero, one_mul] at h
  have he : (digitPMF l n).map (fun x : ℝ ↦ x) = digitPMF l n := PMF.map_id _
  rw [he] at h
  exact h

/-- Disjoint finite blocks are independent convolution factors of the complete
Bernoulli convolution; the remaining factor is an actual probability measure. -/
theorem convolution_disjoint_blocks {I : Type*} [DecidableEq I] (S : Finset I)
    (start length : I → ℕ) {l : ℝ} (hl : |l| < 1)
    (hd : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint
      (Finset.Ico (start i) (start i + length i))
      (Finset.Ico (start j) (start j + length j))) :
    ∃ ρ : Measure ℝ, IsProbabilityMeasure ρ ∧
      convolution l = finsetConvolution S (fun i ↦ (blockPMF l (start i) (length i)).toMeasure) ∗ ρ := by
  classical
  let A := S.biUnion (fun i ↦ Finset.Ico (start i) (start i + length i))
  let M := A.sup id + 1
  have hsub : A ⊆ Finset.range M := by
    intro j hj
    have hle : j ≤ A.sup id := Finset.le_sup (f := id) hj
    exact Finset.mem_range.mpr (by dsimp [M]; omega)
  let tail := (convolution l).map (fun x ↦ l ^ M * x)
  haveI : IsProbabilityMeasure tail := LpSelfSimilar.Probability.isProbabilityMeasure_map (by fun_prop)
  let ρ := finsetConvolution (Finset.range M \ A) (fun j ↦ signLaw (l ^ j)) ∗ tail
  haveI : IsProbabilityMeasure ρ := by dsimp [ρ]; infer_instance
  refine ⟨ρ, inferInstance, ?_⟩
  rw [convolution_prefix_tail hl M, ← finsetConvolution_prefix,
    finsetConvolution_split (Finset.range M) A _ hsub]
  have hA : finsetConvolution A (fun j ↦ signLaw (l ^ j)) =
      finsetConvolution S (fun i ↦ (blockPMF l (start i) (length i)).toMeasure) := by
    dsimp only [A]
    rw [finsetConvolution_biUnion S _ _ hd]
    apply finsetConvolution_congr
    intro i _
    exact finsetConvolution_block l (start i) (length i)
  rw [hA, conv_assoc]

end LpSelfSimilar.Bernoulli
