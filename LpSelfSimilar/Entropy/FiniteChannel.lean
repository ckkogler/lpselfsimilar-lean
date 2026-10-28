module

public import LpSelfSimilar.Entropy.AtomicRelativeEntropy

@[expose] public section

/-!
Information carried by a channel with a finite input alphabet.

Information is the probability-weighted KL divergence of each conditional output
law from the actual mixture. Kernel composition gives the mixture, and KL data
processing proves that further randomization cannot increase information. The
point-mass formula bounds information by the input Shannon entropy, proving
finiteness before any conversion to real numbers. Zero input weights are allowed.
These statements apply to arbitrary output spaces and will be used for Gaussian
channels in every finite Euclidean dimension.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory InformationTheory
open scoped ENNReal

namespace LpSelfSimilar.Entropy

/-- Mutual information in nats for a finite input and an actual Markov channel.
The definition also makes sense for other kernels, possibly with infinite value. -/
noncomputable def finiteInformation {ι E : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSpace E] (p : PMF ι) (κ : Kernel ι E) : ℝ≥0∞ :=
  ∑ i, p i * klDiv (κ i) (κ ∘ₘ p.toMeasure)

lemma finiteEntropy_eq_sum_fintype {ι : Type*} [Fintype ι] (p : PMF ι) :
    finiteEntropy p (Set.toFinite _) = ∑ i, Real.negMulLog (p i).toReal := by
  classical
  unfold finiteEntropy
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i hi hnot
  have hz : p i = 0 := by simpa using hnot
  simp [hz]

/-- Each positive input atom is bounded by its self-information. -/
lemma channel_klDiv_le_neg_log {ι E : Type*} [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [MeasurableSpace E] (p : PMF ι)
    (κ : Kernel ι E) [IsMarkovKernel κ] {i : ι} (hi : p i ≠ 0) :
    klDiv (κ i) (κ ∘ₘ p.toMeasure) ≤ ENNReal.ofReal (-Real.log (p i).toReal) := by
  have h := klDiv_comp_right_le (Measure.dirac i) p.toMeasure κ
  simpa only [Measure.dirac_bind κ.measurable i, klDiv_dirac_pmf p hi] using h

lemma channel_klDiv_ne_top {ι E : Type*} [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [MeasurableSpace E] (p : PMF ι)
    (κ : Kernel ι E) [IsMarkovKernel κ] {i : ι} (hi : p i ≠ 0) :
    klDiv (κ i) (κ ∘ₘ p.toMeasure) ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (channel_klDiv_le_neg_log p κ hi)

/-- Randomizing the output through another Markov kernel cannot increase
information; the two mixture measures are identified by associativity. -/
theorem finiteInformation_comp_le {ι E F : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSpace E] [MeasurableSpace F]
    (p : PMF ι) (κ : Kernel ι E) (η : Kernel E F)
    [IsMarkovKernel κ] [IsMarkovKernel η] :
    finiteInformation p (η ∘ₖ κ) ≤ finiteInformation p κ := by
  unfold finiteInformation
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_right
  have h := klDiv_comp_right_le (κ i) (κ ∘ₘ p.toMeasure) η
  simpa only [Measure.comp_assoc, Kernel.comp_apply] using h

/-- The Shannon entropy bound proves finiteness for every finite input alphabet,
with zero weights handled before invoking the point-mass KL formula. -/
theorem finiteInformation_le_entropy {ι E : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace E]
    (p : PMF ι) (κ : Kernel ι E) [IsMarkovKernel κ] :
    finiteInformation p κ ≤ ENNReal.ofReal (finiteEntropy p (Set.toFinite _)) := by
  classical
  rw [finiteEntropy_eq_sum_fintype, ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_le_sum
    intro i hi
    by_cases hpi : p i = 0
    · simp [hpi]
    · calc
        _ ≤ p i * ENNReal.ofReal (-Real.log (p i).toReal) :=
          mul_le_mul_right (channel_klDiv_le_neg_log p κ hpi) _
        _ = ENNReal.ofReal (Real.negMulLog (p i).toReal) := by
          calc
            _ = ENNReal.ofReal (p i).toReal *
                ENNReal.ofReal (-Real.log (p i).toReal) := by
              rw [ENNReal.ofReal_toReal (p.apply_ne_top i)]
            _ = ENNReal.ofReal ((p i).toReal * (-Real.log (p i).toReal)) :=
              (ENNReal.ofReal_mul ENNReal.toReal_nonneg).symm
            _ = _ := by congr 1; unfold Real.negMulLog; ring
  · intro i hi
    exact Real.negMulLog_nonneg ENNReal.toReal_nonneg
      (ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using p.coe_le_one i))

theorem finiteInformation_ne_top {ι E : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace E]
    (p : PMF ι) (κ : Kernel ι E) [IsMarkovKernel κ] : finiteInformation p κ ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (finiteInformation_le_entropy p κ)

/-- Conversion to real numbers is legitimate because all positive-weight
divergences are finite; a zero-weight input contributes zero even at infinity. -/
theorem finiteInformation_toReal {ι E : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace E]
    (p : PMF ι) (κ : Kernel ι E) [IsMarkovKernel κ] :
    (finiteInformation p κ).toReal =
      ∑ i, (p i).toReal * (klDiv (κ i) (κ ∘ₘ p.toMeasure)).toReal := by
  unfold finiteInformation
  rw [ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul]
  · intro i hi
    by_cases hpi : p i = 0
    · simp [hpi]
    · exact ENNReal.mul_ne_top (p.apply_ne_top i) (channel_klDiv_ne_top p κ hpi)

theorem finiteInformation_toReal_le_entropy {ι E : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace E]
    (p : PMF ι) (κ : Kernel ι E) [IsMarkovKernel κ] :
    (finiteInformation p κ).toReal ≤ finiteEntropy p (Set.toFinite _) := by
  simpa only [ENNReal.toReal_ofReal (finiteEntropy_nonneg p (Set.toFinite _))]
    using ENNReal.toReal_mono ENNReal.ofReal_ne_top (finiteInformation_le_entropy p κ)

end LpSelfSimilar.Entropy
