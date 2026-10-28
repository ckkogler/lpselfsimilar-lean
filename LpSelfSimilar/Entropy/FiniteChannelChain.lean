module

public import LpSelfSimilar.Entropy.FiniteChannelReference
public import LpSelfSimilar.Probability.PairPMF

@[expose] public section

/-!
The information chain rule for two independent finite inputs and one output.

Averaging the second input produces its genuine Markov channel. Its mixture is
exactly the mixture over the product PMF. The reference-change identity then
splits the information of the pair into the information of the first input and
the average information remaining when that input is known. No regularity of
the output law, and in particular no density assumption, is needed.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory InformationTheory
open scoped ENNReal

namespace LpSelfSimilar.Entropy

noncomputable def averageSecondChannel {ι κ E : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace κ] [MeasurableSpace E] (q : PMF κ) (K : Kernel (ι × κ) E) :
    Kernel ι E := Kernel.ofFunOfCountable fun i ↦ K.sectR i ∘ₘ q.toMeasure

@[simp] lemma averageSecondChannel_apply {ι κ E : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace κ] [MeasurableSpace E] (q : PMF κ) (K : Kernel (ι × κ) E)
    (i : ι) : averageSecondChannel q K i = K.sectR i ∘ₘ q.toMeasure := rfl

instance averageSecondChannel_isMarkov {ι κ E : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace κ] [MeasurableSpace E] (q : PMF κ) (K : Kernel (ι × κ) E)
    [IsMarkovKernel K] : IsMarkovKernel (averageSecondChannel q K) :=
  ⟨fun i ↦ by rw [averageSecondChannel_apply]; infer_instance⟩

lemma channel_mixture_apply {ι E : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace E]
    (p : PMF ι) (K : Kernel ι E) {s : Set E} (hs : MeasurableSet s) :
    (K ∘ₘ p.toMeasure) s = ∑ i, p i * K i s := by
  rw [Measure.bind_apply hs K.aemeasurable, lintegral_fintype]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), mul_comm]

lemma averageSecondChannel_mixture {ι κ E : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace κ] [MeasurableSingletonClass κ] [MeasurableSpace E]
    (p : PMF ι) (q : PMF κ) (K : Kernel (ι × κ) E) [IsMarkovKernel K] :
    averageSecondChannel q K ∘ₘ p.toMeasure = K ∘ₘ (pairPMF p q).toMeasure := by
  ext s hs
  simp only [channel_mixture_apply _ _ hs, averageSecondChannel_apply,
    Kernel.sectR_apply, Fintype.sum_prod_type, pairPMF_apply, Finset.mul_sum, mul_assoc]

/-- The chain rule for independent finite inputs, with zero weights allowed. -/
theorem finiteInformation_pair_chain {ι κ E : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace κ] [MeasurableSingletonClass κ] [MeasurableSpace E]
    (p : PMF ι) (q : PMF κ) (K : Kernel (ι × κ) E) [IsMarkovKernel K] :
    (finiteInformation (pairPMF p q) K).toReal =
      (finiteInformation p (averageSecondChannel q K)).toReal +
        ∑ i, (p i).toReal * (finiteInformation q (K.sectR i)).toReal := by
  classical
  rw [finiteInformation_toReal, finiteInformation_toReal,
    ← averageSecondChannel_mixture p q K]
  simp only [Fintype.sum_prod_type, pairPMF_apply, ENNReal.toReal_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  by_cases hpi : p i = 0
  · simp [hpi]
  · have hρ := channel_klDiv_ne_top p (averageSecondChannel q K) hpi
    have h := finite_channel_reference_identity q (K.sectR i)
      (averageSecondChannel q K ∘ₘ p.toMeasure) hρ
    simp only [Kernel.sectR_apply] at h
    rw [h]
    simp only [averageSecondChannel_apply]
    ring

end LpSelfSimilar.Entropy
