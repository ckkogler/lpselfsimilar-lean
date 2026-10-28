module

public import LpSelfSimilar.Gaussian.KernelVarianceGrouping
public import LpSelfSimilar.Probability.RealConditionalVariance

@[expose] public section

/-!
Revised Lemma 3.3 for arbitrary conditioning sigma-algebras, with epsilon_0=10^-4
and total expected conditional variance 1001 k r^2. Real regular conditional laws
are sampled on an independent product of their base spaces. Their marginal
mixtures reconstruct the original independent summands, so the proof does not
require a finite or countably generated conditioning sigma-algebra.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory

namespace LpSelfSimilar.Gaussian

/-- A slightly stronger form: independent summands suffice; the conditioning
sigma-algebras themselves need not be independent. -/
theorem independent_conditional_variance_detail {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (m : Fin n → MeasurableSpace Ω) (hm : ∀ i, m i ≤ mΩ)
    (X C : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hLp : ∀ i, MemLp (X i) 2 P) (hC : ∀ i, Measurable[m i] (C i))
    (hind : iIndepFun X P) {r : ℝ} (hr : 0 < r)
    (hb : ∀ i, ∀ᵐ ω ∂P, |X i ω - C i ω| ≤ (1 / 10000 : ℝ) * r)
    (k : ℕ) (hk : 1 ≤ k)
    (hmass : 1001 * (k : ℝ) * r ^ 2 ≤ ∑ i, ∫ ω, condVar (m i) (X i) P ω ∂P) :
    higherDetail (P.map (fun ω ↦ ∑ i, X i ω)) k r ≤ (1 / 100 : ℝ) ^ k := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  let Q (i : Fin n) : Measure[m i] Ω := P.trim (hm i)
  let κ (i : Fin n) : @Kernel Ω ℝ (m i) inferInstance := realConditionalLaw (m i) (X i) P
  have hQ (i : Fin n) : @IsProbabilityMeasure Ω (m i) (Q i) := by
    refine ⟨?_⟩
    dsimp only [Q]
    rw [trim_measurableSet_eq (hm i) (@MeasurableSet.univ Ω (m i)), measure_univ]
  have hκ (i : Fin n) : @IsMarkovKernel Ω ℝ (m i) inferInstance (κ i) := by
    dsimp only [κ]
    infer_instance
  have hbound (i : Fin n) : ∀ᵐ ω ∂Q i, ∀ᵐ u ∂κ i ω,
      |u - C i ω| ≤ (1 / 10000 : ℝ) * r :=
    realConditionalLaw_ae_abs_sub_le (hm i) (hX i) (hC i) (hb i)
  have he : (∑ i, ∫ ω, condVar (m i) (X i) P ω ∂P) =
      ∑ i, ∫ ω, variance (fun u : ℝ ↦ u) (κ i ω) ∂Q i := by
    apply Finset.sum_congr rfl
    intro i _
    exact integral_condVar_eq_integral_variance_realConditionalLaw (hm i) (hLp i)
  have hg := @higherDetail_independent_kernel_mixtures (Fin n) _ Finset.univ
    (fun _ : Fin n ↦ Ω) m Q hQ κ hκ C r hr hbound k (he ▸ hmass)
  have hrep (i : Fin n) : κ i ∘ₘ Q i = P.map (X i) :=
    realConditionalLaw_comp_trim (hm i) (hX i).aemeasurable
  simp_rw [hrep] at hg
  rw [finsetConvolution_univ_fin] at hg
  rw [map_sum_eq_finiteConvolution hX hind]
  exact hg

/-- **Lemma 3.3 of On Lp density of self similar measures and Bernoulli convolutions.** The paper's full sigma-algebra independence
hypothesis implies the independent-summand form above. All constants are exact. -/
theorem conditional_variance_detail_explicit {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (m : Fin n → MeasurableSpace Ω) (hm : ∀ i, m i ≤ mΩ)
    (X C : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hLp : ∀ i, MemLp (X i) 2 P) (hC : ∀ i, Measurable[m i] (C i))
    (hind : iIndep (fun i ↦ (borel ℝ).comap (X i) ⊔ m i) P)
    {r : ℝ} (hr : 0 < r)
    (hb : ∀ i, ∀ᵐ ω ∂P, |X i ω - C i ω| ≤ (1 / 10000 : ℝ) * r)
    (k : ℕ) (hk : 1 ≤ k)
    (hmass : 1001 * (k : ℝ) * r ^ 2 ≤ ∑ i, ∫ ω, condVar (m i) (X i) P ω ∂P) :
    higherDetail (P.map (fun ω ↦ ∑ i, X i ω)) k r ≤ (1 / 100 : ℝ) ^ k := by
  have hi : iIndepFun X P := (iIndepFun_iff_iIndep (fun _ ↦ borel ℝ) X P).2
    (iIndep_of_iIndep_of_le hind (fun _ ↦ le_sup_left))
  exact independent_conditional_variance_detail P m hm X C hX hLp hC hi hr hb k hk hmass

end LpSelfSimilar.Gaussian
