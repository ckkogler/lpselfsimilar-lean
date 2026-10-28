module

public import LpSelfSimilar.Gaussian.KernelVarianceGrouping
public import LpSelfSimilar.Probability.FiniteKernel

@[expose] public section

/-!
The revised conditional-radius estimate specialized to actual finite mixtures.
All finite conditional laws are measurable kernels, and their kernel composition
is their original PMF mixture. The radius is exactly 10^-4.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory

namespace LpSelfSimilar.Gaussian

/-- Finite-mixture specialization of revised Lemma 3.3, with the exact radius. -/
theorem higherDetail_independent_mixtures_explicit {I : Type*} [DecidableEq I]
    (S : Finset I) {Ω : I → Type*} [∀ i, Fintype (Ω i)]
    [∀ i, MeasurableSpace (Ω i)] [∀ i, MeasurableSingletonClass (Ω i)]
    (p : (i : I) → PMF (Ω i)) (μ : (i : I) → Ω i → Measure ℝ)
    [∀ i ω, IsProbabilityMeasure (μ i ω)] (c : (i : I) → Ω i → ℝ)
    {r : ℝ} (hr : 0 < r)
    (hb : ∀ i ω, ∀ᵐ u ∂μ i ω, |u - c i ω| ≤ (1 / 10000 : ℝ) * r)
    (k : ℕ) (hmass : 1001 * (k + 1 : ℕ) * r ^ 2 ≤
      ∑ i ∈ S, ∫ ω, variance (fun u : ℝ ↦ u) (μ i ω) ∂(p i).toMeasure) :
    higherDetail (finsetConvolution S (fun i ↦ pmfMixture (p i) (μ i))) (k + 1) r ≤
      (1 / 100 : ℝ) ^ (k + 1) := by
  let κ (i : I) : Kernel (Ω i) ℝ := Kernel.ofFunOfCountable (μ i)
  let (i : I) : IsMarkovKernel (κ i) := ⟨fun ω ↦ (inferInstance : IsProbabilityMeasure (μ i ω))⟩
  have h := higherDetail_independent_kernel_mixtures S (fun i ↦ (p i).toMeasure)
    κ c hr (fun i ↦ Filter.Eventually.of_forall (hb i)) k hmass
  simp_rw [finite_kernel_comp_eq_pmfMixture] at h
  exact h

end LpSelfSimilar.Gaussian
