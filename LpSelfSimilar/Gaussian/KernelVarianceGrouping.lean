module

public import LpSelfSimilar.Gaussian.IndependentKernelGroup
public import LpSelfSimilar.Probability.FinsetConvolution
public import LpSelfSimilar.Analysis.VarianceGrouping

@[expose] public section

/-!
Greedy grouping of arbitrary independent kernel mixtures for revised Lemma 3.3.
The total budget 1001 k r^2 supplies k groups, each with detail at most 1/100.
Every variance bound and independence assertion is derived from actual kernels.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set

namespace LpSelfSimilar.Gaussian

lemma detail_finset_independent_kernel_mixtures_le {I : Type*} (s : Finset I) {Ω : I → Type*}
    [∀ i, MeasurableSpace (Ω i)]
    (P : (i : I) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (P i)]
    (κ : (i : I) → Kernel (Ω i) ℝ) [∀ i, IsMarkovKernel (κ i)]
    (c : (i : I) → Ω i → ℝ) {r : ℝ} (hr : 0 < r)
    (hb : ∀ i, ∀ᵐ ω ∂P i, ∀ᵐ u ∂κ i ω, |u - c i ω| ≤ (1 / 10000 : ℝ) * r)
    (hmass : 1000 * r ^ 2 ≤ ∑ i ∈ s, ∫ ω, variance (fun u : ℝ ↦ u) (κ i ω) ∂P i) :
    detail (finsetConvolution s (fun i ↦ κ i ∘ₘ P i)) r ≤ 1 / 100 := by
  classical
  rw [finsetConvolution_eq_finiteConvolution]
  apply detail_independent_kernel_mixtures_le_one_hundredth
    (fun j ↦ P ((Fintype.equivFin s).symm j))
    (fun j ↦ κ ((Fintype.equivFin s).symm j))
    (fun j ↦ c ((Fintype.equivFin s).symm j)) hr
  · exact fun j ↦ hb _
  · have he : (∑ i ∈ s, ∫ ω, variance (fun u : ℝ ↦ u) (κ i ω) ∂P i) =
        ∑ j, ∫ ω, variance (fun u : ℝ ↦ u) (κ ((Fintype.equivFin s).symm j) ω)
          ∂P ((Fintype.equivFin s).symm j) := by
      rw [← Finset.sum_attach]
      exact Fintype.sum_equiv (Fintype.equivFin s)
        (fun i : s ↦ ∫ ω, variance (fun u : ℝ ↦ u) (κ i ω) ∂P i)
        (fun j ↦ ∫ ω, variance (fun u : ℝ ↦ u) (κ ((Fintype.equivFin s).symm j) ω)
          ∂P ((Fintype.equivFin s).symm j))
        (fun i ↦ by
          rw [Equiv.symm_apply_apply])
    exact he ▸ hmass

/-- The grouping conclusion for arbitrary independent kernel mixtures, with
exact revised constants. No independence or concentration assumption is added to the input. -/
theorem higherDetail_independent_kernel_mixtures {I : Type*} [DecidableEq I] (s : Finset I)
    {Ω : I → Type*} [∀ i, MeasurableSpace (Ω i)]
    (P : (i : I) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (P i)]
    (κ : (i : I) → Kernel (Ω i) ℝ) [∀ i, IsMarkovKernel (κ i)]
    (c : (i : I) → Ω i → ℝ) {r : ℝ} (hr : 0 < r)
    (hb : ∀ i, ∀ᵐ ω ∂P i, ∀ᵐ u ∂κ i ω, |u - c i ω| ≤ (1 / 10000 : ℝ) * r)
    (k : ℕ) (hmass : 1001 * (k + 1 : ℕ) * r ^ 2 ≤
      ∑ i ∈ s, ∫ ω, variance (fun u : ℝ ↦ u) (κ i ω) ∂P i) :
    higherDetail (finsetConvolution s (fun i ↦ κ i ∘ₘ P i)) (k + 1) r ≤
      (1 / 100 : ℝ) ^ (k + 1) := by
  let w (i : I) := ∫ ω, variance (fun u : ℝ ↦ u) (κ i ω) ∂P i
  have hw (i : I) : 0 ≤ w i ∧ w i ≤ r ^ 2 := by
    refine ⟨integral_nonneg (fun ω ↦ variance_nonneg _ _), ?_⟩
    have hrad : ((1 / 10000 : ℝ) * r) ^ 2 ≤ r ^ 2 := by nlinarith [sq_nonneg r]
    have hpoint : ∀ᵐ ω ∂P i, variance (fun u : ℝ ↦ u) (κ i ω) ≤ r ^ 2 :=
      (hb i).mono (fun ω hω ↦ (variance_kernel_le_radius_sq (κ i) ω hω).trans hrad)
    have h := integral_mono_ae (integrable_variance_kernel_of_ae_radius (P i) (κ i) (hb i))
      (integrable_const (r ^ 2)) hpoint
    simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using h
  induction k generalizing s with
  | zero =>
    rw [higherDetail_one _ hr]
    have hm : 1000 * r ^ 2 ≤ ∑ i ∈ s, w i := by
      change 1001 * (0 + 1 : ℕ) * r ^ 2 ≤ _ at hmass
      norm_num at hmass
      linarith [sq_nonneg r]
    simpa using detail_finset_independent_kernel_mixtures_le s P κ c hr hb hm
  | succ k ih =>
    have htotal : 1000 * r ^ 2 ≤ ∑ i ∈ s, w i := by
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      simp only [Nat.cast_add, Nat.cast_one] at hmass
      nlinarith [mul_nonneg hk (sq_nonneg r)]
    obtain ⟨t, hts, ht, hu⟩ := exists_subset_sum_between s w
      (mul_nonneg (by norm_num) (sq_nonneg r)) (sq_nonneg r)
      (fun i _ ↦ hw i) htotal
    have he : (∑ i ∈ s \ t, w i) + (∑ i ∈ t, w i) = ∑ i ∈ s, w i :=
      Finset.sum_sdiff hts
    have hrest : 1001 * (k + 1 : ℕ) * r ^ 2 ≤ ∑ i ∈ s \ t, w i := by
      simp only [Nat.cast_add, Nat.cast_one] at hmass ⊢
      linarith
    have hg := detail_finset_independent_kernel_mixtures_le t P κ c hr hb ht
    have hrec := ih (s \ t) hrest
    rw [finsetConvolution_split s t _ hts]
    have hprod := higherDetail_conv_le
      (finsetConvolution t (fun i ↦ κ i ∘ₘ P i))
      (finsetConvolution (s \ t) (fun i ↦ κ i ∘ₘ P i))
      (by norm_num : 0 < (1 : ℕ)) (Nat.succ_pos k) hr
    rw [higherDetail_one _ hr] at hprod
    have hmul := mul_le_mul hg hrec (higherDetail_nonneg _ _ _) (by norm_num : (0 : ℝ) ≤ 1 / 100)
    have horder : 1 + (k + 1) = k + 1 + 1 := by omega
    rw [horder] at hprod
    exact hprod.trans (hmul.trans_eq (by ring))


end LpSelfSimilar.Gaussian
