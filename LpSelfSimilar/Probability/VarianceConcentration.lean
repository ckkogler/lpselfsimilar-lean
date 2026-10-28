module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
Concentration of a sum of independent nonnegative bounded variables. Their
variance is at most the bound times their mean, and Chebyshev gives the precise
lower-tail estimate used for conditional variances in Lemma 3.3.
-/

open MeasureTheory ProbabilityTheory Real Set

namespace LpSelfSimilar

lemma variance_le_bound_mul_mean {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {W : Ω → ℝ} (hW : Measurable W) {R : ℝ}
    (hb : ∀ᵐ ω ∂P, W ω ∈ Icc 0 R) :
    variance W P ≤ R * ∫ ω, W ω ∂P := by
  have hlp : MemLp W 2 P := memLp_of_bounded hb hW.aestronglyMeasurable 2
  have hi := hlp.integrable (by norm_num)
  have hsq : Integrable (fun ω ↦ W ω ^ 2) P := hlp.integrable_sq
  have h := integral_mono_ae hsq (hi.const_mul R) (hb.mono (fun ω hω ↦ by
    change W ω ^ 2 ≤ R * W ω
    nlinarith [mul_nonneg hω.1 (sub_nonneg.mpr hω.2)]))
  have hv := variance_le_expectation_sq (μ := P) hW.aestronglyMeasurable
  simp only [Pi.pow_apply, integral_const_mul] at hv h
  exact hv.trans h

/-- Chebyshev's lower-tail bound, with all variance assumptions derived from
independence and bounded nonnegative summands. -/
theorem probability_sum_lt_half_mean_le {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : I → Ω → ℝ)
    (hW : ∀ i, Measurable (W i)) (hind : iIndepFun W P) {R : ℝ} (hR : 0 ≤ R)
    (hb : ∀ i, ∀ᵐ ω ∂P, W i ω ∈ Icc 0 R)
    (hm : 0 < ∑ i, ∫ ω, W i ω ∂P) :
    P.real {ω | (∑ i, W i ω) < (∑ i, ∫ ω, W i ω ∂P) / 2} ≤
      4 * R / (∑ i, ∫ ω, W i ω ∂P) := by
  let m := ∑ i, ∫ ω, W i ω ∂P
  let S (ω : Ω) := ∑ i, W i ω
  have hlp (i : I) : MemLp (W i) 2 P := memLp_of_bounded (hb i) (hW i).aestronglyMeasurable 2
  have hS : MemLp S 2 P := memLp_finsetSum Finset.univ (fun i _ ↦ hlp i)
  have hmean : (∫ ω, S ω ∂P) = m :=
    integral_finsetSum _ (fun i _ ↦ (hlp i).integrable (by norm_num))
  have hvar : variance S P = ∑ i, variance (W i) P := by
    have h := IndepFun.variance_sum (μ := P) (s := Finset.univ)
      (fun i _ ↦ hlp i) (fun i _ j _ hij ↦ hind.indepFun hij)
    have he : S = ∑ i, W i := by
      funext ω
      simp only [S, Finset.sum_apply]
    rw [he]
    exact h
  have hv : variance S P ≤ R * m := by
    rw [hvar]
    dsimp only [m]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ ↦ variance_le_bound_mul_mean P (hW i) (hb i))
  have hcheb := meas_ge_le_variance_div_sq hS (show 0 < m / 2 by positivity)
  rw [hmean] at hcheb
  have hsub : {ω | S ω < m / 2} ⊆ {ω | m / 2 ≤ |S ω - m|} := by
    intro ω hω
    change m / 2 ≤ |S ω - m|
    have hn := neg_le_abs (S ω - m)
    change S ω < m / 2 at hω
    linarith
  have hprob := (measure_mono hsub).trans hcheb
  have hreal := ENNReal.toReal_mono (by simp) hprob
  rw [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _))] at hreal
  change P.real {ω | S ω < m / 2} ≤ _ at hreal
  apply hreal.trans
  have hden : (m / 2) ^ 2 > 0 := by positivity
  apply (div_le_iff₀ hden).2
  have he : 4 * R / m * (m / 2) ^ 2 = R * m := by field_simp; ring
  rw [he]
  exact hv

end LpSelfSimilar
