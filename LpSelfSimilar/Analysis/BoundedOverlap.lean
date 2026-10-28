module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Tactic

@[expose] public section

/-! A finite family with bounded pointwise overlap has bounded total measure. -/

open MeasureTheory Metric Set
open scoped ENNReal

namespace LpSelfSimilar

open scoped Classical in
/-- Bounded pointwise overlap controls the sum of the measures of a finite family. -/
lemma sum_measure_le_of_overlap {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Finset ι) (B : ι → Set X) (Ω : Set X) (K : ℕ)
    (hB : ∀ i ∈ s, MeasurableSet (B i)) (hΩ : MeasurableSet Ω)
    (hsub : ∀ i ∈ s, B i ⊆ Ω)
    (hcard : ∀ x, (s.filter (fun i ↦ x ∈ B i)).card ≤ K) :
    (∑ i ∈ s, μ (B i)) ≤ (K : ℝ≥0∞) * μ Ω := by
  classical
  have hcount (x : X) : (∑ i ∈ s, (B i).indicator (1 : X → ℝ≥0∞) x) =
      ((s.filter (fun i ↦ x ∈ B i)).card : ℝ≥0∞) := by
    simp [Set.indicator_apply]
  have hpoint (x : X) : (∑ i ∈ s, (B i).indicator (1 : X → ℝ≥0∞) x) ≤
      (K : ℝ≥0∞) * Ω.indicator (1 : X → ℝ≥0∞) x := by
    by_cases hx : x ∈ Ω
    · rw [hcount, indicator_of_mem hx, Pi.one_apply, mul_one]
      exact_mod_cast hcard x
    · have hzero : (∑ i ∈ s, (B i).indicator (1 : X → ℝ≥0∞) x) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        exact indicator_of_notMem (fun hxi ↦ hx (hsub i hi hxi)) _
      rw [hzero]
      exact bot_le
  calc
    (∑ i ∈ s, μ (B i)) = ∫⁻ x, ∑ i ∈ s, (B i).indicator (1 : X → ℝ≥0∞) x ∂μ := by
      rw [lintegral_finsetSum s (f := fun i ↦ (B i).indicator (1 : X → ℝ≥0∞))
        (fun i hi ↦ measurable_const.indicator (hB i hi))]
      apply Finset.sum_congr rfl
      intro i hi
      exact (lintegral_indicator_one (hB i hi)).symm
    _ ≤ ∫⁻ x, (K : ℝ≥0∞) * Ω.indicator (1 : X → ℝ≥0∞) x ∂μ := lintegral_mono hpoint
    _ = (K : ℝ≥0∞) * μ Ω := by
      rw [lintegral_const_mul (K : ℝ≥0∞) (f := Ω.indicator (1 : X → ℝ≥0∞))
        (measurable_const.indicator hΩ), lintegral_indicator_one hΩ]

end LpSelfSimilar
