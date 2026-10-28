module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import LpSelfSimilar.WeakReverseHolder.Constants
public import LpSelfSimilar.Analysis.DensityMoments
public import LpSelfSimilar.WeakReverseHolder.Expansion

@[expose] public section

/-! Lemma 2.1 of `the earlier version of the same work`, with its exact constants and exponent. -/

open MeasureTheory Metric Set
open scoped ENNReal

namespace LpSelfSimilar

/-- Equation (2.1), for every positive-radius open ball of radius less than one
and every measurable subset of that ball. -/
def SmallSetHypothesis {d : ℕ} (f : Space d → ℝ) (ε η : ℝ) : Prop :=
  ∀ (x : Space d) (r : ℝ), 0 < r → r < 1 →
    ∀ E : Set (Space d), MeasurableSet E → E ⊆ ball x r →
      volume E ≤ ENNReal.ofReal ε * volume (ball x r) →
        (∫ y in E, f y) ≤ η * ∫ y in ball x (2 * r), f y

/-- Lemma 2.1, with `C = 21^d` and the exact exponent from the paper. -/
theorem weak_reverse_holder {d : ℕ} (hd : 1 ≤ d)
    {f : Space d → ℝ} (hf_nonneg : ∀ x, 0 ≤ f x) (hf : Integrable f volume)
    {ε η : ℝ} (hε : ε ∈ Ioo 0 1)
    (hη : η ∈ Ioo 0 (coveringConstant d)⁻¹)
    (hsmall : SmallSetHypothesis f ε η) :
    1 < lemmaExponent d ε η ∧
      MemLp f (ENNReal.ofReal (lemmaExponent d ε η)) volume := by
  refine ⟨one_lt_lemmaExponent hε.1 hε.2 hη.1 hη.2, ?_⟩
  let ν := volume.withDensity (fun x ↦ ENNReal.ofReal (f x))
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity hf.lintegral_lt_top.ne
  have hac : ν ≪ volume := withDensity_absolutelyContinuous _ _
  have hν (E : Set (Space d)) (hE : MeasurableSet E) :
      ν E = ENNReal.ofReal (∫ x in E, f x) := by
    rw [show ν = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) from rfl,
      withDensity_apply _ hE]
    exact (ofReal_integral_eq_lintegral_ofReal hf.integrableOn (ae_of_all _ hf_nonneg)).symm
  have hsmallν : MeasureSmallSetHypothesis ν ε η := by
    intro x r hr hr1 E hE hsub hvol
    rw [hν E hE, hν _ isOpen_ball.measurableSet, ← ENNReal.ofReal_mul hη.1.le]
    exact ENNReal.ofReal_le_ofReal (hsmall x r hr hr1 E hE hsub hvol)
  apply memLp_of_measure_expansion volume hf_nonneg hf
    (one_lt_expansion hε.1 hε.2)
    (volume_real_ball_pos (0 : Space d) zero_lt_one)
    (one_lt_lemmaExponent hε.1 hε.2 hη.1 hη.2)
    (summation_ratio_lt_one hε.1 hε.2 hη.1 hη.2)
  intro E hE hvol
  have hunit : ENNReal.ofReal (volume.real (ball (0 : Space d) 1)) =
      volume (ball (0 : Space d) 1) := ENNReal.ofReal_toReal measure_ball_ne_top
  rw [hunit] at hvol
  obtain ⟨Ω, hΩ, hv, hm⟩ := exists_measure_expansion hd ν hac hε hsmallν hE hvol
  exact ⟨Ω, hΩ.measurableSet, hv, hm⟩

end LpSelfSimilar
