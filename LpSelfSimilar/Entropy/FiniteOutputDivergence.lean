module

public import LpSelfSimilar.Entropy.AtomicRelativeEntropy
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

@[expose] public section

/-!
# Relative entropy on finite output spaces

Positive reference masses identify the Radon--Nikodym derivative at every
point. The resulting finite sum computes KL divergence without a positivity
assumption on the first law. On two points the divergence from the fair law
is exactly log 2 minus binary entropy, including deterministic endpoint laws.
-/

open MeasureTheory MeasureTheory.Measure InformationTheory Real
open scoped ENNReal

namespace LpSelfSimilar.Entropy

/-- A reference law with positive mass at every point dominates every measure. -/
theorem absolutelyContinuous_of_positive_atoms {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ ν : Measure α)
    (hν : ∀ a, 0 < ν {a}) : μ ≪ ν := by
  intro s hs
  have hempty : s = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have h := measure_mono (Set.singleton_subset_iff.mpr ha) (μ := ν)
    rw [hs] at h
    exact (not_le_of_gt (hν a)) h
  simp [hempty]

/-- The atomic Radon--Nikodym identity after conversion to real numbers. -/
theorem toReal_rnDeriv_at_positive_atom {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    {a : α} (ha : 0 < ν {a}) :
    (μ.rnDeriv ν a).toReal = (μ {a}).toReal / (ν {a}).toReal := by
  have he := Measure.withDensity_rnDeriv_eq μ ν hμν
  have hm := congrArg (fun ρ : Measure α => ρ {a}) he
  have hm' : μ.rnDeriv ν a * ν {a} = μ {a} := by
    simpa [withDensity_apply, lintegral_singleton, mul_comm] using hm
  have hr := congrArg ENNReal.toReal hm'
  rw [ENNReal.toReal_mul] at hr
  exact (eq_div_iff (ENNReal.toReal_pos ha.ne' (measure_ne_top ν _)).ne').mpr hr

/-- Exact real KL divergence for finite probability laws and positive reference masses. -/
theorem toReal_klDiv_fintype {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hν : ∀ a, 0 < ν {a}) :
    (klDiv μ ν).toReal =
      ∑ a, (μ {a}).toReal * log ((μ {a}).toReal / (ν {a}).toReal) := by
  have hac := absolutelyContinuous_of_positive_atoms μ ν hν
  rw [toReal_klDiv_of_measure_eq hac (by simp), integral_fintype Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [measureReal_def, smul_eq_mul, llr,
    toReal_rnDeriv_at_positive_atom μ ν hac (hν a)]

/-- The logarithmic expansion remains valid after multiplication by a zero mass. -/
theorem mul_log_div_half (p : ℝ) : p * log (p / (1 / 2)) = p * log p + p * log 2 := by
  by_cases hp : p = 0
  · simp [hp]
  · rw [show p / (1 / 2) = p * 2 by ring, log_mul hp (by norm_num)]
    ring

/-- Two-point divergence from the fair law is the missing binary entropy. -/
theorem toReal_klDiv_bool_uniform (μ ν : Measure Bool)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hν : ∀ b, ν {b} = (1 / 2 : ℝ≥0∞)) :
    (klDiv μ ν).toReal = log 2 - binEntropy (μ {false}).toReal := by
  have hp : (μ {false}).toReal + (μ {true}).toReal = 1 := by
    have h : (∫ _ : Bool, (1 : ℝ) ∂μ) = 1 := by
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rw [integral_fintype (integrable_const 1)] at h
    simpa only [Fintype.sum_bool, measureReal_def, smul_eq_mul, mul_one, add_comm] using h
  rw [toReal_klDiv_fintype μ ν (fun b => by rw [hν b]; norm_num)]
  simp only [Fintype.sum_bool, hν, ENNReal.toReal_div, ENNReal.toReal_one,
    ENNReal.toReal_ofNat, mul_log_div_half]
  rw [show (μ {true}).toReal = 1 - (μ {false}).toReal by linarith]
  simp only [binEntropy, log_inv]
  ring

end LpSelfSimilar.Entropy
