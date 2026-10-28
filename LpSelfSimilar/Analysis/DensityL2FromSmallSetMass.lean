module

public import LpSelfSimilar.Analysis.DensityGeometricTails
public import LpSelfSimilar.Analysis.GeometricMoments
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

/-!
# A sharp L2 conclusion from geometric small-set mass bounds

The density level ratio is beta*D, while its mass ratio is beta. The existing
geometric moment lemma, applied to the density under its own probability law,
therefore requires exactly beta^2*D<1. The weighted first moment is precisely
the Lebesgue second moment. This avoids an auxiliary logarithmic tail exponent.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LpSelfSimilar.Analysis

/-- Geometric small-set mass bounds with beta^2*D<1 imply L2 for the actual density. -/
theorem memLp_two_of_geometric_smallSetMass {X : Type*} [MeasurableSpace X]
    (μ σ : Measure X) [IsProbabilityMeasure σ] {f : X → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hσ : σ = μ.withDensity (fun x => ENNReal.ofReal (f x)))
    {R D β : ℝ} (hR : 0 < R) (hD : 0 < D) (hβ : 0 < β)
    (hA : 1 < β * D) (hratio : β ^ 2 * D < 1)
    (hmass : ∀ n : ℕ, smallSetMass σ μ (ENNReal.ofReal (R / D ^ n)) ≤ ENNReal.ofReal β ^ n) :
    MemLp f 2 μ := by
  let L := 1 / (β * R)
  let A := β * D
  let S := fun n : ℕ => {x | L * A ^ n ≤ f x}
  have hL : 0 < L := by dsimp only [L]; positivity
  have hS (n : ℕ) : MeasurableSet (S n) := measurableSet_le measurable_const hf
  have htail (n : ℕ) : σ (S n) ≤ ENNReal.ofReal β ^ n * σ Set.univ := by
    rw [measure_univ, mul_one]
    exact density_geometric_tails_of_smallSetMass μ σ hf hσ hR hD hβ hA hmass n
  have hratio' : β * A ^ (1 : ℝ) < 1 := by
    rw [Real.rpow_one]
    dsimp only [A]
    nlinarith [hratio]
  have hmoment : ∫⁻ x, ENNReal.ofReal (f x) ^ (1 : ℝ) ∂σ < ∞ :=
    lintegral_rpow_lt_top_of_geometric_tails σ f hL hA (by norm_num) hratio'
      S hS (fun _ _ hx => hx) htail
  have hfm := hf.ennreal_ofReal.aemeasurable (μ := μ)
  rw [hσ, lintegral_withDensity_eq_lintegral_mul₀ hfm (hfm.pow_const (1 : ℝ))] at hmoment
  simp only [ENNReal.rpow_one] at hmoment
  refine (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num) (by norm_num) hf.aestronglyMeasurable).2 ?_
  convert hmoment using 1
  apply lintegral_congr
  intro x
  rw [Real.enorm_of_nonneg (hf0 x)]
  norm_num [pow_two]

end LpSelfSimilar.Analysis
