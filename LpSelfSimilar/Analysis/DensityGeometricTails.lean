module

public import LpSelfSimilar.Analysis.SmallSetMassIteration
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Density tails from geometric small-set mass bounds

Let sigma=f*mu be a probability measure, and suppose sets of volume R/D^n
have sigma-mass at most beta^n. The density superlevel sets at heights
(1/(beta*R))*(beta*D)^n then have mass at most beta^n. The induction uses
the preceding level's mass to bound the next level's reference volume.
The resulting height ratio beta*D is the extra gain needed for sharp L2.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LpSelfSimilar.Analysis

/-- A density's integral over a containing set bounds the volume of a high-density subset. -/
theorem density_level_volume_mul_le_mass {X : Type*} [MeasurableSpace X]
    (μ σ : Measure X) {f : X → ℝ} (hσ : σ = μ.withDensity (fun x => ENNReal.ofReal (f x)))
    {S T : Set X} (hS : MeasurableSet S) (hT : MeasurableSet T) (hST : S ⊆ T)
    (u : ℝ) (hu : ∀ x ∈ S, u ≤ f x) : ENNReal.ofReal u * μ S ≤ σ T := by
  rw [hσ, withDensity_apply _ hT]
  calc
    _ = ∫⁻ _x in S, ENNReal.ofReal u ∂μ := by simp
    _ ≤ ∫⁻ x in S, ENNReal.ofReal (f x) ∂μ :=
      setLIntegral_mono' hS (fun x hx => ENNReal.ofReal_le_ofReal (hu x hx))
    _ ≤ _ := lintegral_mono_set hST

/-- Geometric small-set bounds yield geometric tails of the actual density under its own measure. -/
theorem density_geometric_tails_of_smallSetMass {X : Type*} [MeasurableSpace X]
    (μ σ : Measure X) [IsProbabilityMeasure σ] {f : X → ℝ} (hf : Measurable f)
    (hσ : σ = μ.withDensity (fun x => ENNReal.ofReal (f x)))
    {R D β : ℝ} (hR : 0 < R) (hD : 0 < D) (hβ : 0 < β) (hA : 1 < β * D)
    (hmass : ∀ n : ℕ, smallSetMass σ μ (ENNReal.ofReal (R / D ^ n)) ≤ ENNReal.ofReal β ^ n)
    (n : ℕ) :
    σ {x | (1 / (β * R)) * (β * D) ^ n ≤ f x} ≤ ENNReal.ofReal β ^ n := by
  let L := 1 / (β * R)
  let A := β * D
  let S := fun n : ℕ => {x | L * A ^ n ≤ f x}
  have hL : 0 < L := by dsimp only [L]; positivity
  have hA0 : 0 < A := zero_lt_one.trans hA
  have hS (n : ℕ) : MeasurableSet (S n) := measurableSet_le measurable_const hf
  change σ (S n) ≤ _
  induction n with
  | zero =>
    rw [pow_zero]
    exact (measure_mono (subset_univ _)).trans_eq measure_univ
  | succ n ih =>
    have hsub : S (n + 1) ⊆ S n := by
      intro x hx
      change L * A ^ n ≤ f x
      apply le_trans _ hx
      rw [pow_succ]
      have hp : 0 ≤ L * A ^ n := by positivity
      nlinarith
    have hlower : ENNReal.ofReal (L * A ^ (n + 1)) * μ (S (n + 1)) ≤ ENNReal.ofReal β ^ n :=
      (density_level_volume_mul_le_mass μ σ hσ (hS _) (hS _) hsub _ (fun _ hx => hx)).trans ih
    have heq : L * A ^ (n + 1) * (R / D ^ (n + 1)) = β ^ n := by
      dsimp only [L, A]
      rw [mul_pow, pow_succ β]
      field_simp [hβ.ne', hR.ne', hD.ne']
    have hvol : μ (S (n + 1)) ≤ ENNReal.ofReal (R / D ^ (n + 1)) := by
      apply (ENNReal.mul_le_mul_iff_right
        (ENNReal.ofReal_pos.mpr (mul_pos hL (pow_pos hA0 _))).ne' ENNReal.ofReal_ne_top).mp
      calc
        _ ≤ ENNReal.ofReal β ^ n := hlower
        _ = ENNReal.ofReal (L * A ^ (n + 1)) * ENNReal.ofReal (R / D ^ (n + 1)) := by
          rw [← ENNReal.ofReal_pow hβ.le, ← ENNReal.ofReal_mul (by positivity), heq]
    exact (measure_le_smallSetMass σ μ (hS _) hvol).trans (hmass (n + 1))

end LpSelfSimilar.Analysis
