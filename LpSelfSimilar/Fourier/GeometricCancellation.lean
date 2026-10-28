module

public import LpSelfSimilar.Fourier.FinitePhaseCancellation
public import LpSelfSimilar.Analysis.GeometricPhaseAverage

@[expose] public section

/-!
# Geometric cancellation of finite distance-band laws

The geometric phase estimate is even in the phase difference. Applying it to
the absolute difference gives the exact Fourier attenuation of a finite law whose
nonzero atoms lie in one distance band. No bound on the number of labels is needed
here; the sixteen-atom bound enters the entropy estimate elsewhere.
-/

open scoped BigOperators
open LpSelfSimilar.Analysis

namespace LpSelfSimilar.Fourier

/-- The geometric phase bound in angular-frequency units, allowing negative differences. -/
theorem geometric_phase_deficit_ge_of_abs {θ x : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hgap : -Real.log θ ≤ 1 / 70)
    (hx0 : Real.pi ≤ |x|) (hx1 : |x| ≤ 16 * Real.pi / θ) :
    (3 / 5 : ℝ) ≤ ∑ k : Fin (geometricPhaseLength θ + 1),
      geometricWeight θ (geometricPhaseLength θ) k *
        (1 - Real.cos (x * θ ^ (k : ℕ))) := by
  have hden : 0 < 2 * Real.pi := by positivity
  have hy0 : (1 / 2 : ℝ) ≤ |x| / (2 * Real.pi) := by
    apply (le_div_iff₀ hden).mpr
    linarith
  have hy1 : |x| / (2 * Real.pi) ≤ 8 / θ := by
    apply (div_le_iff₀ hden).mpr
    calc
      |x| ≤ 16 * Real.pi / θ := hx1
      _ = 8 / θ * (2 * Real.pi) := by ring
  have h := geometric_phase_average_ge_of_log_gap hθ0 hθ1 hgap hy0 hy1
  convert h using 1
  apply Finset.sum_congr rfl
  intro k hk
  congr 2
  rw [show 2 * Real.pi * (|x| / (2 * Real.pi)) = |x| by field_simp]
  rw [← Real.cos_abs (x * θ ^ (k : ℕ)), abs_mul,
    abs_of_nonneg (pow_nonneg hθ0.le _)]

/-- A finite law in a distance band has the exact averaged Fourier cancellation. -/
theorem geometric_norm_finiteTransform_le_of_band {ι : Type*} [Fintype ι]
    (p z : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    {θ a s₀ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hgap : -Real.log θ ≤ 1 / 70)
    (hs : 0 < s₀) (hbase0 : Real.pi ≤ s₀ * a) (hbase1 : s₀ * a ≤ Real.pi / θ)
    (hband : ∀ i j, i ≠ j → p i ≠ 0 → p j ≠ 0 →
      a ≤ |z i - z j| ∧ |z i - z j| < 16 * a) :
    (∑ k : Fin (geometricPhaseLength θ + 1),
      geometricWeight θ (geometricPhaseLength θ) k *
        ‖finiteTransform p z (s₀ * θ ^ (k : ℕ))‖) ≤
      1 - Entropy.finiteCancellation Finset.univ p := by
  apply weighted_norm_finiteTransform_le_one_sub_cancellation p z
    (geometricWeight θ (geometricPhaseLength θ))
    (fun k ↦ s₀ * θ ^ (k : ℕ)) hp hpsum
    (geometricWeight_nonneg hθ0.le hθ1.le _)
    (sum_geometricWeight_eq_one θ _) 
  intro i j hij hi hj
  have hd := hband i j hij hi hj
  have hx0 : Real.pi ≤ |s₀ * (z i - z j)| := by
    rw [abs_mul, abs_of_nonneg hs.le]
    exact hbase0.trans (mul_le_mul_of_nonneg_left hd.1 hs.le)
  have hx1 : |s₀ * (z i - z j)| ≤ 16 * Real.pi / θ := by
    rw [abs_mul, abs_of_nonneg hs.le]
    calc
      s₀ * |z i - z j| ≤ s₀ * (16 * a) :=
        mul_le_mul_of_nonneg_left hd.2.le hs.le
      _ = 16 * (s₀ * a) := by ring
      _ ≤ 16 * (Real.pi / θ) := by linarith
      _ = 16 * Real.pi / θ := by ring
  have h := geometric_phase_deficit_ge_of_abs hθ0 hθ1 hgap hx0 hx1
  convert h using 1
  apply Finset.sum_congr rfl
  intro k hk
  congr 2
  ring

end LpSelfSimilar.Fourier
