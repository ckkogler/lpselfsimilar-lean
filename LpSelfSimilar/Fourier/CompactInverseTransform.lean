module

public import LpSelfSimilar.Fourier.AngularInverseFirstDerivative
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Normed.Group.Bounded

@[expose] public section

/-!
# Inverse Fourier identities for compactly supported smooth amplitudes

A single interval contains the topological support of an amplitude and those
of its derivatives. Enlarging the interval makes every boundary value zero.
The previously proved interval identities then give the exact first-derivative
multiplier and the inverse L1 estimate for any compactly supported C2 amplitude.
-/

open MeasureTheory Set

namespace LpSelfSimilar.Fourier

/-- One finite interval contains an amplitude and its first two derivatives. -/
theorem exists_pos_zero_derivatives_off_interval {f : ℝ → ℂ} (hf : HasCompactSupport f) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, x ≤ -R ∨ R ≤ x →
      f x = 0 ∧ deriv f x = 0 ∧ deriv (deriv f) x = 0 := by
  obtain ⟨R, hR, hbound⟩ := hf.isCompact.isBounded.exists_pos_norm_le
  refine ⟨R + 1, by linarith, ?_⟩
  intro x hx
  have habs : R + 1 ≤ |x| := by
    rcases hx with hx | hx
    · exact le_abs.mpr (Or.inr (by linarith))
    · exact le_abs.mpr (Or.inl hx)
  have hn : x ∉ tsupport f := by
    intro hmem
    have hb := hbound x hmem
    rw [Real.norm_eq_abs] at hb
    linarith
  exact ⟨image_eq_zero_of_notMem_tsupport hn, deriv_of_notMem_tsupport hn,
    deriv_of_notMem_tsupport (fun hx => hn (tsupport_deriv_subset hx))⟩

/-- The inverse of an actual compactly supported C1 derivative is exactly -i*x times the inverse. -/
theorem angularInverseFourier_deriv_of_compact_support {f : ℝ → ℂ}
    (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) (x : ℝ) :
    angularInverseFourier (deriv f) x = -Complex.I * (x : ℂ) * angularInverseFourier f x := by
  obtain ⟨R, hR, hz⟩ := exists_pos_zero_derivatives_off_interval hs
  have h := angularInverseFourier_firstDerivative_of_interval (a := -R) (b := R)
    (by linarith) hf.continuous.continuousOn
    (fun ξ hξ => (hf.differentiable (by norm_num) ξ).hasDerivAt)
    (hf.continuous_deriv_one.intervalIntegrable _ _)
    (fun ξ hξ => (hz ξ hξ).1) (fun ξ hξ => (hz ξ hξ).2.1) x
  exact h.trans (by ring)

/-- A compactly supported C2 amplitude has an integrable inverse, with the exact half-factor bound. -/
theorem angularInverseFourier_compact_C2_L1_bound {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    Integrable (angularInverseFourier f) ∧
      (∫ x, ‖angularInverseFourier f x‖) ≤
        (1 / 2 : ℝ) * ((∫ ξ, ‖f ξ‖) + ∫ ξ, ‖deriv (deriv f) ξ‖) := by
  obtain ⟨R, hR, hz⟩ := exists_pos_zero_derivatives_off_interval hs
  have hf' : ContDiff ℝ 1 (deriv f) := hf.deriv'
  exact angularInverseFourier_interval_L1_bound (a := -R) (b := R)
    (by linarith) hf.continuous.continuousOn hf'.continuous.continuousOn
    (fun ξ hξ => (hf.differentiable (by norm_num) ξ).hasDerivAt)
    (fun ξ hξ => (hf'.differentiable (by norm_num) ξ).hasDerivAt)
    (hf'.continuous_deriv_one.intervalIntegrable _ _)
    (fun ξ hξ => (hz ξ hξ).1) (fun ξ hξ => (hz ξ hξ).2.2)
    (hz (-R) (Or.inl le_rfl)).2.1 (hz R (Or.inr le_rfl)).2.1

end LpSelfSimilar.Fourier
