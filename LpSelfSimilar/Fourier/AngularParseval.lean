module

public import LpSelfSimilar.Fourier.AngularFourierInversion
public import LpSelfSimilar.Fourier.AngularInverseReality
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
# Parseval for integrable angular Fourier pairs

An integrable product majorant justifies the conjugate-pairing Fubini identity.
Applying exact Fourier inversion then proves the quadratic norm identity with
coefficient 1/(2*pi). All transforms here are the actual ordinary integrals.
-/

open MeasureTheory
open scoped ComplexConjugate

namespace LpSelfSimilar.Fourier

/-- Fubini's pairing identity for the actual forward and inverse angular integrals. -/
theorem integral_conj_mul_angularInverseFourier {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) :
    (∫ x, conj (f x) * angularInverseFourier g x) =
      (2 * Real.pi)⁻¹ • ∫ ξ, conj (angularFourier f ξ) * g ξ := by
  have hfc : Integrable (fun x => conj (f x)) := hf.norm.mono'
    (Complex.continuous_conj.comp_aestronglyMeasurable hf.aestronglyMeasurable)
    (ae_of_all _ (fun x => by simp))
  have hj0 : Integrable (fun p : ℝ × ℝ =>
      angularFourierPhase p.1 p.2 * (conj (f p.1) * g p.2)) :=
    (hfc.mul_prod hg).bdd_mul continuous_angularFourierPhase.aestronglyMeasurable
      (ae_of_all _ (fun p => (norm_angularFourierPhase p.1 p.2).le))
  have hj : Integrable (fun p : ℝ × ℝ =>
      conj (f p.1) * (angularFourierPhase p.1 p.2 * g p.2)) :=
    hj0.congr (ae_of_all _ (fun p => by dsimp only; ring))
  unfold angularInverseFourier
  simp_rw [mul_smul_comm, ← integral_const_mul]
  rw [integral_smul, integral_integral_swap
    (f := fun x ξ => conj (f x) * (angularFourierPhase x ξ * g ξ)) hj]
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro ξ
  have hp (x : ℝ) : conj (f x) * (angularFourierPhase x ξ * g ξ) =
      conj (angularFourierPhase (-ξ) x * f x) * g ξ := by
    rw [map_mul, conj_angularFourierPhase, neg_neg]
    have hs : angularFourierPhase ξ x = angularFourierPhase x ξ := by
      unfold angularFourierPhase
      rw [mul_comm ξ x]
    rw [hs]
    ring
  simp_rw [hp]
  rw [integral_mul_const, integral_conj]
  rfl

/-- Parseval's identity for an integrable continuous amplitude with integrable inverse. -/
theorem integral_sq_norm_angularInverseFourier {f : ℝ → ℂ}
    (hc : Continuous f) (hf : Integrable f) (hi : Integrable (angularInverseFourier f)) :
    (∫ x, ‖angularInverseFourier f x‖ ^ 2) =
      (2 * Real.pi)⁻¹ * ∫ ξ, ‖f ξ‖ ^ 2 := by
  have hh := integral_conj_mul_angularInverseFourier hi hf
  simp_rw [angularFourier_angularInverseFourier hc hf hi] at hh
  have hn (z : ℂ) : conj z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj']
    push_cast
    rfl
  simp_rw [hn] at hh
  rw [integral_complex_ofReal, integral_complex_ofReal] at hh
  have hr := congrArg Complex.re hh
  simpa using hr

/-- An integrable inverse of an L1 amplitude is square integrable by its uniform bound. -/
theorem integrable_sq_norm_angularInverseFourier {f : ℝ → ℂ}
    (hf : Integrable f) (hi : Integrable (angularInverseFourier f)) :
    Integrable (fun x => ‖angularInverseFourier f x‖ ^ 2) := by
  have hb : ∀ᵐ x, ‖‖angularInverseFourier f x‖‖ ≤
      (2 * Real.pi)⁻¹ * ∫ ξ, ‖f ξ‖ := ae_of_all _ (fun x => by
    rw [norm_norm]
    exact norm_angularInverseFourier_le f x)
  simpa only [sq] using hi.norm.bdd_mul
    (continuous_angularInverseFourier hf).norm.aestronglyMeasurable hb

end LpSelfSimilar.Fourier
