module

public import LpSelfSimilar.Analysis.SmallSetMass
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

/-!
A quantitative mass modulus from an L1 approximation by a bounded density.
This reusable measure-theoretic estimate supplies the explicit epsilon in the
weak reverse Hölder criterion, without a compact-support assumption.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LpSelfSimilar

lemma measure_le_of_bounded_density_approximation {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} {f f₀ : X → ℝ} (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x)
    (hrep : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (f x))) (hf₀ : Integrable f₀ μ)
    {C η t : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, f₀ x ≤ C)
    (herr : (∫ x, |f x - f₀ x| ∂μ) ≤ η) {E : Set X} (hE : MeasurableSet E)
    (hvol : μ E ≤ ENNReal.ofReal t) (ht : 0 ≤ t) :
    ν E ≤ ENNReal.ofReal (η + C * t) := by
  have hfinite : μ E < ⊤ := hvol.trans_lt ENNReal.ofReal_lt_top
  letI : IsFiniteMeasure (μ.restrict E) := ⟨by simpa using hfinite⟩
  have hvolreal : μ.real E ≤ t := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_lt_top.ne hvol
    simpa only [measureReal_def, ENNReal.toReal_ofReal ht] using h
  have hdiff : Integrable (fun x ↦ |f x - f₀ x|) μ := (hf.sub hf₀).abs
  have h₁ : (∫ x in E, f x ∂μ) ≤
      (∫ x in E, |f x - f₀ x| ∂μ) + ∫ x in E, f₀ x ∂μ := by
    rw [← integral_add hdiff.integrableOn hf₀.integrableOn]
    exact integral_mono hf.integrableOn (hdiff.integrableOn.add hf₀.integrableOn)
      (fun x ↦ by linarith [le_abs_self (f x - f₀ x)])
  have h₂ : (∫ x in E, |f x - f₀ x| ∂μ) ≤ η :=
    (setIntegral_le_integral hdiff (ae_of_all _ (fun x ↦ abs_nonneg _))).trans herr
  have h₃ : (∫ x in E, f₀ x ∂μ) ≤ C * t := by
    have h := integral_mono hf₀.integrableOn (integrable_const (μ := μ.restrict E) C) hbound
    simp only [integral_const, Measure.restrict_apply_univ, measureReal_def,
      smul_eq_mul] at h
    exact h.trans (by
      have hh := mul_le_mul_of_nonneg_left hvolreal hC
      simpa only [measureReal_def, mul_comm] using hh)
  have hi : (∫ x in E, f x ∂μ) ≤ η + C * t := by linarith
  rw [hrep, withDensity_apply _ hE,
    ← ofReal_integral_eq_lintegral_ofReal hf.integrableOn (ae_of_all _ hf0)]
  exact ENNReal.ofReal_le_ofReal hi

lemma smallSetMass_le_of_bounded_density_approximation {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} {f f₀ : X → ℝ} (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x)
    (hrep : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (f x))) (hf₀ : Integrable f₀ μ)
    {C η t : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, f₀ x ≤ C)
    (herr : (∫ x, |f x - f₀ x| ∂μ) ≤ η) (ht : 0 ≤ t) :
    smallSetMass ν μ (ENNReal.ofReal t) ≤ ENNReal.ofReal (η + C * t) :=
  smallSetMass_le ν μ (fun _ hE hvol ↦
    measure_le_of_bounded_density_approximation hf hf0 hrep hf₀ hC hbound herr hE hvol ht)

end LpSelfSimilar
