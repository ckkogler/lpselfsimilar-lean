module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-!
# Characteristic functions under almost-sure approximation

The complex phase has norm one, so dominated convergence applies to actual
pushforward laws of almost-surely convergent real random variables. This supplies
finite-prefix limits without assuming convergence in total variation or a density.
-/

open MeasureTheory Filter
open scoped Topology

namespace LpSelfSimilar.Fourier

/-- Almost-sure approximation on a probability space gives pointwise characteristic convergence. -/
theorem tendsto_charFun_map_of_ae_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, Measurable (X n)) (hY : Measurable Y)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ X n ω) atTop (𝓝 (Y ω))) (s : ℝ) :
    Tendsto (fun n ↦ charFun (P.map (X n)) s) atTop (𝓝 (charFun (P.map Y) s)) := by
  have he (Z : Ω → ℝ) (hZ : Measurable Z) :
      charFun (P.map Z) s = ∫ ω, Complex.exp ((s * Z ω : ℝ) * Complex.I) ∂P := by
    rw [charFun_apply_real, integral_map hZ.aemeasurable (by fun_prop)]
    simp only [Function.comp_apply, Complex.ofReal_mul]
  simp_rw [he _ hY, he _ (hX _)]
  apply tendsto_integral_of_dominated_convergence (fun _ ↦ (1 : ℝ))
  · intro n
    fun_prop
  · exact integrable_const _
  · intro n
    exact ae_of_all _ (fun ω ↦ by rw [Complex.norm_exp_ofReal_mul_I])
  · have hc : Continuous (fun x : ℝ ↦ Complex.exp ((s * x : ℝ) * Complex.I)) := by fun_prop
    filter_upwards [hlim] with ω hω
    exact hc.continuousAt.tendsto.comp hω

end LpSelfSimilar.Fourier
