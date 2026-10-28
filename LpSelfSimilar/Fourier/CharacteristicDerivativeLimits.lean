module

public import LpSelfSimilar.Fourier.CharacteristicLimits
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

@[expose] public section

/-!
# Derivative convergence for bounded random variables

A common almost-sure support bound supplies every moment. The integral formula
for characteristic derivatives and dominated convergence then identify the
limits of derivatives of actual pushforward laws. No interchange of formal
infinite products and derivatives is assumed.
-/

open MeasureTheory Filter
open scoped Topology ENNReal

namespace LpSelfSimilar.Fourier

/-- A derived almost-sure bound gives every moment of the actual pushforward law. -/
theorem memLp_id_map_of_ae_abs_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {Z : Ω → ℝ} {S : ℝ}
    (hZ : Measurable Z) (hb : ∀ᵐ ω ∂P, |Z ω| ≤ S) (p : ℝ≥0∞) :
    MemLp id p (P.map Z) := by
  apply MemLp.of_bound (by fun_prop) S
  change ∀ᵐ x ∂P.map Z, |x| ≤ S
  rw [ae_map_iff hZ.aemeasurable
    (isClosed_le continuous_abs continuous_const).measurableSet]
  exact hb

/-- All characteristic derivatives pass through uniformly bounded almost-sure approximation. -/
theorem tendsto_iteratedDeriv_charFun_map_of_ae_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {X : ℕ → Ω → ℝ} {Y : Ω → ℝ} {S : ℝ}
    (hX : ∀ n, Measurable (X n)) (hY : Measurable Y)
    (hXb : ∀ n, ∀ᵐ ω ∂P, |X n ω| ≤ S) (hYb : ∀ᵐ ω ∂P, |Y ω| ≤ S)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ X n ω) atTop (𝓝 (Y ω)))
    (k : ℕ) (s : ℝ) :
    Tendsto (fun n ↦ iteratedDeriv k (charFun (P.map (X n))) s) atTop
      (𝓝 (iteratedDeriv k (charFun (P.map Y)) s)) := by
  have he (Z : Ω → ℝ) (hZ : Measurable Z) (hb : ∀ᵐ ω ∂P, |Z ω| ≤ S) :
      iteratedDeriv k (charFun (P.map Z)) s =
        Complex.I ^ k * ∫ ω, (Z ω : ℂ) ^ k *
          Complex.exp ((s * Z ω : ℝ) * Complex.I) ∂P := by
    rw [iteratedDeriv_charFun (memLp_id_map_of_ae_abs_le P hZ hb k),
      integral_map hZ.aemeasurable (by fun_prop)]
    simp only [Complex.ofReal_mul]
  simp_rw [he _ hY hYb, he _ (hX _) (hXb _)]
  apply Tendsto.mul tendsto_const_nhds
  apply tendsto_integral_of_dominated_convergence (fun _ ↦ S ^ k)
  · intro n
    fun_prop
  · exact integrable_const _
  · intro n
    filter_upwards [hXb n] with ω hω
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    exact pow_le_pow_left₀ (abs_nonneg _) hω k
  · have hc : Continuous (fun x : ℝ ↦ (x : ℂ) ^ k *
        Complex.exp ((s * x : ℝ) * Complex.I)) := by fun_prop
    filter_upwards [hlim] with ω hω
    exact hc.continuousAt.tendsto.comp hω

end LpSelfSimilar.Fourier
