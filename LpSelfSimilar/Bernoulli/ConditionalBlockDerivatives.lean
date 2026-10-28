module

public import LpSelfSimilar.Probability.MapProbability

public import LpSelfSimilar.Bernoulli.PackingAttenuationRange
public import LpSelfSimilar.Fourier.ConditionalDerivativeMajorants
public import LpSelfSimilar.Fourier.AffineCharacteristicNorm

@[expose] public section

/-!
# Exact averaged derivative bounds for normalized conditional blocks

Each original conditional block is translated and divided by the common scale.
The support then lies in `[0,52]`. The translation may depend on the label, but
its characteristic norm is the original norm at the rescaled frequency. Original
label probabilities therefore supply the mean attenuation, and the proved cap
`1-sqrt(7/16)` gives derivative cost less than eighty.
-/

open MeasureTheory Set
open scoped BigOperators

namespace LpSelfSimilar.Bernoulli

/-- Actual normalized conditional blocks retain their exponential mean attenuation through order two. -/
theorem integral_norm_iteratedDeriv_normalized_conditionals_le
    {m : ℕ} {Ω : Fin m → Type*} [∀ i, Fintype (Ω i)]
    [∀ i, MeasurableSpace (Ω i)] [∀ i, MeasurableSingletonClass (Ω i)]
    (p : (i : Fin m) → PMF (Ω i)) (μ : (i : Fin m) → Ω i → Measure ℝ)
    [∀ i a, IsProbabilityMeasure (μ i a)] (b : Fin m → ℝ)
    (c : (i : Fin m) → Ω i → ℝ) (r : ℝ)
    (hb0 : ∀ i, 0 ≤ b i) (hbcap : ∀ i, b i ≤ 1 - Real.sqrt (7 / 16))
    (hs : ∀ i a, ((μ i a).map (fun y ↦ (y - c i a) / r)) (Icc 0 52) = 1)
    (x : ℝ) (hb : ∀ i, (∫ a, ‖charFun (μ i a) (x / r)‖ ∂(p i).toMeasure) ≤ 1 - b i)
    (k : ℕ) (hk : k ≤ 2) :
    (∫ ω, ‖iteratedDeriv k
      (charFun (finiteConvolution (fun i ↦ (μ i (ω i)).map
        (fun y ↦ (y - c i (ω i)) / r)))) x‖ ∂(productPMF p).toMeasure) ≤
      (80 * (m : ℝ)) ^ k * Real.exp (-∑ i, b i) := by
  let μ' := fun i a ↦ (μ i a).map (fun y ↦ (y - c i a) / r)
  haveI : ∀ i a, IsProbabilityMeasure (μ' i a) :=
    fun i a ↦ LpSelfSimilar.Probability.isProbabilityMeasure_map (by fun_prop)
  have hden (i : Fin m) : 0 < 1 - b i := by
    have hp : 0 < Real.sqrt (7 / 16 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
    linarith [hbcap i]
  apply Fourier.integral_norm_iteratedDeriv_charFun_product_le_exp p μ' b
    (D := 52) (C := 80) (by norm_num) (by norm_num) hb0
    (fun i ↦ by linarith [hden i]) _ _ x _ k hk
  · intro i
    exact ((div_lt_iff₀ (hden i)).mp (derivative_cost_lt_eighty (hbcap i))).le
  · intro i a
    exact Fourier.ae_abs_le_of_mass_Icc_eq_one (μ' i a) (hs i a)
  · intro i
    have he : (fun a ↦ ‖charFun (μ' i a) x‖) = fun a ↦ ‖charFun (μ i a) (x / r)‖ := by
      funext a
      exact Fourier.norm_charFun_map_sub_div (μ i a) (c i a) r x
    rw [he]
    exact hb i

end LpSelfSimilar.Bernoulli
