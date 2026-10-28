module

public import LpSelfSimilar.Bernoulli.ScaledDigits
public import LpSelfSimilar.Bernoulli.PrefixTail
public import LpSelfSimilar.Fourier.IndependentProducts
public import LpSelfSimilar.Fourier.CharacteristicLimits

@[expose] public section

/-!
# Cosine products for the actual Bernoulli law

A scaled fair sign has characteristic function `cos(s*a)`. Independence gives
the finite product for an actual digit prefix, and dominated convergence of the
fair-sign series identifies the limit with the actual Bernoulli characteristic
function. No Fourier product or limiting measure is assumed in these statements.
-/

open MeasureTheory Filter
open scoped BigOperators Topology

namespace LpSelfSimilar.Bernoulli

/-- The characteristic function of an actual scaled fair sign is the corresponding cosine. -/
theorem charFun_signLaw (a s : ℝ) : charFun (signLaw a) s = (Real.cos (s * a) : ℂ) := by
  rw [charFun_apply_real, signLaw, integral_map (by fun_prop) (by fun_prop),
    fairDigit, ProbabilityTheory.integral_bernoulliMeasure]
  norm_num [sign, Complex.real_smul, Complex.exp_mul_I]
  rw [show -((s : ℂ) * (a : ℂ) * Complex.I) = (-((s : ℂ) * (a : ℂ))) * Complex.I by ring,
    Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  ring

/-- Independence identifies the actual scaled-prefix characteristic function with its cosine product. -/
theorem charFun_scaled_prefix (a θ s : ℝ) (n : ℕ) :
    charFun (digitSpace.map (fun w ↦ a * digitSum θ (fun j : Fin n ↦ w j))) s =
      ((∏ j : Fin n, Real.cos (s * (a * θ ^ (j : ℕ)))) : ℝ) := by
  rw [scaled_prefix_law, Fourier.charFun_finiteConvolution]
  simp only [charFun_signLaw, Complex.ofReal_prod]

/-- Finite cosine products converge to the characteristic function of the actual infinite sign series. -/
theorem tendsto_cosine_products {θ : ℝ} (hθ : |θ| < 1) (s : ℝ) :
    Tendsto (fun n : ℕ ↦ (((∏ j : Fin n, Real.cos (s * θ ^ (j : ℕ))) : ℝ) : ℂ))
      atTop (𝓝 (charFun (convolution θ) s)) := by
  have he (n : ℕ) :
      charFun (digitSpace.map (fun w ↦ digitSum θ (fun j : Fin n ↦ w j))) s =
        ((∏ j : Fin n, Real.cos (s * θ ^ (j : ℕ))) : ℝ) := by
    simpa only [one_mul] using charFun_scaled_prefix 1 θ s n
  have ht := Fourier.tendsto_charFun_map_of_ae_tendsto digitSpace
    (fun n ↦ show Measurable (fun w ↦ digitSum θ (fun j : Fin n ↦ w j)) from by
      unfold digitSum
      fun_prop)
    (measurable_series θ) (ae_of_all _ (fun w ↦ tendsto_digitSum hθ w)) s
  exact Filter.Tendsto.congr' (Eventually.of_forall he) ht

end LpSelfSimilar.Bernoulli
