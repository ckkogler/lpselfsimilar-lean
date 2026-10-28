module

public import LpSelfSimilar.Bernoulli.ReservedTailDerivatives
public import LpSelfSimilar.Bernoulli.PackingParameters
public import LpSelfSimilar.Fourier.MeanProductDerivatives

@[expose] public section

/-!
# Combining the independent block product with its reserved tail

The block cost is `80*L*T/chi` and the tail cost is `16/chi`. Their sum is at
most `100*J*(T+1)/chi`, where `J=L/rho`. Averaged Leibniz bounds therefore give
the exact combined majorant used for localized Fourier inversion. The tail is
the actual normalized Bernoulli tail, with all moments already derived.
-/

open MeasureTheory
open scoped BigOperators
open LpSelfSimilar.Analysis LpSelfSimilar.Entropy

namespace LpSelfSimilar.Bernoulli

/-- The exact block and tail derivative costs fit the source's common majorant. -/
theorem packing_total_derivative_cost_le {χ ρ L : ℝ} (hχ : 0 < χ)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L) (T : ℕ) :
    80 * L * T / χ + 16 / χ ≤ 100 * (L / ρ) * ((T : ℝ) + 1) / χ := by
  have hL0 : 0 ≤ L := by linarith
  have hJ := three_le_separation_entropy_ratio hρ hρ1 hL
  have hLJ : L ≤ L / ρ := (le_div_iff₀ hρ).mpr
    (mul_le_of_le_one_right hL0 hρ1)
  have hm := mul_le_mul_of_nonneg_right hLJ (show 0 ≤ (T : ℝ) by positivity)
  have hjt := mul_nonneg (show 0 ≤ L / ρ by positivity) (show 0 ≤ (T : ℝ) by positivity)
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ hχ.le
  nlinarith

/-- An averaged block product times the actual reserved tail has the exact combined derivative bound. -/
theorem integral_norm_iteratedDeriv_mul_reserved_tail_le
    {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : PMF Ω) (f : Ω → ℝ → ℂ) {θ ρ L r : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hgap : -Real.log θ ≤ 1 / 250)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L) (hr : 0 < r) (hrχ : r ≤ -Real.log θ)
    (T : ℕ) (ξ : ℝ) (hξ : abs (|ξ| - 1) ≤ packingFrequencyWidth (L / ρ))
    (hf : ∀ a, ContDiffAt ℝ 2 (f a) ξ)
    (hb : ∀ j ≤ 2, (∫ a, ‖iteratedDeriv j (f a) ξ‖ ∂p.toMeasure) ≤
      (80 * L * T / (-Real.log θ)) ^ j *
        Real.exp (-(packingAttenuation (-Real.log θ) ρ L * T))) (k : ℕ) (hk : k ≤ 2) :
    (∫ a, ‖iteratedDeriv k (fun s ↦ f a s *
      charFun ((convolution θ).map (fun y ↦
        (θ ^ reservedTailStart θ (packingFrequencyWidth (L / ρ)) r / r) * y)) s) ξ‖
      ∂p.toMeasure) ≤
        (100 * (L / ρ) * ((T : ℝ) + 1) / (-Real.log θ)) ^ k *
          Real.exp (-1 / (2 * (-Real.log θ))) *
            Real.exp (-(packingAttenuation (-Real.log θ) ρ L * T)) := by
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  have hJ := three_le_separation_entropy_ratio hρ hρ1 hL
  have hL0 : 0 ≤ L := by linarith
  let a := θ ^ reservedTailStart θ (packingFrequencyWidth (L / ρ)) r / r
  let g := charFun ((convolution θ).map (fun y ↦ a * y))
  have hg : ContDiffAt ℝ 2 g ξ :=
    (contDiff_charFun (memLp_id_scaled_convolution hθ0.le hθ1 a 2)).contDiffAt
  have hgb (j : ℕ) (hj : j ≤ 2) : ‖iteratedDeriv j g ξ‖ ≤
      (16 / (-Real.log θ)) ^ j * Real.exp (-1 / (2 * (-Real.log θ))) :=
    norm_iteratedDeriv_charFun_reserved_tail_le hθ0 hθ1 hgap
      (packingFrequencyWidth_pos hJ).le (packingFrequencyWidth_lt hJ).le hr hrχ ξ hξ j hj
  have h := Fourier.integral_norm_iteratedDeriv_mul_le p f g
    (Real.exp_pos _).le (Real.exp_pos _).le
    (show 0 ≤ 80 * L * T / (-Real.log θ) by positivity)
    (show 0 ≤ 16 / (-Real.log θ) by positivity) 2 ξ hf hg hb hgb k hk
  have hcost := packing_total_derivative_cost_le hχ hρ hρ1 hL T
  calc
    _ ≤ (80 * L * T / (-Real.log θ) + 16 / (-Real.log θ)) ^ k *
        (Real.exp (-(packingAttenuation (-Real.log θ) ρ L * T)) *
          Real.exp (-1 / (2 * (-Real.log θ)))) := h
    _ ≤ (100 * (L / ρ) * ((T : ℝ) + 1) / (-Real.log θ)) ^ k *
        (Real.exp (-(packingAttenuation (-Real.log θ) ρ L * T)) *
          Real.exp (-1 / (2 * (-Real.log θ)))) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hcost k) (by positivity)
    _ = _ := by ring

end LpSelfSimilar.Bernoulli
