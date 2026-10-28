module

public import LpSelfSimilar.Bernoulli.SmoothedGaussianEnergyIntegrability
public import LpSelfSimilar.Bernoulli.SmoothedLowFrequencyEnergy
public import LpSelfSimilar.Bernoulli.HighFrequencyEnergyMargin
public import LpSelfSimilar.Bernoulli.GaussianHighFrequencyMargin

@[expose] public section

/-!
# The explicit Gaussian approximation for the actual smoothed Bernoulli law

All energy components are integrable. The low-frequency error contributes
less than (7*chi/4)^2. On the complementary high-frequency region the
squared triangle inequality costs at most twice each individual energy;
the proved numerical tails make this cost smaller than (chi/50)^2.
Together with weighted Plancherel this gives the strict 9*chi/5 L1 bound.
The regions are used only to split integrals, so no indicator is differentiated.
-/

open MeasureTheory Set
open LpSelfSimilar.Fourier LpSelfSimilar.Gaussian LpSelfSimilar.Analysis LpSelfSimilar.Entropy

namespace LpSelfSimilar.Bernoulli

/-- The actual normalized packing smoothing is within 9*chi/5 of the standard Gaussian in L1. -/
theorem integral_abs_packing_smoothedGaussianError_lt {θ ρ L : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hgap : -Real.log θ ≤ 1 / 250)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L)
    (hsmall : (-Real.log θ) * packingLogScale (L / ρ) ^ 2 ≤ ρ / 2) :
    (∫ x : ℝ, |varianceNormalizedSmoothing θ (packingFrequencyWidth (L / ρ)) x - kernel 1 x|) <
      (9 / 5 : ℝ) * (-Real.log θ) := by
  let ε := packingFrequencyWidth (L / ρ)
  let F := angularFourier (fun x => (varianceNormalizedSmoothing θ ε x : ℂ))
  let e : ℝ → ℝ := fun u => ‖F u - standardGaussianAmplitude u‖ ^ 2 +
    ‖deriv F u - deriv standardGaussianAmplitude u‖ ^ 2
  let lo : Set ℝ := {u | |Real.sqrt (1 - θ ^ 2) * u| ≤ 1}
  let hi : Set ℝ := {u | 1 < |Real.sqrt (1 - θ ^ 2) * u|}
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  have hε : 0 < ε := packingFrequencyWidth_pos (three_le_separation_entropy_ratio hρ hρ1 hL)
  have hlo : MeasurableSet lo := measurableSet_le (by fun_prop) measurable_const
  have hhi : MeasurableSet hi := measurableSet_lt measurable_const (by fun_prop)
  have hec : loᶜ = hi := by ext u; simp only [lo, hi, mem_compl_iff, mem_setOf_eq, not_le]
  have hiE := integrable_smoothedGaussian_fourier_energy_components hθ0 hθ1 hε
  have hie : Integrable e := hiE.2.2.1.add hiE.2.2.2
  have hif : Integrable (fun u => ‖F u‖ ^ 2 + ‖deriv F u‖ ^ 2) := hiE.1.add hiE.2.1
  have hed (u : ℝ) : deriv F u - deriv standardGaussianAmplitude u =
      deriv F u + ((u * Real.exp (-(u ^ 2) / 2) : ℝ) : ℂ) := by
    rw [(hasDerivAt_standardGaussianAmplitude u).deriv]
    simp only [neg_mul, sub_neg_eq_add, standardGaussianAmplitude, Complex.ofReal_mul]
  have hb : (∫ x : ℝ, |varianceNormalizedSmoothing θ ε x - kernel 1 x|) ^ 2 ≤
      (1 / 2 : ℝ) * ∫ u : ℝ, e u := by
    rw [show (∫ u : ℝ, e u) =
        (∫ u : ℝ, ‖F u - standardGaussianAmplitude u‖ ^ 2) +
          ∫ u : ℝ, ‖deriv F u - deriv standardGaussianAmplitude u‖ ^ 2 from
      integral_add hiE.2.2.1 hiE.2.2.2]
    simp_rw [hed]
    exact smoothedGaussian_weighted_L1_bound hθ0 hθ1 hε
  have hh := half_integral_pair_difference_le hhi hie hif integrable_standardGaussian_fourier_energy
  have hsplit : (∫ u : ℝ in lo, e u) + (∫ u : ℝ in hi, e u) = ∫ u : ℝ, e u := by
    simpa only [hec] using integral_add_compl hlo hie
  have hlow : Real.sqrt ((1 / 2 : ℝ) * ∫ u : ℝ in lo, e u) <
      (7 / 4 : ℝ) * (-Real.log θ) := by
    dsimp only [e]
    simp_rw [hed]
    exact sqrt_half_integral_lowFrequency_packing_smoothing_error_lt hθ0 hθ1 hgap hρ hρ1 hL
  have hfsmall : Real.sqrt ((1 / 2 : ℝ) * ∫ u : ℝ in hi, ‖F u‖ ^ 2 + ‖deriv F u‖ ^ 2) <
      (-Real.log θ) / 100 := by
    have h := sqrt_highFrequency_packing_smoothing_energy_lt hθ0 hθ1 hgap hρ hρ1 hL hsmall
    exact h.trans_le (by norm_num; nlinarith)
  have hgsmall : Real.sqrt ((1 / 2 : ℝ) * ∫ u : ℝ in hi,
      ‖standardGaussianAmplitude u‖ ^ 2 + ‖deriv standardGaussianAmplitude u‖ ^ 2) <
      (-Real.log θ) / 100 := by
    have h := sqrt_highFrequency_standardGaussian_energy_lt hθ0 hθ1 hgap
    exact h.trans_le (by norm_num; nlinarith)
  apply lt_nine_fifths_of_energy_bounds hχ (L := (1 / 2 : ℝ) * ∫ u : ℝ in lo, e u)
    (F := (1 / 2 : ℝ) * ∫ u : ℝ in hi, ‖F u‖ ^ 2 + ‖deriv F u‖ ^ 2)
    (G := (1 / 2 : ℝ) * ∫ u : ℝ in hi,
      ‖standardGaussianAmplitude u‖ ^ 2 + ‖deriv standardGaussianAmplitude u‖ ^ 2)
    ?_ hlow hfsmall hgsmall
  change (∫ x : ℝ, |varianceNormalizedSmoothing θ ε x - kernel 1 x|) ^ 2 ≤ _
  change (1 / 2 : ℝ) * (∫ u : ℝ in hi, e u) ≤ _ at hh
  nlinarith

end LpSelfSimilar.Bernoulli
