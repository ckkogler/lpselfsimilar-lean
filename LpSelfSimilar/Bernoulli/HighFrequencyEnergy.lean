module

public import LpSelfSimilar.Bernoulli.HighFrequencyGaussianBounds
public import LpSelfSimilar.Bernoulli.GaussianCutoffEnergy
public import LpSelfSimilar.Bernoulli.SmoothedFourierRegularity
public import LpSelfSimilar.Analysis.CutoffProductEnergy

@[expose] public section

/-!
# The integrated high-frequency energy of the actual smoothed transform

The actual transform is the cutoff times the normalized Bernoulli
characteristic function. Its actual derivative is identified before taking
squares. The proved pointwise tail bounds and the two whole-line cutoff
energies give the precise expression under the square root in (B.3).
Integrability is derived from the majorant, and no sharp cutoff is differentiated.
-/

open MeasureTheory Set
open LpSelfSimilar.Analysis LpSelfSimilar.Fourier

namespace LpSelfSimilar.Bernoulli

/-- The actual high-frequency energy is integrable and has the exact pre-numerical bound. -/
theorem highFrequency_smoothed_fourier_energy_bound {θ ε : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hgap : -Real.log θ ≤ 1 / 250)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    IntegrableOn (fun u =>
      ‖angularFourier (fun x => (varianceNormalizedSmoothing θ ε x : ℂ)) u‖ ^ 2 +
      ‖deriv (angularFourier (fun x => (varianceNormalizedSmoothing θ ε x : ℂ))) u‖ ^ 2)
      {u : ℝ | 1 < |Real.sqrt (1 - θ ^ 2) * u|} ∧
    (1 / 2 : ℝ) * (∫ u : ℝ in {u : ℝ | 1 < |Real.sqrt (1 - θ ^ 2) * u|},
      ‖angularFourier (fun x => (varianceNormalizedSmoothing θ ε x : ℂ)) u‖ ^ 2 +
      ‖deriv (angularFourier (fun x => (varianceNormalizedSmoothing θ ε x : ℂ))) u‖ ^ 2) ≤
      Real.exp (-1 / (4 * (-Real.log θ))) ^ 2 *
        ((2 / ((-Real.log θ) * Real.sqrt (-Real.log θ))) * (1 + 18 / (-Real.log θ)) +
          6 * (-Real.log θ) * Real.sqrt (-Real.log θ) / ε) := by
  let q : ℝ → ℝ := fun u => quinticFourierCutoff ε
    (((-Real.log θ) * Real.sqrt (1 - θ ^ 2)) * u)
  let P : ℝ → ℂ := charFun ((convolution θ).map (fun x => Real.sqrt (1 - θ ^ 2) * x))
  let F : ℝ → ℂ := angularFourier (fun x => (varianceNormalizedSmoothing θ ε x : ℂ))
  let H : Set ℝ := {u | 1 < |Real.sqrt (1 - θ ^ 2) * u|}
  let E : ℝ := Real.exp (-1 / (4 * (-Real.log θ)))
  let C : ℝ := 3 / Real.sqrt (-Real.log θ)
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  have hr : 0 < (-Real.log θ) * Real.sqrt (1 - θ ^ 2) :=
    mul_pos hχ (Real.sqrt_pos.mpr (variance_scale_pos hθ0.le hθ1))
  have hq : ContDiff ℝ 1 q := (contDiff_one_quinticFourierCutoff hε).comp (by fun_prop)
  have hP : ContDiff ℝ 1 P := by
    apply contDiff_charFun (n := 1)
    simpa only [Nat.cast_one] using memLp_id_scaled_convolution hθ0.le hθ1
      (Real.sqrt (1 - θ ^ 2)) 1
  have hs : MeasurableSet H := measurableSet_lt measurable_const (by fun_prop)
  have hiq : Integrable (fun u => q u ^ 2) := integrable_sq_gaussian_cutoff hθ0 hθ1 hgap hε hε1
  have hid : Integrable (fun u => deriv q u ^ 2) :=
    integrable_sq_deriv_quinticFourierCutoff_mul hε hε1 hr
  have hq0 (u : ℝ) (hu : u ∈ H) : 0 ≤ q u := (quinticFourierCutoff_mem_Icc hε hε1 _).1
  have h0 (u : ℝ) (hu : u ∈ H) : ‖P u‖ ≤ E :=
    (varianceNormalized_highFrequency_bounds hθ0 hθ1 hgap hu.le).1
  have h1 (u : ℝ) (hu : u ∈ H) : ‖deriv P u‖ ≤ C * E :=
    (varianceNormalized_highFrequency_bounds hθ0 hθ1 hgap hu.le).2
  have heF : F = fun u => (q u : ℂ) * P u :=
    funext (angularFourier_varianceNormalizedSmoothing hθ0 hθ1 hε)
  have hdF (u : ℝ) : deriv F u =
      ((deriv q u : ℝ) : ℂ) * P u + (q u : ℂ) * deriv P u := by
    rw [heF]
    exact (((hq.differentiable (by norm_num)).differentiableAt.hasDerivAt.ofReal_comp).mul
      (hP.differentiable (by norm_num)).differentiableAt.hasDerivAt).deriv
  have he : (fun u => ‖F u‖ ^ 2 + ‖deriv F u‖ ^ 2) =
      (fun u => ‖(q u : ℂ) * P u‖ ^ 2 +
        ‖((deriv q u : ℝ) : ℂ) * P u + (q u : ℂ) * deriv P u‖ ^ 2) := by
    funext u
    rw [hdF, congrFun heF u]
  have hi := integrableOn_cutoff_product_energy hs
    hq.continuous.aestronglyMeasurable hq.continuous_deriv_one.aestronglyMeasurable
    hP.continuous.aestronglyMeasurable hP.continuous_deriv_one.aestronglyMeasurable
    hiq hid hq0 h0 h1
  have hb := half_integral_cutoff_product_energy_le hs
    hq.continuous.aestronglyMeasurable hq.continuous_deriv_one.aestronglyMeasurable
    hP.continuous.aestronglyMeasurable hP.continuous_deriv_one.aestronglyMeasurable
    hiq hid hq0 h0 h1
  rw [← he] at hi hb
  refine ⟨hi, hb.trans ?_⟩
  have hqc : (∫ u : ℝ, q u ^ 2) ≤ 4 / ((-Real.log θ) * Real.sqrt (-Real.log θ)) :=
    integral_sq_gaussian_cutoff_le hθ0 hθ1 hgap hε hε1
  have hdc : (∫ u : ℝ, deriv q u ^ 2) ≤ 6 * (-Real.log θ) * Real.sqrt (-Real.log θ) / ε :=
    integral_sq_deriv_gaussian_cutoff_le hθ0 hθ1 hε hε1
  have hc : C ^ 2 = 9 / (-Real.log θ) := by
    dsimp only [C]
    rw [div_pow, Real.sq_sqrt hχ.le]
    norm_num
  have hm := mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hqc
      (by positivity : 0 ≤ (1 / 2 : ℝ) * (1 + 2 * C ^ 2))) hdc) (sq_nonneg E)
  refine hm.trans_eq ?_
  rw [hc]
  dsimp only [E]
  ring

end LpSelfSimilar.Bernoulli
