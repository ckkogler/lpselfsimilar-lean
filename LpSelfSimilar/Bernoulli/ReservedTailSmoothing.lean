module

public import LpSelfSimilar.Bernoulli.ConditionalSmoothingEstimate
public import LpSelfSimilar.Bernoulli.BandMixtureProducts

@[expose] public section

/-!
# The tail-only smoothing estimate

The conditional smoothing theorem is applied to the empty block family. Its
actual convolution is the point mass at zero, its characteristic function is
one, and every positive-order derivative is zero. The unused finite prefix and
reserved infinite tail recover the complete Bernoulli law.
-/

open MeasureTheory MeasureTheory.Measure Set
open scoped BigOperators

namespace LpSelfSimilar.Bernoulli

/-- The reserved tail alone yields the exact T=0 smoothing coefficient for every r<=chi. -/
theorem reserved_tail_smoothing_bound {θ ρ L r : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hgap : -Real.log θ ≤ 1 / 250)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L) (hr : 0 < r) (hrχ : r ≤ -Real.log θ) :
    (∫ x, ‖Analysis.measureFunctionConvolution (convolution θ)
      (Analysis.rescaledKernel r (Fourier.angularInverseFourier
        (fun ξ ↦ (Fourier.quinticFourierDetail (packingFrequencyWidth (L / ρ)) ξ : ℂ)))) x‖) ≤
      smoothingPrefactor (-Real.log θ) (L / ρ) := by
  let p : Fin 0 → PMF Unit := fun i ↦ Fin.elim0 i
  let μ : Fin 0 → Unit → Measure ℝ := fun i ↦ Fin.elim0 i
  let c : Fin 0 → Unit → ℝ := fun i ↦ Fin.elim0 i
  let tail := reservedTailStart θ (packingFrequencyWidth (L / ρ)) r
  let η := (digitPMF θ tail).toMeasure
  haveI (i : Fin 0) (a : Unit) : IsProbabilityMeasure (μ i a) := Fin.elim0 i
  have hchar : charFun (dirac (0 : ℝ)) = fun _ : ℝ ↦ (1 : ℂ) := by
    funext ξ
    simp
  have hs (i : Fin 0) (a : Unit) : ((μ i a).map (fun y ↦ (y - c i a) / r)) (Icc 0 52) = 1 :=
    Fin.elim0 i
  have hb ξ (hξ : |(|ξ| - 1)| ≤ packingFrequencyWidth (L / ρ)) (j : ℕ) (hj : j ≤ 2) :
      (∫ ω, ‖iteratedDeriv j (charFun (finiteConvolution
        (fun i ↦ (μ i (ω i)).map (fun y ↦ (y - c i (ω i)) / r)))) ξ‖
          ∂(productPMF p).toMeasure) ≤
            (80 * L * (0 : ℕ) / (-Real.log θ)) ^ j *
              Real.exp (-(packingAttenuation (-Real.log θ) ρ L * (0 : ℕ))) := by
    simp only [finiteConvolution, hchar, iteratedDeriv_const]
    by_cases hj0 : j = 0
    · simp [hj0]
    · simp [hj0, zero_pow hj0]
  have h := conditional_blocks_smoothing_bound p μ c η hθ0 hθ1 hgap hρ hρ1 hL hr hrχ 0 hs hb
  have he := finiteConvolution_pmfMixture p μ
  change dirac (0 : ℝ) = pmfMixture (productPMF p)
    (fun ω ↦ finiteConvolution (fun i ↦ μ i (ω i))) at he
  rw [← he] at h
  have hlaw := convolution_prefix_tail (show |θ| < 1 by rwa [abs_of_pos hθ0]) tail
  change convolution θ = η ∗ (convolution θ).map
    (fun y ↦ θ ^ reservedTailStart θ (packingFrequencyWidth (L / ρ)) r * y) at hlaw
  simpa only [dirac_zero_conv, ← hlaw, Nat.cast_zero, zero_add, one_pow, mul_one,
    mul_zero, Real.exp_zero] using h

end LpSelfSimilar.Bernoulli
