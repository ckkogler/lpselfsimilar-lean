module

public import LpSelfSimilar.Algebraic.CubicSquareDensity
public import LpSelfSimilar.Bernoulli.ContinuousDensity

@[expose] public section

/-!
# The algebraic cubic continuity theorem

The exact non-strict cubic hypothesis gives an actual nonnegative L2 density
at the squared parameter. The existing even/odd convolution argument then gives
an everywhere nonnegative continuous compactly supported density at the original
parameter. Both conclusions include explicit equality to weighted Lebesgue measure.
Canonical degree and Mahler measure appear directly in the public hypotheses.
-/

open MeasureTheory Real
open LpSelfSimilar.Algebraic

namespace LpSelfSimilar

/-- The square-density conclusion of the cubic theorem, at its exact hypotheses and endpoint. -/
theorem algebraic_bernoulli_convolution_square_density_cubic {x : ℝ}
    (hx : IsAlgebraic ℚ x) (hxhalf : 1 / 2 < x) (hx1 : x < 1)
    (hcubic : 1 - (min 1 (log (mahlerMeasure x)) /
      (1 + (algebraicDegree x : ℝ) + log (mahlerMeasure x))) ^ 3 ≤ x) :
    ∃ f : ℝ → ℝ, Measurable f ∧ Integrable f volume ∧ (∀ y, 0 ≤ f y) ∧
      Bernoulli.convolution (x ^ 2) = volume.withDensity (fun y => ENNReal.ofReal (f y)) ∧
      MemLp f 2 volume := by
  obtain ⟨f, hfm, hfi, hfn, hrep, hLp, herr⟩ :=
    cubic_square_density_with_gaussian_error hx (by linarith) hx1 hcubic
  exact ⟨f, hfm, hfi, hfn, hrep, hLp⟩

/-- The continuous compact-density conclusion of the cubic theorem, with no extra analytic inputs. -/
theorem algebraic_bernoulli_convolution_continuous_density_cubic {x : ℝ}
    (hx : IsAlgebraic ℚ x) (hxhalf : 1 / 2 < x) (hx1 : x < 1)
    (hcubic : 1 - (min 1 (log (mahlerMeasure x)) /
      (1 + (algebraicDegree x : ℝ) + log (mahlerMeasure x))) ^ 3 ≤ x) :
    ∃ f : ℝ → ℝ, (∀ y, 0 ≤ f y) ∧ Continuous f ∧ HasCompactSupport f ∧
      Bernoulli.convolution x = volume.withDensity (fun y => ENNReal.ofReal (f y)) := by
  obtain ⟨f, hfm, hfi, hfn, hrep, hLp⟩ :=
    algebraic_bernoulli_convolution_square_density_cubic hx hxhalf hx1 hcubic
  apply Bernoulli.continuous_density_of_power_memLp (by linarith) hx1 (k := 2) (by norm_num)
    hfi hfn hrep
  convert! hLp using 1 <;> norm_num

/-- Both conclusions of the algebraic cubic theorem, with their actual density representations. -/
theorem algebraic_bernoulli_convolution_cubic {x : ℝ}
    (hx : IsAlgebraic ℚ x) (hxhalf : 1 / 2 < x) (hx1 : x < 1)
    (hcubic : 1 - (min 1 (log (mahlerMeasure x)) /
      (1 + (algebraicDegree x : ℝ) + log (mahlerMeasure x))) ^ 3 ≤ x) :
    (∃ f : ℝ → ℝ, Measurable f ∧ Integrable f volume ∧ (∀ y, 0 ≤ f y) ∧
      Bernoulli.convolution (x ^ 2) = volume.withDensity (fun y => ENNReal.ofReal (f y)) ∧
      MemLp f 2 volume) ∧
    (∃ g : ℝ → ℝ, (∀ y, 0 ≤ g y) ∧ Continuous g ∧ HasCompactSupport g ∧
      Bernoulli.convolution x = volume.withDensity (fun y => ENNReal.ofReal (g y))) :=
  ⟨algebraic_bernoulli_convolution_square_density_cubic hx hxhalf hx1 hcubic,
    algebraic_bernoulli_convolution_continuous_density_cubic hx hxhalf hx1 hcubic⟩

end LpSelfSimilar
