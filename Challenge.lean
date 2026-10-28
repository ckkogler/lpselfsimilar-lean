/-
Copyright (c) 2026 Constantin Kogler.
Released under the BSD Zero Clause License; see LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.NumberTheory.MahlerMeasure
public import Mathlib.Tactic

/-!
# Lp densities of self-similar measures and Bernoulli convolutions

The introduction results of Samuel Kittle and Constantin Kogler are stated
independently below. An absolutely continuous self-similar measure has an Lp
density for some p > 1. Explicit algebraic hypotheses give continuous densities
for Bernoulli convolutions, with exponents 100 and 3. The cubic hypothesis also
gives an L2 density at the squared parameter; it implies the rational criterion
and continuity for every parameter 1 - 1/n with integer n >= 588.

A similarity may include a reflection. Its positive ratio is its metric scale;
ratios may differ and images may overlap. Bernoulli convolution means the law
of the actual convergent independent fair-sign series. Degree and Mahler
measure are canonical algebraic invariants. Logarithms are natural.

Density identities are equalities of measures with Lebesgue volume weighted
by the stated nonnegative functions. Compact support is part of the continuous
density conclusion. The theorem holes specify independent statements; Solution
supplies their proofs without importing this module. Imports here are Mathlib-only.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Metric Set Polynomial Real
open scoped ENNReal nonZeroDivisors

namespace LpSelfSimilar

/-- Euclidean d-space with its standard metric and Lebesgue volume. -/
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A similarity x ↦ ratio • orthogonal x + shift, allowing reflections. -/
structure Similarity (d : ℕ) where
  ratio : ℝ
  ratio_pos : 0 < ratio
  orthogonal : Space d ≃ₗᵢ[ℝ] Space d
  shift : Space d

namespace Similarity

/-- The actual affine action of the similarity. -/
noncomputable instance {d : ℕ} : CoeFun (Similarity d) (fun _ ↦ Space d → Space d) :=
  ⟨fun g x ↦ g.ratio • g.orthogonal x + g.shift⟩

end Similarity

namespace Bernoulli

/-- A Boolean digit is the sign +1 or -1. -/
def sign (e : Bool) : ℝ := if e then 1 else -1

/-- The fair-sign series; convergence for |r|<1 is proved in the library. -/
noncomputable def series (r : ℝ) (w : ℕ → Bool) : ℝ :=
  ∑' j : ℕ, sign (w j) * r ^ j

-- Reproduce the separate construction module's auxiliary-lemma boundary.
run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

/-- The genuine probability law of a single fair Boolean digit. -/
noncomputable def fairDigit : Measure Bool := bernoulliMeasure true false ⟨1 / 2, by norm_num⟩

/-- The countable product law of independent fair digits. -/
noncomputable def digitSpace : Measure (ℕ → Bool) := Measure.infinitePi (fun _ ↦ fairDigit)

/-- The Bernoulli convolution is the pushforward law of the actual sign series. -/
noncomputable def convolution (r : ℝ) : Measure ℝ := digitSpace.map (series r)

end Bernoulli

namespace Algebraic

/-- Clear rational denominators, remove content, and normalize to positive
leading coefficient. This gives zero only when the input polynomial is zero. -/
noncomputable def primitiveRepresentative (p : ℚ[X]) : ℤ[X] :=
  if p = 0 then 0 else normalize (IsLocalization.integerNormalization ℤ⁰ p).primPart

/-- The canonical primitive positive-leading integer minimal polynomial. -/
noncomputable def integerMinimalPolynomial (x : ℝ) : ℤ[X] :=
  primitiveRepresentative (minpoly ℚ x)

/-- The ordinary algebraic degree over the rationals. -/
noncomputable def algebraicDegree (x : ℝ) : ℕ := (minpoly ℚ x).natDegree

/-- Mathlib's genuine polynomial Mahler measure of the integer minimal polynomial.
Its equality to the leading-coefficient/root product is proved in the library. -/
noncomputable def mahlerMeasure (x : ℝ) : ℝ :=
  ((integerMinimalPolynomial x).map (Int.castRingHom ℂ)).mahlerMeasure

end Algebraic


/-- **Higher integrability of self-similar measures.** For every d >= 1,
take a finite nonempty family of similarities of Euclidean d-space, each with
contraction ratio strictly between zero and one. Their ratios may differ and
their images may overlap. Give them nonnegative weights summing to one, including
zero weights if desired. Every absolutely continuous stationary probability
measure nu = sum_i weight_i (g_i)_*nu has a nonnegative integrable density f and
there is a real p > 1 for which f belongs to L^p. -/
theorem self_similar_higher_integrability {d : ℕ} (hd : 1 ≤ d)
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (g : ι → Similarity d) (hg : ∀ i, (g i).ratio < 1)
    (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i) (hsum : ∑ i, weight i = 1)
    (ν : Measure (Space d)) [IsProbabilityMeasure ν]
    (hstationary : ν = ∑ i, ENNReal.ofReal (weight i) • ν.map (g i))
    (hac : ν ≪ volume) :
    ∃ f : Space d → ℝ, (∀ x, 0 ≤ f x) ∧ Integrable f volume ∧
      ν = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) ∧
      ∃ p : ℝ, 1 < p ∧ MemLp f (ENNReal.ofReal p) volume := by
  sorry

/-- **Algebraic Bernoulli convolutions.** Let lambda be an algebraic real
number strictly between 1/2 and 1. Let d be its degree over Q and M the Mahler
measure of its primitive integer minimal polynomial with positive leading
coefficient. If lambda >= 1 - (min(1,log M)/(1+d+log M))^100, the law of the
convergent random series sum_j epsilon_j lambda^j, with independent fair signs
epsilon_j in {-1,1}, has a nonnegative continuous compactly supported density. -/
theorem algebraic_bernoulli_convolution_continuous_density_non_strict {l : ℝ}
    (hlalg : IsAlgebraic ℚ l) (hl0 : 1 / 2 < l) (hl1 : l < 1)
    (hsmall : 1 - (min 1 (Real.log (Algebraic.mahlerMeasure l)) /
      (1 + (Algebraic.algebraicDegree l : ℝ) + Real.log (Algebraic.mahlerMeasure l))) ^ 100 ≤ l) :
    ∃ f : ℝ → ℝ, (∀ x, 0 ≤ f x) ∧ Continuous f ∧ HasCompactSupport f ∧
      Bernoulli.convolution l = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) := by
  sorry

open Algebraic

/-- **Cubic criterion (Theorem 1.3; cubic Theorem 1.1).** Under the non-strict
exponent-three hypothesis, both the L2 density at lambda squared and the
continuous compactly supported density at lambda exist. No preliminary
absolute-continuity or entropy assumption is required. -/
theorem algebraic_bernoulli_convolution_cubic {x : ℝ}
    (hx : IsAlgebraic ℚ x) (hxhalf : 1 / 2 < x) (hx1 : x < 1)
    (hcubic : 1 - (min 1 (log (mahlerMeasure x)) /
      (1 + (algebraicDegree x : ℝ) + log (mahlerMeasure x))) ^ 3 ≤ x) :
    (∃ f : ℝ → ℝ, Measurable f ∧ Integrable f volume ∧ (∀ y, 0 ≤ f y) ∧
      Bernoulli.convolution (x ^ 2) = volume.withDensity (fun y => ENNReal.ofReal (f y)) ∧
      MemLp f 2 volume) ∧
    (∃ g : ℝ → ℝ, (∀ y, 0 ≤ g y) ∧ Continuous g ∧ HasCompactSupport g ∧
      Bernoulli.convolution x = volume.withDensity (fun y => ENNReal.ofReal (g y))) := by
  sorry

/-- **Rational criterion.** For every pair of coprime positive integers p,q,
put lambda=1-p/q and assume 1/2 < lambda < 1. If p <= q/(2+log q)^3, the
Bernoulli convolution at lambda has an everywhere nonnegative continuous
compactly supported density, with the measure identity stated explicitly. -/
theorem rational_bernoulli_convolution_continuous_density_cubic
    (p q : ℕ) (_hp : 0 < p) (hq : 0 < q) (hpq : p.Coprime q)
    (hhalf : (1 : ℝ) / 2 < 1 - (p : ℝ) / (q : ℝ))
    (hone : 1 - (p : ℝ) / (q : ℝ) < 1)
    (hsmall : (p : ℝ) ≤ (q : ℝ) / (2 + log (q : ℝ)) ^ 3) :
    ∃ f : ℝ → ℝ, (∀ y, 0 ≤ f y) ∧ Continuous f ∧ HasCompactSupport f ∧
      Bernoulli.convolution (1 - (p : ℝ) / (q : ℝ)) =
        volume.withDensity (fun y => ENNReal.ofReal (f y)) := by
  sorry

/-- **The same family for integer denominators.** For every integer n >= 588,
the Bernoulli convolution at 1-1/n equals Lebesgue measure weighted by an
everywhere nonnegative continuous compactly supported density. Positivity,
the parameter range and the rational criterion follow from n >= 588. -/
theorem bernoulli_convolution_one_sub_inv_continuous_density_cubic_int (n : ℤ) (hn : 588 ≤ n) :
    ∃ f : ℝ → ℝ, (∀ y, 0 ≤ f y) ∧ Continuous f ∧ HasCompactSupport f ∧
      Bernoulli.convolution (1 - 1 / (n : ℝ)) =
        volume.withDensity (fun y => ENNReal.ofReal (f y)) := by
  sorry

end LpSelfSimilar
