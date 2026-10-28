module

public import LpSelfSimilar.Algebraic.FinitePowerMoments
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Tactic

@[expose] public section

/-!
# Real observations of distinct real and conjugate-paired nodes

A real node is included once and an upper-half-plane node with its conjugate.
Real observations are exactly the power moments of this complex family. The
Vandermonde theorem then separates the real and complex coefficients. This is
the observation argument for a real spectral block matrix.
-/

open scoped ComplexConjugate

namespace LpSelfSimilar.Algebraic

/-- Real entries together with a complex entry and its conjugate for every pair. -/
def pairedComplexValues {R C : Type*} (a : R → ℝ) (z : C → ℂ) : R ⊕ (Bool × C) → ℂ
  | Sum.inl i => a i
  | Sum.inr (true, j) => z j
  | Sum.inr (false, j) => conj (z j)

/-- Distinct real nodes and distinct upper-half-plane nodes give a distinct full family. -/
theorem pairedComplexValues_injective {R C : Type*} (a : R → ℝ) (z : C → ℂ)
    (ha : Function.Injective a) (hz : Function.Injective z) (hi : ∀ j, 0 < (z j).im) :
    Function.Injective (pairedComplexValues a z) := by
  rintro (i | ⟨b,j⟩) (k | ⟨c,l⟩) h
  · exact congrArg Sum.inl (ha (Complex.ofReal_injective h))
  · exfalso
    have hh := congrArg Complex.im h
    cases c <;> simp only [pairedComplexValues, Complex.ofReal_im, Complex.conj_im] at hh
    all_goals linarith [hi l]
  · exfalso
    have hh := congrArg Complex.im h
    cases b <;> simp only [pairedComplexValues, Complex.ofReal_im, Complex.conj_im] at hh
    all_goals linarith [hi j]
  · cases b <;> cases c
    · exact congrArg (fun j => Sum.inr (false,j)) (hz (Complex.conjAe.injective h))
    · exfalso
      have hh := congrArg Complex.im h
      simp only [pairedComplexValues, Complex.conj_im] at hh
      linarith [hi j, hi l]
    · exfalso
      have hh := congrArg Complex.im h
      simp only [pairedComplexValues, Complex.conj_im] at hh
      linarith [hi j, hi l]
    · exact congrArg (fun j => Sum.inr (true,j)) (hz h)

/-- The complex moment is real, and each conjugate pair supplies twice its real part. -/
theorem pairedComplexValues_moment {R C : Type*} [Fintype R] [Fintype C]
    (a u : R → ℝ) (z v : C → ℂ) (n : ℕ) :
    (∑ i, pairedComplexValues u v i * pairedComplexValues a z i ^ n) =
      ((∑ i, u i * a i ^ n) + 2 * ∑ j, (v j * z j ^ n).re : ℝ) := by
  have hr : (∑ i, (u i : ℂ) * (a i : ℂ) ^ n) = ((∑ i, u i * a i ^ n) : ℝ) := by
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow]
  have hc : (∑ j, conj (v j) * conj (z j) ^ n) = conj (∑ j, v j * z j ^ n) := by
    simp only [map_sum, map_mul, map_pow]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool, pairedComplexValues]
  rw [hr, hc, Complex.add_conj, Complex.re_sum, ← Complex.ofReal_add]

/-- Vanishing real orbit observations separate every real and paired complex coordinate. -/
theorem real_complex_power_moments_separate {R C : Type*} [Fintype R] [Fintype C]
    (a : R → ℝ) (z : C → ℂ) (ha : Function.Injective a) (hz : Function.Injective z)
    (hi : ∀ j, 0 < (z j).im) (u : R → ℝ) (v : C → ℂ)
    (h : ∀ n : ℕ, (∑ i, u i * a i ^ n) + 2 * ∑ j, (v j * z j ^ n).re = 0) :
    u = 0 ∧ v = 0 := by
  have hh : pairedComplexValues u v = 0 := by
    apply finite_power_moments_separate_all (pairedComplexValues a z)
      (pairedComplexValues_injective a z ha hz hi)
    intro n
    rw [pairedComplexValues_moment, h n, Complex.ofReal_zero]
  constructor
  · ext i
    have he := congrFun hh (Sum.inl i)
    exact Complex.ofReal_injective he
  · ext j
    exact congrFun hh (Sum.inr (true,j))

end LpSelfSimilar.Algebraic
