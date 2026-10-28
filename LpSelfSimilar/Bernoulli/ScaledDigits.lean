module

public import LpSelfSimilar.Probability.MapProbability

public import LpSelfSimilar.Bernoulli.FiniteLaw
public import LpSelfSimilar.Probability.FiniteConvolutionLaws

@[expose] public section

/-!
Laws and exact moments of scaled fair signs, and the independent finite
convolution formula for a scaled digit prefix. These supply every probabilistic
hypothesis of the Gaussian small-summand estimate directly from fair digits.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real
open scoped ENNReal

namespace LpSelfSimilar.Bernoulli

noncomputable def signLaw (a : ℝ) : Measure ℝ := fairDigit.map (fun e ↦ sign e * a)

instance (a : ℝ) : IsProbabilityMeasure (signLaw a) := LpSelfSimilar.Probability.isProbabilityMeasure_map (by fun_prop)

lemma signLaw_bound (a : ℝ) : ∀ᵐ u ∂signLaw a, |u| ≤ |a| := by
  rw [signLaw, ae_map_iff (by fun_prop) ((isClosed_le continuous_abs continuous_const).measurableSet)]
  exact ae_of_all _ (fun e ↦ by simp only [abs_mul, abs_sign, one_mul, le_refl])

lemma integral_signLaw (a : ℝ) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ u, f u ∂signLaw a) = (f a + f (-a)) / 2 := by
  rw [signLaw, integral_map (by fun_prop) hf.aestronglyMeasurable]
  rw [fairDigit, integral_bernoulliMeasure]
  simp only [sign_true, sign_false, one_mul, neg_one_mul, smul_eq_mul]
  norm_num
  ring

lemma signLaw_mean (a : ℝ) : (∫ u : ℝ, u ∂signLaw a) = 0 := by
  have h := integral_signLaw a (fun u : ℝ ↦ u) (by fun_prop)
  simpa only [add_neg_cancel, zero_div] using h

lemma signLaw_secondMoment (a : ℝ) : (∫ u : ℝ, u ^ 2 ∂signLaw a) = a ^ 2 := by
  rw [integral_signLaw a _ (by fun_prop)]
  ring

lemma scaled_prefix_law (a r : ℝ) (n : ℕ) :
    digitSpace.map (fun w ↦ a * digitSum r (fun j : Fin n ↦ w j)) =
      finiteConvolution (fun j : Fin n ↦ signLaw (a * r ^ (j : ℕ))) := by
  let X (j : Fin n) (w : ℕ → Bool) := sign (w j) * (a * r ^ (j : ℕ))
  have hm (j : Fin n) : Measurable (X j) := by fun_prop
  have hind : iIndepFun X digitSpace :=
    (independent_digits.precomp Fin.val_injective).comp (fun j ↦ fun e ↦ sign e * (a * r ^ (j : ℕ)))
      (fun _ ↦ by fun_prop)
  have he : (fun w ↦ a * digitSum r (fun j : Fin n ↦ w j)) = fun w ↦ ∑ j, X j w := by
    funext w
    rw [digitSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [X]
    ring
  have hl (j : Fin n) : digitSpace.map (X j) = signLaw (a * r ^ (j : ℕ)) := by
    rw [signLaw, ← digit_law j, Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [he, map_sum_eq_finiteConvolution hm hind]
  simp_rw [hl]

end LpSelfSimilar.Bernoulli
