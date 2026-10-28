module

public import LpSelfSimilar.Bernoulli.Construction
public import Mathlib.Probability.Distributions.Uniform

@[expose] public section

/-!
The finite digit law is the pushforward of the uniform law on all `2^n` words.
We prove that it is also the law of the first `n` coordinates of the canonical
infinite series. This connects finite arithmetic/entropy to the Bernoulli measure.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace LpSelfSimilar.Bernoulli

lemma fairDigit_singleton (e : Bool) : fairDigit {e} = (1 / 2 : ℝ≥0∞) := by
  cases e <;> norm_num [fairDigit_eq, Measure.smul_apply, smul_eq_mul]

/-- The uniform distribution on finite words agrees with the product of fair digits. -/
lemma finite_product_eq_uniform (n : ℕ) :
    Measure.pi (fun _ : Fin n ↦ fairDigit) = (PMF.uniformOfFintype (Fin n → Bool)).toMeasure := by
  apply Measure.ext_of_singleton
  intro w
  rw [Measure.pi_singleton, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp [fairDigit_singleton, PMF.uniformOfFintype_apply, Fintype.card_fun, ENNReal.inv_pow]

lemma prefix_law (n : ℕ) :
    digitSpace.map (fun w (j : Fin n) ↦ w j) = (PMF.uniformOfFintype (Fin n → Bool)).toMeasure := by
  calc
    digitSpace.map (fun w (j : Fin n) ↦ w j) =
        Measure.infinitePi (fun _ : Fin n ↦ fairDigit) :=
      Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective
    _ = _ := by rw [Measure.infinitePi_eq_pi, finite_product_eq_uniform]

/-- The finitely supported law of the first `n` signed digits. -/
noncomputable def digitPMF (r : ℝ) (n : ℕ) : PMF ℝ :=
  (PMF.uniformOfFintype (Fin n → Bool)).map (digitSum r)

lemma digitPMF_support_finite (r : ℝ) (n : ℕ) : (digitPMF r n).support.Finite := by
  rw [digitPMF, PMF.support_map]
  exact (Set.toFinite _).image _

lemma digitSum_law (r : ℝ) (n : ℕ) :
    digitSpace.map (fun w ↦ digitSum r (fun j : Fin n ↦ w j)) = (digitPMF r n).toMeasure := by
  have hmeas : Measurable (digitSum r (n := n)) := measurable_of_countable _
  change digitSpace.map (digitSum r ∘ (fun w (j : Fin n) ↦ w j)) = _
  rw [← Measure.map_map hmeas (by fun_prop), prefix_law, PMF.toMeasure_map _ _ hmeas]
  rfl

end LpSelfSimilar.Bernoulli
