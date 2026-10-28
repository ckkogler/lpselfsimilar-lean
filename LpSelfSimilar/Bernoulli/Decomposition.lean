module

public import LpSelfSimilar.Bernoulli.Construction
public import LpSelfSimilar.Probability.IndependentCoordinates

@[expose] public section

/-!
Independence and convolution identities for disjoint digit subsequences.
In particular, splitting the first sign from the tail proves the stationarity
equation of the Bernoulli convolution from its explicit series construction.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal

namespace LpSelfSimilar.Bernoulli

lemma independent_subsequences {α β : Type*} (f : α → ℕ) (g : β → ℕ)
    (hfg : Disjoint (range f) (range g)) :
    IndepFun (fun w i ↦ w (f i)) (fun w j ↦ w (g j)) digitSpace :=
  independent_coordinate_families (fun j ↦ measurable_pi_apply j) independent_digits f g hfg

lemma independent_head_tail :
    IndepFun (fun w : ℕ → Bool ↦ w 0) (fun w j ↦ w (j + 1)) digitSpace := by
  have h := independent_subsequences (fun _ : Unit ↦ 0) (fun j ↦ j + 1) (by
    rw [Set.disjoint_left]
    rintro _ ⟨_, rfl⟩ ⟨j, hj⟩
    change j + 1 = 0 at hj
    omega)
  exact h.comp (measurable_pi_apply ()) measurable_id

/-- Splitting the first digit gives a convolution with a rescaled independent
copy of the original law. -/
lemma convolution_head_tail {r : ℝ} (hr : |r| < 1) :
    convolution r = (fairDigit.map sign) ∗ ((convolution r).map (fun x ↦ r * x)) := by
  have h := independent_head_tail.comp measurable_sign
    ((measurable_series r).const_mul r)
  have heq : series r = (fun w ↦ sign (w 0)) +
      (fun w ↦ r * series r (fun j ↦ w (j + 1))) := funext (series_eq_head_add_tail hr)
  change IndepFun (fun w ↦ sign (w 0))
    (fun w ↦ r * series r (fun j ↦ w (j + 1))) digitSpace at h
  conv_lhs => rw [convolution, heq, h.map_add_eq_map_conv_map (by fun_prop) (by fun_prop)]
  have hsign : digitSpace.map (fun w ↦ sign (w 0)) = fairDigit.map sign := by
    rw [← digit_law 0, Measure.map_map measurable_sign (measurable_pi_apply 0)]
    rfl
  rw [hsign]
  congr 1
  have htail := series_subsequence_law r (f := fun j ↦ j + 1) Nat.succ_injective
  rw [← htail, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- The balanced affine stationarity equation, proved without absolute continuity. -/
lemma convolution_stationary {r : ℝ} (hr : |r| < 1) :
    convolution r = (1 / 2 : ℝ≥0∞) • (convolution r).map (fun x ↦ r * x + 1) +
      (1 / 2 : ℝ≥0∞) • (convolution r).map (fun x ↦ r * x - 1) := by
  conv_lhs => rw [convolution_head_tail hr]
  have hfair : fairDigit.map sign =
      (1 / 2 : ℝ≥0∞) • dirac (1 : ℝ) + (1 / 2 : ℝ≥0∞) • dirac (-1 : ℝ) := by
    rw [fairDigit_eq, Measure.map_add _ _ measurable_sign]
    rw [Measure.map_smul _ measurable_sign.aemeasurable,
      Measure.map_smul _ measurable_sign.aemeasurable]
    simp [Measure.map_dirac' measurable_sign]
  rw [hfair, add_conv, conv_smul_left, conv_smul_left, dirac_conv, dirac_conv,
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def, add_comm, sub_eq_add_neg]

end LpSelfSimilar.Bernoulli
