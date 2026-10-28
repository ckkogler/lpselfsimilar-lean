module

public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

/-!
# The sign partition of a symmetric real probability law

The nonnegative half-line is encoded by true and the negative half-line by
false. For a reflection-invariant law with no mass at zero, the sign law is
fair. Only the zero atom must vanish; other atoms are allowed.
-/

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

namespace LpSelfSimilar.Probability

noncomputable def nonnegativeSign (x : ℝ) : Bool := if 0 ≤ x then true else false

@[fun_prop] theorem measurable_nonnegativeSign : Measurable nonnegativeSign := by
  unfold nonnegativeSign
  exact measurable_const.ite measurableSet_Ici measurable_const

theorem nonnegativeSign_preimage_false : nonnegativeSign ⁻¹' {false} = Iio 0 := by
  ext x
  simp [nonnegativeSign, not_le]

theorem nonnegativeSign_preimage_true : nonnegativeSign ⁻¹' {true} = Ici 0 := by
  ext x
  simp [nonnegativeSign]

/-- A null endpoint makes the open and closed upper half-lines have equal mass. -/
theorem measure_Ici_eq_Ioi_of_singleton_zero (μ : Measure ℝ) (b : ℝ)
    (hb : μ {b} = 0) : μ (Ici b) = μ (Ioi b) := by
  have he : Ici b = {b} ∪ Ioi b := by
    ext x
    simp only [mem_Ici, mem_union, mem_singleton_iff, mem_Ioi]
    constructor
    · intro hx; rcases hx.eq_or_lt with h | h
      · exact Or.inl h.symm
      · exact Or.inr h
    · rintro (rfl | h) <;> linarith
  rw [he, measure_union (by simp) measurableSet_Ioi, hb, zero_add]

/-- Reflection symmetry and a null zero atom give exactly fair sign masses. -/
theorem symmetric_sign_masses (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsym : μ.map (fun x : ℝ => -x) = μ) (hzero : μ {0} = 0) :
    ∀ b : Bool, (μ.map nonnegativeSign) {b} = (1 / 2 : ℝ≥0∞) := by
  have href : μ (Ioi 0) = μ (Iio 0) := by
    have h := congrArg (fun ν : Measure ℝ => ν (Iio 0)) hsym
    rw [Measure.map_apply measurable_neg measurableSet_Iio] at h
    simpa only [show (fun x : ℝ => -x) ⁻¹' Iio 0 = Ioi 0 by ext x; simp] using h
  have hclosed : μ (Ici 0) = μ (Ioi 0) :=
    measure_Ici_eq_Ioi_of_singleton_zero μ 0 hzero
  have hsum := measure_add_measure_compl (μ := μ) (s := Iio (0 : ℝ)) measurableSet_Iio
  rw [compl_Iio, measure_univ, hclosed, href] at hsum
  have hr := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _), ENNReal.toReal_one] at hr
  have hhalf : μ (Iio 0) = (1 / 2 : ℝ≥0∞) := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (by norm_num)).mp
    norm_num
    linarith
  intro b
  rw [Measure.map_apply measurable_nonnegativeSign (measurableSet_singleton b)]
  cases b with
  | false => rw [nonnegativeSign_preimage_false, hhalf]
  | true => rw [nonnegativeSign_preimage_true, hclosed, href, hhalf]

end LpSelfSimilar.Probability
