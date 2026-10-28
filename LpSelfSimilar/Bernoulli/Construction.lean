module

public import LpSelfSimilar.Bernoulli.Digits
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section

/-!
Bernoulli convolutions as laws of convergent fair-sign series on the canonical
countable product probability space. The construction is explicit and does not
assume absolute continuity or invoke an unproved stationary-measure existence
theorem. The deterministic support bound holds for every digit sequence.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal

namespace LpSelfSimilar.Bernoulli

noncomputable section

/-- The balanced measure on a single binary digit. -/
def fairDigit : Measure Bool := bernoulliMeasure true false ⟨1 / 2, by norm_num⟩

instance : IsProbabilityMeasure fairDigit := inferInstanceAs
  (IsProbabilityMeasure (bernoulliMeasure true false ⟨1 / 2, by norm_num⟩))

lemma fairDigit_eq : fairDigit = (1 / 2 : ℝ≥0∞) • dirac true +
    (1 / 2 : ℝ≥0∞) • dirac false := by
  have hh : unitInterval.toNNReal ⟨1 / 2, by norm_num⟩ = (1 / 2 : NNReal) := by
    apply NNReal.eq
    norm_num
  have ht : unitInterval.toNNReal (unitInterval.symm ⟨1 / 2, by norm_num⟩) =
      (1 / 2 : NNReal) := by
    apply NNReal.eq
    norm_num
  rw [fairDigit, bernoulliMeasure, hh, ht]
  ext E hE
  simp only [Measure.add_apply, Measure.smul_apply, Measure.nnreal_smul_coe_apply, smul_eq_mul]
  norm_num

/-- Independent fair binary digits, indexed by the natural numbers. -/
def digitSpace : Measure (ℕ → Bool) := Measure.infinitePi (fun _ ↦ fairDigit)

instance : IsProbabilityMeasure digitSpace := inferInstanceAs
  (IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ ↦ fairDigit)))

@[fun_prop] lemma measurable_sign : Measurable sign := measurable_of_countable sign

@[fun_prop] lemma measurable_series (r : ℝ) : Measurable (series r) := by
  apply Measurable.tsum
  intro j
  exact (measurable_sign.comp (measurable_pi_apply j)).mul_const _

/-- The actual Bernoulli convolution, with digits ±1 as in the paper. The
definition is total, while every analytic result assumes a contracting parameter. -/
def convolution (r : ℝ) : Measure ℝ := digitSpace.map (series r)

instance (r : ℝ) : IsProbabilityMeasure (convolution r) :=
  inferInstanceAs (IsProbabilityMeasure (digitSpace.map (series r)))

lemma independent_digits : iIndepFun (fun j (w : ℕ → Bool) ↦ w j) digitSpace :=
  iIndepFun_infinitePi (fun _ ↦ measurable_id)

lemma digit_law (j : ℕ) : digitSpace.map (fun w ↦ w j) = fairDigit :=
  Measure.infinitePi_map_eval _ _

/-- Any subsequence indexed injectively by ℕ has the original product law. -/
lemma subsequence_law {f : ℕ → ℕ} (hf : Function.Injective f) :
    digitSpace.map (fun w j ↦ w (f j)) = digitSpace :=
  Measure.map_infinitePi_infinitePi_of_inj hf

lemma series_subsequence_law (r : ℝ) {f : ℕ → ℕ} (hf : Function.Injective f) :
    digitSpace.map (fun w ↦ series r (fun j ↦ w (f j))) = convolution r := by
  change digitSpace.map (series r ∘ (fun w j ↦ w (f j))) = _
  rw [← Measure.map_map (measurable_series r) (by fun_prop), subsequence_law hf]
  rfl

/-- No compact-support hypothesis is needed: the geometric series bounds every
point of the defining probability space. -/
lemma convolution_compl_interval (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    convolution r (Icc (-(1 - r)⁻¹) (1 - r)⁻¹)ᶜ = 0 := by
  rw [convolution, Measure.map_apply (measurable_series r) measurableSet_Icc.compl]
  have hpre : series r ⁻¹' (Icc (-(1 - r)⁻¹) (1 - r)⁻¹)ᶜ = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro w hw
    exact hw (abs_le.mp (abs_series_le hr0 hr1 w))
  rw [hpre, measure_empty]

end
end LpSelfSimilar.Bernoulli
