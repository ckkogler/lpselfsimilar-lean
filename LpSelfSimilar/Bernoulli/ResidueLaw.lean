module

public import LpSelfSimilar.Bernoulli.Residues

@[expose] public section

/-!
The joint law of all residue-class digit streams is a product law. In particular,
the scaled residue series used to decompose a Bernoulli convolution are mutually
independent, not merely pairwise independent.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory

namespace LpSelfSimilar.Bernoulli

lemma residue_streams_law {k : ℕ} (hk : 0 < k) :
    digitSpace.map (fun w (j : Fin k) n ↦ w (residueIndex k j n)) =
      Measure.pi (fun _ : Fin k ↦ digitSpace) := by
  letI : NeZero k := ⟨hk.ne'⟩
  let e : (Fin k × ℕ) ≃ ℕ :=
    (Equiv.prodComm (Fin k) ℕ).trans (Nat.divModEquiv k).symm
  have h := map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ ↦ fairDigit) e.injective
  have hm := congrArg (fun ν : Measure ((Fin k × ℕ) → Bool) ↦
    ν.map (MeasurableEquiv.curry (Fin k) ℕ Bool)) h
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    infinitePi_map_curry (fun (_ : Fin k) (_ : ℕ) ↦ fairDigit)] at hm
  change digitSpace.map (fun w (j : Fin k) n ↦ w (residueIndex k j n)) =
    infinitePi (fun _ : Fin k ↦ digitSpace) at hm
  rw [infinitePi_eq_pi (fun _ : Fin k ↦ digitSpace)] at hm
  exact hm

lemma independent_residue_streams {k : ℕ} (hk : 0 < k) :
    iIndepFun (fun (j : Fin k) w n ↦ w (residueIndex k j n)) digitSpace := by
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun j ↦
    (Measurable.of_eval (fun n ↦ measurable_pi_apply (residueIndex k j n))).aemeasurable)).mpr
  rw [residue_streams_law hk]
  congr 1
  funext j
  exact (subsequence_law (residueIndex_injective hk j)).symm

lemma independent_residue_series (r : ℝ) {k : ℕ} (hk : 0 < k) :
    iIndepFun (fun (j : Fin k) w ↦
      r ^ (j : ℕ) * series (r ^ k) (fun n ↦ w (residueIndex k j n))) digitSpace :=
  (independent_residue_streams hk).comp
    (fun j w ↦ r ^ (j : ℕ) * series (r ^ k) w) (fun _ ↦ by fun_prop)

lemma scaled_residue_series_law (r : ℝ) {k : ℕ} (hk : 0 < k) (j : Fin k) :
    digitSpace.map (fun w ↦ r ^ (j : ℕ) *
      series (r ^ k) (fun n ↦ w (residueIndex k j n))) =
      (convolution (r ^ k)).map (fun x ↦ r ^ (j : ℕ) * x) := by
  rw [← residue_series_law r hk j, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

end LpSelfSimilar.Bernoulli
