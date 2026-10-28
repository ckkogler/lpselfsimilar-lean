module

public import LpSelfSimilar.Probability.IndependentCoordinates
public import Mathlib.Probability.Independence.Integration

@[expose] public section

/-!
Finite convolutions, including the empty convolution, and their exact relation
to sums of mutually independent real random variables. The recursive order is
explicit; no informal appeal to independence of a sum is needed.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set

namespace LpSelfSimilar

/-- The empty convolution is the point mass at zero. -/
noncomputable def finiteConvolution : {n : ℕ} → (Fin n → Measure ℝ) → Measure ℝ
  | 0, _ => dirac 0
  | n + 1, μ => μ 0 ∗ finiteConvolution (fun j : Fin n ↦ μ j.succ)

lemma independent_head_sum_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} {X : Fin (n + 1) → Ω → ℝ} (hX : ∀ j, Measurable (X j))
    (hind : iIndepFun X P) :
    IndepFun (X 0) (fun ω ↦ ∑ j : Fin n, X j.succ ω) P := by
  have h := independent_coordinate_families hX hind
    (fun _ : Unit ↦ (0 : Fin (n + 1))) (fun j : Fin n ↦ j.succ) (by
      rw [Set.disjoint_left]
      rintro _ ⟨_, rfl⟩ ⟨j, hj⟩
      exact Fin.succ_ne_zero j hj)
  have hm : Measurable (fun v : Fin n → ℝ ↦ ∑ j, v j) := by fun_prop
  exact h.comp (measurable_pi_apply ()) hm

theorem map_sum_eq_finiteConvolution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} {X : Fin n → Ω → ℝ}
    (hX : ∀ j, Measurable (X j)) (hind : iIndepFun X P) :
    P.map (fun ω ↦ ∑ j, X j ω) = finiteConvolution (fun j ↦ P.map (X j)) := by
  induction n with
  | zero => simp [finiteConvolution, Measure.map_const]
  | succ n ih =>
    have heq : (fun ω ↦ ∑ j, X j ω) = X 0 + (fun ω ↦ ∑ j : Fin n, X j.succ ω) := by
      funext ω
      exact Fin.sum_univ_succ (fun j ↦ X j ω)
    rw [heq, (independent_head_sum_tail hX hind).map_add_eq_map_conv_map
      (by fun_prop) (by fun_prop)]
    rw [ih (fun j ↦ hX j.succ) (hind.precomp (Fin.succ_injective n))]
    rfl

end LpSelfSimilar
