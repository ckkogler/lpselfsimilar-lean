module

public import LpSelfSimilar.Bernoulli.Decomposition
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
Deterministic splitting of the Bernoulli series into residue classes. Absolute
convergence justifies regrouping all digits, and each subsequence has the same
fair product law. The powers of the parameter in the final smoothing argument
arise from this exact identity.
-/

open MeasureTheory MeasureTheory.Measure
open scoped BigOperators

namespace LpSelfSimilar.Bernoulli

/-- The index of the `n`th digit in residue class `j`. -/
def residueIndex (k : ℕ) (j : Fin k) (n : ℕ) : ℕ := n * k + j

lemma residueIndex_injective {k : ℕ} (hk : 0 < k) (j : Fin k) :
    Function.Injective (residueIndex k j) := by
  intro m n h
  dsimp [residueIndex] at h
  exact Nat.eq_of_mul_eq_mul_right hk (Nat.add_right_cancel h)

lemma series_split_residues {r : ℝ} (hr : |r| < 1) {k : ℕ} (hk : 0 < k)
    (w : ℕ → Bool) :
    series r w = ∑ j : Fin k, r ^ (j : ℕ) * series (r ^ k) (fun n ↦ w (residueIndex k j n)) := by
  letI : NeZero k := ⟨hk.ne'⟩
  let e : (Fin k × ℕ) ≃ ℕ :=
    (Equiv.prodComm (Fin k) ℕ).trans (Nat.divModEquiv k).symm
  have he (p : Fin k × ℕ) : e p = residueIndex k p.1 p.2 := rfl
  have hs := (e.summable_iff).mpr (summable_sign_mul_pow hr w)
  change Summable (fun p : Fin k × ℕ ↦ sign (w (e p)) * r ^ e p) at hs
  calc
    series r w = ∑' p : Fin k × ℕ, sign (w (e p)) * r ^ e p := (e.tsum_eq _).symm
    _ = ∑ j : Fin k, ∑' n, sign (w (residueIndex k j n)) * r ^ residueIndex k j n := by
      rw [hs.tsum_prod, tsum_fintype]
      rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [series, ← tsum_mul_left]
      apply tsum_congr
      intro n
      simp only [residueIndex, pow_add, pow_mul]
      ring

lemma residue_series_law (r : ℝ) {k : ℕ} (hk : 0 < k) (j : Fin k) :
    digitSpace.map (fun w ↦ series (r ^ k) (fun n ↦ w (residueIndex k j n))) =
      convolution (r ^ k) :=
  series_subsequence_law _ (residueIndex_injective hk j)

end LpSelfSimilar.Bernoulli
