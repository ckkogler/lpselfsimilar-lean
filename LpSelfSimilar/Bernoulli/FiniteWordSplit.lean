module

public import LpSelfSimilar.Bernoulli.FiniteLaw
public import LpSelfSimilar.Probability.UniformReindex
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# Splitting a finite Bernoulli word

Concatenation separates a word sum into its prefix and a scaled suffix. The
uniform-word equivalence proves that these two inputs are independent. These
identities hold for every real parameter, including zero, and empty word parts.
-/

open MeasureTheory ProbabilityTheory

namespace LpSelfSimilar.Bernoulli

/-- Concatenating words gives the prefix sum plus the correctly scaled suffix sum. -/
theorem digitSum_append (r : ℝ) {m n : ℕ} (u : Fin m → Bool) (v : Fin n → Bool) :
    digitSum r (Fin.append u v) = digitSum r u + r ^ m * digitSum r v := by
  rw [digitSum, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Fin.val_castAdd, Fin.val_natAdd, pow_add]
  rw [digitSum, digitSum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The actual finite digit law is a combination of two independent uniform word laws. -/
theorem digitPMF_add_eq_pair_map (r : ℝ) (m n : ℕ) :
    digitPMF r (m + n) =
      (pairPMF (PMF.uniformOfFintype (Fin m → Bool))
        (PMF.uniformOfFintype (Fin n → Bool))).map
        (fun z => digitSum r z.1 + r ^ m * digitSum r z.2) := by
  rw [pairPMF_uniform]
  have h := congrArg (fun p : PMF (Fin (m + n) → Bool) => p.map (digitSum r))
    (uniformPMF_map_equiv (Fin.appendEquiv (α := Bool) m n))
  have hsum (z : (Fin m → Bool) × (Fin n → Bool)) :
      digitSum r ((Fin.appendEquiv (α := Bool) m n) z) =
        digitSum r z.1 + r ^ m * digitSum r z.2 := by
    change digitSum r (Fin.append z.1 z.2) = _
    exact digitSum_append r z.1 z.2
  simpa only [PMF.map_comp, Function.comp_def, hsum, digitPMF] using h.symm

end LpSelfSimilar.Bernoulli
