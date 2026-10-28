module

public import LpSelfSimilar.Probability.PairPMF
public import Mathlib.Tactic

@[expose] public section

/-!
# Statistics of independent finite inputs

Applying separate statistics to independent inputs preserves the product of
atom probabilities, even if either statistic has collisions and its codomain
is infinite. The inputs alone are finite; no separation is assumed.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LpSelfSimilar

/-- The joint mass of separate statistics of independent finite inputs factors exactly. -/
theorem pairPMF_map_pair_apply {ι κ A B : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (p : PMF ι) (q : PMF κ) (X : ι → A) (Y : κ → B) (a : A) (b : B) :
    ((pairPMF p q).map (fun z => (X z.1, Y z.2))) (a, b) = p.map X a * q.map Y b := by
  classical
  simp only [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, pairPMF_apply,
    Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases ha : a = X i <;> by_cases hb : b = Y j <;> simp [Prod.mk.injEq, ha, hb]

end LpSelfSimilar
