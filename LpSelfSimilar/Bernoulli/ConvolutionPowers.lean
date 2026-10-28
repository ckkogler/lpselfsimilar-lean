module

public import LpSelfSimilar.Bernoulli.ResidueLaw
public import LpSelfSimilar.Probability.FiniteConvolution

@[expose] public section

/-!
Exact decomposition into scaled copies of the Bernoulli convolution at a power
of its parameter. Absolute convergence gives equality of the sums, and the full
joint residue law gives the finite convolution of their marginal measures.
-/

open MeasureTheory MeasureTheory.Measure

namespace LpSelfSimilar.Bernoulli

theorem convolution_eq_finiteConvolution_power {r : ℝ} (hr : |r| < 1)
    {k : ℕ} (hk : 0 < k) :
    convolution r = finiteConvolution (fun j : Fin k ↦
      (convolution (r ^ k)).map (fun x ↦ r ^ (j : ℕ) * x)) := by
  have hs : series r = (fun w ↦ ∑ j : Fin k,
      r ^ (j : ℕ) * series (r ^ k) (fun n ↦ w (residueIndex k j n))) :=
    funext (series_split_residues hr hk)
  conv_lhs =>
    rw [convolution, hs, map_sum_eq_finiteConvolution (fun _ ↦ by fun_prop)
      (independent_residue_series r hk)]
  congr 1
  funext j
  exact scaled_residue_series_law r hk j

end LpSelfSimilar.Bernoulli
