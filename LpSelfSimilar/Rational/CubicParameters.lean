module

public import LpSelfSimilar.Algebraic.RationalIdentification
public import LpSelfSimilar.Rational.Parameters
public import LpSelfSimilar.Analysis.CubicLogRatios

@[expose] public section

/-!
# Rational identification of the exact cubic hypothesis

Reduction of 1-p/q gives canonical degree one and Mahler measure q. The
parameter interval forces q>=3, hence log(q)>1 and the truncated logarithm
is exactly one. The displayed rational inequality is therefore precisely
sufficient for the non-strict canonical cubic hypothesis.
-/

open Real
open LpSelfSimilar.Algebraic

namespace LpSelfSimilar.Rational

/-- Actual canonical rational invariants and the truncated logarithm. -/
theorem cubic_gap_parameter_invariants {p q : ℕ} (hq : 0 < q) (hpq : p.Coprime q)
    (hhalf : (1 : ℝ) / 2 < 1 - (p : ℝ) / q) (hone : 1 - (p : ℝ) / q < 1) :
    algebraicDegree (1 - (p : ℝ) / q) = 1 ∧
      mahlerMeasure (1 - (p : ℝ) / q) = (q : ℝ) ∧
      min 1 (log (mahlerMeasure (1 - (p : ℝ) / q))) = 1 := by
  obtain ⟨ha, hb, hab, he⟩ := reduced_gap_parameter hq hpq hhalf hone
  have hlt : q - p < q := by
    exact_mod_cast (div_lt_one (by positivity : (0 : ℝ) < q)).mp (he ▸ hone)
  have hM : mahlerMeasure (1 - (p : ℝ) / q) = (q : ℝ) := by
    rw [he, mahlerMeasure_rat_div hq hab hlt]
  refine ⟨?_, hM, ?_⟩
  · rw [he, algebraicDegree_rat_div]
  · rw [hM, min_eq_left]
    exact Analysis.one_le_log_of_three_le (by exact_mod_cast hb)

/-- The rational denominator with exponent three implies the exact algebraic cubic endpoint. -/
theorem rational_cubic_hypothesis {p q : ℕ} (hq : 0 < q) (hpq : p.Coprime q)
    (hhalf : (1 : ℝ) / 2 < 1 - (p : ℝ) / q) (hone : 1 - (p : ℝ) / q < 1)
    (hsmall : (p : ℝ) ≤ (q : ℝ) / (2 + log (q : ℝ)) ^ 3) :
    1 - (min 1 (log (mahlerMeasure (1 - (p : ℝ) / q))) /
      (1 + (algebraicDegree (1 - (p : ℝ) / q) : ℝ) +
        log (mahlerMeasure (1 - (p : ℝ) / q)))) ^ 3 ≤ 1 - (p : ℝ) / q := by
  obtain ⟨hd, hM, hs⟩ := cubic_gap_parameter_invariants hq hpq hhalf hone
  rw [hs, hd, hM]
  norm_num at ⊢
  have hq0 : (0 : ℝ) < q := by positivity
  have h : (p : ℝ) / q ≤ 1 / (2 + log (q : ℝ)) ^ 3 := by
    apply (div_le_iff₀ hq0).mpr
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using hsmall
  rw [one_div] at h
  linarith

end LpSelfSimilar.Rational
