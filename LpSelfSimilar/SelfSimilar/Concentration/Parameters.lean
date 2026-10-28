module

public import Mathlib.Tactic

@[expose] public section

/-!
# The exact numerical margin in sharp concentration stopping

The paper's strict hypothesis 12*K*e<theta is exactly beta^2*D0<1 for
beta=2*e and D0=3/(theta*e/K). It permits a strictly larger multiplier D,
as needed for open outer approximation, while preserving beta^2*D<1.
-/

open Set

namespace LpSelfSimilar.SelfSimilar.Concentration

/-- The concentration level lies strictly between zero and one under the sharp hypothesis. -/
theorem concentration_level_mem_Ioo {θ K e : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hK : 1 ≤ K) (he : 0 < e)
    (hsharp : 12 * K * e < θ) : θ * (e / K) ∈ Ioo 0 1 := by
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have he1 : e < 1 := by nlinarith
  have heK : e / K < 1 := (div_lt_one hK0).mpr (he1.trans_le hK)
  constructor
  · positivity
  · nlinarith [div_pos he hK0]

/-- A strictly enlarged cover multiplier retains the exact quadratic mass margin. -/
theorem exists_enlarged_concentration_multiplier {θ K e : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hK : 1 ≤ K) (he : 0 < e)
    (hsharp : 12 * K * e < θ) :
    ∃ D : ℝ, 3 / (θ * (e / K)) < D ∧ 1 < D ∧
      1 < (2 * e) * D ∧ (2 * e) ^ 2 * D < 1 := by
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hr := concentration_level_mem_Ioo hθ hθ1 hK he hsharp
  have hβ : 0 < 2 * e := by positivity
  have hb2 : 0 < (2 * e) ^ 2 := sq_pos_of_pos hβ
  have hbase : (2 * e) ^ 2 * (3 / (θ * (e / K))) = 12 * K * e / θ := by
    field_simp [hθ.ne', hK0.ne', he.ne']
    <;> ring
  have hmargin : (2 * e) ^ 2 * (3 / (θ * (e / K))) < 1 := by
    rw [hbase]
    exact (div_lt_one hθ).mpr hsharp
  have hupper : 3 / (θ * (e / K)) < 1 / (2 * e) ^ 2 := by
    apply (lt_div_iff₀ hb2).mpr
    simpa only [mul_comm] using hmargin
  obtain ⟨D, hD, hDu⟩ := exists_between hupper
  have hD₀ : 1 < 3 / (θ * (e / K)) := (lt_div_iff₀ hr.1).mpr (by linarith [hr.2])
  have hbbase : (2 * e) * (3 / (θ * (e / K))) = 6 * K / θ := by
    field_simp [hθ.ne', hK0.ne', he.ne']
    <;> ring
  have hbD₀ : 1 < (2 * e) * (3 / (θ * (e / K))) := by
    rw [hbbase]
    apply (lt_div_iff₀ hθ).mpr
    linarith
  refine ⟨D, hD, hD₀.trans hD, hbD₀.trans (mul_lt_mul_of_pos_left hD hβ), ?_⟩
  have h := (lt_div_iff₀ hb2).mp hDu
  simpa only [mul_comm] using h

end LpSelfSimilar.SelfSimilar.Concentration
