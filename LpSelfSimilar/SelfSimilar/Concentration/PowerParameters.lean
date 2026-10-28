module

public import LpSelfSimilar.SelfSimilar.Concentration.Parameters
public import LpSelfSimilar.Analysis.MassDecayExponent

@[expose] public section

/-!
# Exact parameters of the concentration power exponent

The stopped-cover constants satisfy beta*D0=6*K/theta and
beta^2*D0=12*K*e/theta. These identities place the logarithmic exponent
strictly between one half and one under the stated sharp hypothesis.
-/

open Set
open LpSelfSimilar.Analysis

namespace LpSelfSimilar.SelfSimilar.Concentration

/-- The mass factor times the cover multiplier is exactly 6*K/theta. -/
theorem concentration_mass_volume_product {θ K e : ℝ}
    (hθ : 0 < θ) (hK : 0 < K) (he : 0 < e) :
    (2 * e) * (3 / (θ * (e / K))) = 6 * K / θ := by
  field_simp [hθ.ne', hK.ne', he.ne']
  <;> ring

/-- The quadratic mass factor times the cover multiplier is exactly 12*K*e/theta. -/
theorem concentration_quadratic_volume_product {θ K e : ℝ}
    (hθ : 0 < θ) (hK : 0 < K) (he : 0 < e) :
    (2 * e) ^ 2 * (3 / (θ * (e / K))) = 12 * K * e / θ := by
  field_simp [hθ.ne', hK.ne', he.ne']
  <;> ring

/-- The stopped-cover logarithmic exponent has precisely the claimed quadratic threshold. -/
theorem half_lt_concentration_exponent_iff {θ K e : ℝ}
    (hθ : 0 < θ) (hK : 0 < K) (he : 0 < e) (hr : θ * (e / K) < 1) :
    (1 / 2 : ℝ) < massDecayExponent (2 * e) (3 / (θ * (e / K))) ↔ 12 * K * e < θ := by
  have hr0 : 0 < θ * (e / K) := mul_pos hθ (div_pos he hK)
  have hD : 1 < 3 / (θ * (e / K)) := (lt_div_iff₀ hr0).mpr (by linarith)
  rw [half_lt_massDecayExponent_iff (by positivity) hD,
    concentration_quadratic_volume_product hθ hK he, div_lt_one hθ]

/-- Under the sharp hypothesis, the mass factor contracts and the exact exponent lies in (1/2,1). -/
theorem concentration_power_parameters {θ K e : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hK : 1 ≤ K) (he : 0 < e)
    (hsharp : 12 * K * e < θ) :
    1 < 3 / (θ * (e / K)) ∧ 0 < 2 * e ∧ 2 * e < 1 ∧
      massDecayExponent (2 * e) (3 / (θ * (e / K))) ∈ Ioo (1 / 2) 1 := by
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hr := concentration_level_mem_Ioo hθ hθ1 hK he hsharp
  have hD : 1 < 3 / (θ * (e / K)) := (lt_div_iff₀ hr.1).mpr (by linarith [hr.2])
  have hβ : 0 < 2 * e := by positivity
  have hβ1 : 2 * e < 1 := by nlinarith
  have hproduct : 1 < (2 * e) * (3 / (θ * (e / K))) := by
    rw [concentration_mass_volume_product hθ hK0 he]
    apply (lt_div_iff₀ hθ).mpr
    linarith
  exact ⟨hD, hβ, hβ1, (half_lt_concentration_exponent_iff hθ hK0 he hr.2).mpr hsharp,
    (massDecayExponent_lt_one_iff hβ hD).mpr hproduct⟩

end LpSelfSimilar.SelfSimilar.Concentration
