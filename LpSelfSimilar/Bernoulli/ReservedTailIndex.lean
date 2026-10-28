module

public import LpSelfSimilar.Analysis.GeometricBandShift
public import LpSelfSimilar.Analysis.LogarithmicContraction

@[expose] public section

/-!
# The actual natural starting index of the reserved tail

The target geometric band has endpoints `sqrt(2)*r/(1-epsilon)` and that
quantity divided by `theta`. The logarithmic-gap and frequency-width bounds
put the upper endpoint below one, so the exact integer ceiling is nonnegative.
Only after this proof is the shift interpreted as a natural digit index.
-/

open LpSelfSimilar.Analysis

namespace LpSelfSimilar.Bernoulli

/-- The logarithmic-gap bound gives the explicit lower bound for the parameter. -/
theorem reserved_tail_parameter_lower {θ : ℝ} (hθ0 : 0 < θ)
    (hgap : -Real.log θ ≤ 1 / 250) : (249 / 250 : ℝ) ≤ θ := by
  linarith [one_add_log_le_parameter hθ0]

/-- The upper target for the first tail coefficient is positive and below one. -/
theorem reserved_tail_upperEndpoint_bounds {θ ε r : ℝ} (hθ0 : 0 < θ)
    (hgap : -Real.log θ ≤ 1 / 250) (hε : ε ≤ 1 / 100000)
    (hr : 0 < r) (hrχ : r ≤ -Real.log θ) :
    0 < Real.sqrt 2 * r / (θ * (1 - ε)) ∧ Real.sqrt 2 * r / (θ * (1 - ε)) < 1 := by
  have hθ := reserved_tail_parameter_lower hθ0 hgap
  have hε1 : 0 < 1 - ε := by linarith
  have hs0 := Real.sqrt_nonneg (2 : ℝ)
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs1 : Real.sqrt 2 < (3 / 2 : ℝ) := by nlinarith
  have hden : (1 / 4 : ℝ) ≤ θ * (1 - ε) := by
    have hm := mul_le_mul (show (1 / 2 : ℝ) ≤ θ by linarith)
      (show (1 / 2 : ℝ) ≤ 1 - ε by linarith) (by norm_num : (0 : ℝ) ≤ 1 / 2) hθ0.le
    norm_num at hm
    exact hm
  constructor
  · positivity
  · apply (div_lt_one (mul_pos hθ0 hε1)).mpr
    have hm := mul_lt_mul_of_pos_right hs1 hr
    nlinarith

/-- Natural index at which the reserved tail first enters its geometric target band. -/
noncomputable def reservedTailStart (θ ε r : ℝ) : ℕ :=
  (geometricBandShift θ 1 (Real.sqrt 2 * r / (θ * (1 - ε)))).toNat

/-- The natural index is exactly the integer shift; no negative index is truncated. -/
theorem reservedTailStart_intCast {θ ε r : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hgap : -Real.log θ ≤ 1 / 250) (hε : ε ≤ 1 / 100000)
    (hr : 0 < r) (hrχ : r ≤ -Real.log θ) :
    (reservedTailStart θ ε r : ℤ) =
      geometricBandShift θ 1 (Real.sqrt 2 * r / (θ * (1 - ε))) := by
  have hb := reserved_tail_upperEndpoint_bounds hθ0 hgap hε hr hrχ
  exact Int.toNat_of_nonneg (geometricBandShift_nonneg hθ0 hθ1 hb.1 hb.2.le)

/-- The first actual tail coefficient has exactly the endpoints required by the Fourier argument. -/
theorem reservedTailStart_spec {θ ε r : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hgap : -Real.log θ ≤ 1 / 250) (hε : ε ≤ 1 / 100000)
    (hr : 0 < r) (hrχ : r ≤ -Real.log θ) :
    Real.sqrt 2 * r / (1 - ε) ≤ θ ^ reservedTailStart θ ε r ∧
      θ ^ reservedTailStart θ ε r ≤ Real.sqrt 2 * r / (θ * (1 - ε)) := by
  have hb := reserved_tail_upperEndpoint_bounds hθ0 hgap hε hr hrχ
  have hs := geometricBandShift_spec hθ0 hθ1 (by norm_num : (0 : ℝ) < 1) hb.1
  rw [← reservedTailStart_intCast hθ0 hθ1 hgap hε hr hrχ] at hs
  simp only [zpow_natCast, mul_one] at hs
  have he : θ * (Real.sqrt 2 * r / (θ * (1 - ε))) = Real.sqrt 2 * r / (1 - ε) := by
    field_simp
  rw [he] at hs
  exact ⟨hs.1.le, hs.2⟩

end LpSelfSimilar.Bernoulli
