module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic

@[expose] public section

/-!
# Convergent Gram forms of stable linear orbits

An explicit geometric bound on powers of a continuous linear operator makes
the orbit-observation Gram series absolutely summable. Shifting the series
gives its rank-one defect identity. Positivity is strict when the observations
separate vectors. These are reusable analytic inputs; the contracting-conjugate
construction must prove stability and separation for its actual operator.
-/

open scoped InnerProductSpace

namespace LpSelfSimilar.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An explicit geometric operator-norm bound, allowing a prefactor for non-normal operators. -/
def HasGeometricPowerBound (A : E →L[ℝ] E) : Prop :=
  ∃ C r : ℝ, 0 ≤ C ∧ 0 ≤ r ∧ r < 1 ∧ ∀ n : ℕ, ‖A ^ n‖ ≤ C * r ^ n

/-- Every strict operator-norm contraction has such a bound with prefactor one. -/
theorem hasGeometricPowerBound_of_norm_lt_one {A : E →L[ℝ] E} (hA : ‖A‖ < 1) :
    HasGeometricPowerBound A := by
  refine ⟨1, ‖A‖, by norm_num, norm_nonneg _, hA, ?_⟩
  intro n
  cases n with
  | zero => simpa only [pow_zero, one_mul, ContinuousLinearMap.one_def] using (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E))
  | succ n => simpa only [one_mul] using norm_pow_le' A (Nat.succ_pos n)

/-- The orbit Gram series is defined independently of any chosen decay certificate. -/
noncomputable def stableOrbitGram (A : E →L[ℝ] E) (v x y : E) : ℝ :=
  ∑' n : ℕ, ⟪(A ^ n) x, v⟫_ℝ * ⟪(A ^ n) y, v⟫_ℝ

theorem abs_orbit_inner_le {A : E →L[ℝ] E} {C r : ℝ}
    (hpow : ∀ n : ℕ, ‖A ^ n‖ ≤ C * r ^ n) (v x : E) (n : ℕ) :
    |⟪(A ^ n) x, v⟫_ℝ| ≤ C * ‖x‖ * ‖v‖ * r ^ n := by
  calc
    _ ≤ ‖(A ^ n) x‖ * ‖v‖ := abs_real_inner_le_norm _ _
    _ ≤ (‖A ^ n‖ * ‖x‖) * ‖v‖ := by gcongr; exact (A ^ n).le_opNorm x
    _ ≤ ((C * r ^ n) * ‖x‖) * ‖v‖ := by gcongr; exact hpow n
    _ = _ := by ring

/-- Absolute summability follows from a geometric majorant of ratio r squared. -/
theorem summable_stableOrbitGram {A : E →L[ℝ] E} (hA : HasGeometricPowerBound A)
    (v x y : E) : Summable (fun n : ℕ => ⟪(A ^ n) x, v⟫_ℝ * ⟪(A ^ n) y, v⟫_ℝ) := by
  obtain ⟨C, r, hC, hr, hr1, hpow⟩ := hA
  have hrsq : r ^ 2 < 1 := by nlinarith
  have hs := (summable_geometric_of_lt_one (sq_nonneg r) hrsq).mul_left
    (C ^ 2 * ‖x‖ * ‖y‖ * ‖v‖ ^ 2)
  apply hs.of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_mul]
  calc
    _ ≤ (C * ‖x‖ * ‖v‖ * r ^ n) * (C * ‖y‖ * ‖v‖ * r ^ n) :=
      mul_le_mul (abs_orbit_inner_le hpow v x n) (abs_orbit_inner_le hpow v y n)
        (abs_nonneg _) (by positivity)
    _ = (C ^ 2 * ‖x‖ * ‖y‖ * ‖v‖ ^ 2) * (r ^ 2) ^ n := by
      rw [pow_two r, mul_pow]
      ring

theorem stableOrbitGram_symm (A : E →L[ℝ] E) (v x y : E) :
    stableOrbitGram A v x y = stableOrbitGram A v y x := by
  unfold stableOrbitGram
  apply tsum_congr
  intro n
  ring

theorem stableOrbitGram_nonneg (A : E →L[ℝ] E) (v x : E) :
    0 ≤ stableOrbitGram A v x x :=
  tsum_nonneg (fun n => mul_self_nonneg _)

/-- Removing the initial observation gives exactly the rank-one bilinear defect. -/
theorem stableOrbitGram_apply_apply {A : E →L[ℝ] E} (hA : HasGeometricPowerBound A)
    (v x y : E) :
    stableOrbitGram A v (A x) (A y) = stableOrbitGram A v x y - ⟪x, v⟫_ℝ * ⟪y, v⟫_ℝ := by
  have h := (summable_stableOrbitGram hA v x y).tsum_eq_zero_add
  have hshift (n : ℕ) (z : E) : (A ^ n) (A z) = (A ^ (n + 1)) z := by
    rw [pow_succ]
    rfl
  unfold stableOrbitGram
  simp only [pow_zero, one_apply_eq_self] at h
  simp_rw [hshift]
  linarith

/-- Nonzero vectors have positive Gram energy if their observations cannot all vanish. -/
theorem stableOrbitGram_pos {A : E →L[ℝ] E} (hA : HasGeometricPowerBound A) (v : E)
    (hsep : ∀ x : E, (∀ n : ℕ, ⟪(A ^ n) x, v⟫_ℝ = 0) → x = 0)
    {x : E} (hx : x ≠ 0) : 0 < stableOrbitGram A v x x := by
  have hex : ∃ n : ℕ, ⟪(A ^ n) x, v⟫_ℝ ≠ 0 := by
    by_contra! h
    exact hx (hsep x h)
  obtain ⟨n, hn⟩ := hex
  exact (summable_stableOrbitGram hA v x x).tsum_pos
    (fun k => mul_self_nonneg _) n (mul_self_pos.mpr hn)

end LpSelfSimilar.Analysis
