module

public import LpSelfSimilar.Entropy.FiniteCancellation
public import LpSelfSimilar.Entropy.FiniteVariational

@[expose] public section

/-!
# The sixteen-atom entropy/cancellation inequality

Entropy is measured in bits here. The parameter in the exponential comparison
law is `alpha * (13/40) * log 2`, so conversion from natural logarithms retains
the exact exponent `-alpha * (13/40)` and the factor fifteen.
-/

open scoped BigOperators

namespace LpSelfSimilar.Entropy

/-- The finite cancellation functional, with its exact phase-averaging constants. -/
noncomputable def finiteCancellation {ι : Type*} (s : Finset ι) (p : ι → ℝ) : ℝ :=
  1 - Real.sqrt (2 / 5 + (3 / 5) * ∑ j ∈ s, (p j) ^ 2)

/-- Entropy in bits of a probability vector on at most sixteen points is bounded
by its cancellation, with the sharp constants used in the cubic criterion. -/
theorem sixteen_atom_entropy_le_cancellation {ι : Type*}
    (s : Finset ι) (p : ι → ℝ) (hp : ∀ j ∈ s, 0 ≤ p j)
    (hsum : ∑ j ∈ s, p j = 1) (hcard : s.card ≤ 16)
    {α : ℝ} (hα : 0 < α) :
    (∑ j ∈ s, Real.negMulLog (p j)) / Real.log 2 ≤
      α * finiteCancellation s p +
        Real.log (1 + 15 * (2 : ℝ) ^ (-α * (13 / 40 : ℝ))) / Real.log 2 := by
  classical
  have hsne : s.Nonempty := by
    by_contra h
    have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [he] at hsum
  obtain ⟨i, hi, hmax⟩ := s.exists_max_image p hsne
  have hc : (s.erase i).card ≤ 15 := by
    have he := Finset.card_erase_add_one hi
    omega
  have hv := finite_entropy_le_dominant_atom_bound s p i hi hp hsum 15 hc
    (α * (13 / 40 : ℝ) * Real.log 2)
  have ha := finite_cancellation_ge_mass_outside_max s p i hi hp hsum hmax
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpowers : (2 : ℝ) ^ (-α * (13 / 40 : ℝ)) =
      Real.exp (-(α * (13 / 40 : ℝ) * Real.log 2)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [← hpowers] at hv
  have hm := mul_le_mul_of_nonneg_left ha (mul_nonneg hα.le hl.le)
  apply (div_le_iff₀ hl).mpr
  dsimp [finiteCancellation] at *
  have hclear := div_mul_cancel₀
    (Real.log (1 + 15 * (2 : ℝ) ^ (-α * (13 / 40 : ℝ)))) hl.ne'
  nlinarith

/-- The specialized entropy bound with `t = log (150 J)`, including the exact
remainder and its upper bound. -/
theorem sixteen_atom_entropy_le_cancellation_log_parameter {ι : Type*}
    (s : Finset ι) (p : ι → ℝ) (hp : ∀ j ∈ s, 0 ≤ p j)
    (hsum : ∑ j ∈ s, p j = 1) (hcard : s.card ≤ 16)
    {J : ℝ} (hJ : 3 ≤ J) :
    (∑ j ∈ s, Real.negMulLog (p j)) / Real.log 2 ≤
      (Real.log (150 * J) / ((13 / 40 : ℝ) * Real.log 2)) * finiteCancellation s p +
        Real.log (1 + 1 / (10 * J)) / Real.log 2 ∧
      Real.log (1 + 1 / (10 * J)) / Real.log 2 ≤ 1 / (10 * J * Real.log 2) := by
  classical
  have hJ0 : 0 < J := by linarith
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht : 0 < Real.log (150 * J) := Real.log_pos (by linarith)
  have hα : 0 < Real.log (150 * J) / ((13 / 40 : ℝ) * Real.log 2) := by positivity
  have hpower : (2 : ℝ) ^
      (-(Real.log (150 * J) / ((13 / 40 : ℝ) * Real.log 2)) * (13 / 40 : ℝ)) =
        1 / (150 * J) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    have he : Real.log 2 *
        (-(Real.log (150 * J) / ((13 / 40 : ℝ) * Real.log 2)) * (13 / 40 : ℝ)) =
          -Real.log (150 * J) := by field_simp
    rw [he, Real.exp_neg, Real.exp_log (by positivity), one_div]
  have hcoeff : 15 * (1 / (150 * J)) = 1 / (10 * J) := by field_simp; ring
  constructor
  · have h := sixteen_atom_entropy_le_cancellation s p hp hsum hcard hα
    simpa only [hpower, hcoeff] using h
  · have h := Real.log_le_sub_one_of_pos
      (by positivity : 0 < 1 + 1 / (10 * J))
    apply (div_le_iff₀ hl).mpr
    have he : 1 / (10 * J * Real.log 2) * Real.log 2 = 1 / (10 * J) := by
      field_simp
    rw [he]
    linarith

end LpSelfSimilar.Entropy
