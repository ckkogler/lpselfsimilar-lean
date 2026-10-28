module

public import LpSelfSimilar.Bernoulli.DigitEntropySubadditivity

@[expose] public section

/-!
# The limiting Bernoulli digit entropy rate

Subadditivity and nonnegativity of the actual finite entropies justify Fekete's
limit. The rate is defined by that proved construction, and every finite word
entropy dominates its length times the rate. Conversely, any bound valid at
every finite length passes to the rate. No entropy limit is assumed.
-/

open Set Filter
open scoped Topology

namespace LpSelfSimilar.Bernoulli

/-- The limiting entropy per signed digit, in natural logarithms. -/
noncomputable def entropyRate (r : ℝ) : ℝ := (digitEntropy_subadditive r).lim

/-- The normalized actual entropies have a genuine finite lower bound. -/
theorem digitEntropy_div_bddBelow (r : ℝ) : BddBelow (range (fun n : ℕ => digitEntropy r n / (n : ℝ))) :=
  ⟨0, by rintro _ ⟨n, rfl⟩; exact digitEntropy_div_nonneg r n⟩

/-- The rate is the infimum over positive finite word lengths. -/
theorem entropyRate_eq_sInf (r : ℝ) :
    entropyRate r = sInf ((fun n : ℕ => digitEntropy r n / (n : ℝ)) '' Ici 1) := by
  rw [entropyRate, Subadditive.lim]

/-- Fekete's theorem proves convergence to the stated entropy rate. -/
theorem tendsto_digitEntropy_div (r : ℝ) :
    Tendsto (fun n : ℕ => digitEntropy r n / (n : ℝ)) atTop (𝓝 (entropyRate r)) :=
  (digitEntropy_subadditive r).tendsto_lim (digitEntropy_div_bddBelow r)

/-- The actual limiting entropy rate is nonnegative. -/
theorem entropyRate_nonneg (r : ℝ) : 0 ≤ entropyRate r :=
  ge_of_tendsto (tendsto_digitEntropy_div r) (Eventually.of_forall (digitEntropy_div_nonneg r))

/-- No entropy rate exceeds one fair binary digit per symbol. -/
theorem entropyRate_le_log_two (r : ℝ) : entropyRate r ≤ Real.log 2 := by
  have h : entropyRate r ≤ digitEntropy r 1 := by
    simpa only [entropyRate, Nat.cast_one, div_one] using
      (digitEntropy_subadditive r).lim_le_div (digitEntropy_div_bddBelow r) (n := 1) (by decide)
  exact h.trans (by simpa using digitEntropy_le_length_log_two r 1)

/-- Every finite entropy is at least its length times the limiting entropy rate. -/
theorem mul_entropyRate_le_digitEntropy (r : ℝ) (n : ℕ) :
    (n : ℝ) * entropyRate r ≤ digitEntropy r n := by
  rcases n with _ | n
  · simp [digitEntropy_zero]
  · have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    have h := (digitEntropy_subadditive r).lim_le_div (digitEntropy_div_bddBelow r)
      (n := n + 1) (by omega)
    have h' := (le_div_iff₀ hn).mp h
    simpa only [entropyRate, mul_comm] using h'

/-- A lower bound at every finite length passes to the actual rate. -/
theorem le_entropyRate_of_mul_le (r : ℝ) {c : ℝ}
    (hbound : ∀ n : ℕ, (n : ℝ) * c ≤ digitEntropy r n) : c ≤ entropyRate r := by
  apply ge_of_tendsto (tendsto_digitEntropy_div r)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (zero_lt_one.trans_le hn)
  apply (le_div_iff₀ hn0).mpr
  simpa only [mul_comm] using hbound n

/-- A linear finite-entropy sequence has exactly its slope as entropy rate. -/
theorem entropyRate_eq_of_digitEntropy_eq (r : ℝ) {c : ℝ}
    (heq : ∀ n : ℕ, digitEntropy r n = (n : ℝ) * c) : entropyRate r = c := by
  apply le_antisymm
  · have h := mul_entropyRate_le_digitEntropy r 1
    simpa only [Nat.cast_one, one_mul, heq 1] using h
  · exact le_entropyRate_of_mul_le r (fun n => (heq n).ge)

end LpSelfSimilar.Bernoulli
