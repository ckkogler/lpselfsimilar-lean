module

public import LpSelfSimilar.Bernoulli.WordPolynomial
public import LpSelfSimilar.Bernoulli.FiniteLaw
public import LpSelfSimilar.Entropy.Finite
public import LpSelfSimilar.Algebraic.Units

@[expose] public section

/-!
The elementary non-unit entropy argument for general algebraic parameters.

A nonzero polynomial with coefficients in {-1,0,1} has leading coefficient
plus or minus one, so each of its roots is integral. Reversing the polynomial
proves integrality of the inverse of every nonzero root. A collision of distinct
Bernoulli words therefore makes the parameter an algebraic unit. Outside that
case the actual digit law has exactly length*log(2) entropy.
-/

open Polynomial LpSelfSimilar.Bernoulli LpSelfSimilar.Entropy

namespace LpSelfSimilar.Algebraic

theorem digitSum_injective_of_not_isAlgebraicUnit {x : ℝ} (hx0 : x ≠ 0)
    (hx : ¬ IsAlgebraicUnit x) (n : ℕ) :
    Function.Injective (digitSum x (n := n)) := by
  intro u v huv
  by_contra hne
  apply hx
  apply isAlgebraicUnit_of_height_one_polynomial hx0 (differencePolynomial_ne_zero hne)
    (differencePolynomial_coeff_abs_le u v)
  have h := digitSum_sub_eq_two_mul_aeval x u v
  rw [huv, sub_self] at h
  linarith

/-- The actual finite-digit Shannon entropy in nats. This holds even without an
algebraicity assumption: every nonzero non-unit parameter has distinct words. -/
theorem digit_entropy_of_not_isAlgebraicUnit {x : ℝ} (hx0 : x ≠ 0)
    (hx : ¬ IsAlgebraicUnit x) (n : ℕ) :
    finiteEntropy (digitPMF x n) (digitPMF_support_finite _ _) = (n : ℝ) * Real.log 2 := by
  unfold digitPMF
  rw [finiteEntropy_map_of_injective _ (Set.toFinite _)
    (digitSum_injective_of_not_isAlgebraicUnit hx0 hx n), finiteEntropy_uniform]
  simp [Real.log_pow]

end LpSelfSimilar.Algebraic
