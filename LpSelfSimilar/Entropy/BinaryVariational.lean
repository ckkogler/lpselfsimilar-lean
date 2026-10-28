module

public import LpSelfSimilar.Entropy.FiniteVariational
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

@[expose] public section

/-!
# The exact binary entropy variational identity

For every real t, binary entropy plus t times the success probability has
maximum log(1+exp(t)) on [0,1], attained at exp(t)/(1+exp(t)). The proof uses
the already established finite Gibbs bound and then evaluates the actual
maximizer. Zero and unit probabilities are included in the upper bound.
The specialization to log(15)-alpha*(13/40)*log(2) retains the exact factor
15 and exponent in the sixteen-atom cancellation estimate.
-/

open Real Set
open scoped BigOperators

namespace LpSelfSimilar.Entropy

/-- The binary Gibbs bound, including both endpoint probabilities. -/
theorem binEntropy_add_mul_le_log_one_add_exp {p : ℝ} (hp : p ∈ Icc 0 1) (t : ℝ) :
    binEntropy p + t * p ≤ log (1 + exp t) := by
  have h := finite_entropy_le_log_partition (Finset.univ : Finset Bool)
    (fun b => if b then p else 1 - p) (fun b => if b then exp t else 1)
    (by intro b hb; cases b <;> simp <;> linarith [hp.1, hp.2])
    (by simp)
    (by intro b hb; cases b <;> simp [Real.exp_pos])
    (Z := 1 + exp t) (by positivity) (by simp [add_comm])
  simp at h
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  linarith

/-- The exact maximizing probability is strictly between zero and one. -/
theorem binary_variational_maximizer_mem (t : ℝ) : exp t / (1 + exp t) ∈ Ioo 0 1 := by
  constructor
  · positivity
  · exact (div_lt_one (by positivity)).mpr (by linarith)

/-- Direct evaluation attains the binary variational upper bound. -/
theorem binEntropy_variational_maximizer_value (t : ℝ) :
    binEntropy (exp t / (1 + exp t)) + t * (exp t / (1 + exp t)) =
      log (1 + exp t) := by
  have he : 1 - exp t / (1 + exp t) = 1 / (1 + exp t) := by field_simp; ring
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub, he]
  simp only [negMulLog, log_div (exp_pos t).ne' (by positivity : 1 + exp t ≠ 0),
    log_exp, log_div (by norm_num : (1 : ℝ) ≠ 0) (by positivity : 1 + exp t ≠ 0), log_one]
  field_simp
  ring

/-- The maximum is attained, not just a formal upper bound for a supremum. -/
theorem binEntropy_variational_isGreatest (t : ℝ) :
    IsGreatest ((fun p : ℝ => binEntropy p + t * p) '' Icc 0 1) (log (1 + exp t)) := by
  refine ⟨⟨exp t / (1 + exp t), ?_, binEntropy_variational_maximizer_value t⟩, ?_⟩
  · exact ⟨(binary_variational_maximizer_mem t).1.le, (binary_variational_maximizer_mem t).2.le⟩
  · rintro z ⟨p, hp, rfl⟩
    exact binEntropy_add_mul_le_log_one_add_exp hp t

/-- The exact binary variational supremum. -/
theorem binEntropy_variational_sup (t : ℝ) :
    sSup ((fun p : ℝ => binEntropy p + t * p) '' Icc 0 1) = log (1 + exp t) :=
  (binEntropy_variational_isGreatest t).csSup_eq

/-- The paper's binary-entropy expression, in bits, with exact factor 15 and 13/40 exponent. -/
theorem binary_entropy_sixteen_variational_bound {p : ℝ} (hp : p ∈ Icc 0 1) (α : ℝ) :
    binEntropy p / log 2 + p * (log 15 / log 2) - α * (13 / 40) * p ≤
      log (1 + 15 * (2 : ℝ) ^ (-α * (13 / 40))) / log 2 := by
  have h := binEntropy_add_mul_le_log_one_add_exp hp (log 15 - α * (13 / 40) * log 2)
  have he : exp (log 15 - α * (13 / 40) * log 2) =
      15 * (2 : ℝ) ^ (-α * (13 / 40)) := by
    rw [sub_eq_add_neg, exp_add, exp_log (by norm_num : (0 : ℝ) < 15),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    congr 1
    ring
  rw [he] at h
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  convert! h using 1 <;> field_simp <;> ring

end LpSelfSimilar.Entropy
