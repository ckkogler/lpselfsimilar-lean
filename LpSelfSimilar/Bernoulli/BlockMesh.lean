module

public import LpSelfSimilar.Bernoulli.BlockPlacement

@[expose] public section

/-!
Power and exponential forms of the actual mesh of a placed Bernoulli block.
The two-sided comparison keeps the uniform variance loss explicit.
-/

open Real

namespace LpSelfSimilar.Bernoulli

lemma pow_eq_exp_log {l : ℝ} (hl : 0 < l) (n : ℕ) :
    l ^ n = exp (log l * n) := by
  rw [mul_comm, exp_nat_mul, exp_log hl]

lemma blockStart_power_mesh {l T v : ℝ} (hl0 : 0 < l) (hl1 : l < 1)
    (hv : v ≤ T) :
    l * exp (-T) ≤ l ^ blockStart (-log l) T v * exp (-v) ∧
      l ^ blockStart (-log l) T v * exp (-v) ≤ exp (-T) := by
  have hχ : 0 < -log l := neg_pos.mpr (log_neg hl0 hl1)
  have h := blockStart_scaled_mesh hχ hv
  simpa only [neg_neg, exp_log hl0, ← pow_eq_exp_log hl0] using h

lemma placed_mesh_variance_lower {l T v V : ℝ} (hl0 : 1 / 2 ≤ l) (hl1 : l < 1)
    (hv : v ≤ T) (hV : 0 ≤ V) :
    exp (-T) ^ 2 / 4 * V ≤
      (l ^ blockStart (-log l) T v * exp (-v)) ^ 2 * V := by
  have hl : 0 < l := by linarith
  have hm := blockStart_power_mesh hl hl1 hv
  have hlo : exp (-T) / 2 ≤ l ^ blockStart (-log l) T v * exp (-v) := by
    nlinarith [mul_le_mul_of_nonneg_right hl0 (exp_pos (-T)).le]
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ exp (-T) / 2) hlo 2
  apply mul_le_mul_of_nonneg_right _ hV
  nlinarith

end LpSelfSimilar.Bernoulli
