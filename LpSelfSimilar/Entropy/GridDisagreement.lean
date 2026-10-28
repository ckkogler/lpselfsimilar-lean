module

public import LpSelfSimilar.Entropy.Grid
public import LpSelfSimilar.Entropy.CollisionLaw
public import LpSelfSimilar.Probability.FiniteIntegration
public import LpSelfSimilar.Analysis.RandomGrid

@[expose] public section

/-!
Averaging over a uniform grid shift bounds disagreement by the square root of
the variance. This is the collision step of Lemma 3.5, and applies to every
finitely supported law without an arithmetic or separation hypothesis.
-/

open MeasureTheory Set Real LpSelfSimilar.FiniteProbability

namespace LpSelfSimilar.Entropy

lemma integrable_indicator_quantize_ne (s x y : ℝ) :
    IntegrableOn (fun t ↦ if quantize s t x ≠ quantize s t y then (1 : ℝ) else 0)
      (Icc (0 : ℝ) 1) volume := by
  have hm : Measurable (fun t ↦ if quantize s t x ≠ quantize s t y then (1 : ℝ) else 0) := by
    apply Measurable.ite
    · exact (measurableSet_eq_fun (by unfold quantize; fun_prop)
        (by unfold quantize; fun_prop)).compl
    · exact measurable_const
    · exact measurable_const
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  exact ae_of_all _ (fun _ ↦ by split_ifs <;> norm_num)

lemma integral_indicator_quantize_ne_le {s : ℝ} (hs : 0 < s) (x y : ℝ) :
    (∫ t in Icc (0 : ℝ) 1,
      if quantize s t x ≠ quantize s t y then (1 : ℝ) else 0) ≤ |x - y| / s := by
  have h := integral_indicator_floor_ne_le (x / s) (y / s)
  rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc,
    ← sub_div, abs_div, abs_of_pos hs] at h
  exact h

lemma integral_grid_disagreement_le (p : PMF ℝ) (hp : p.support.Finite)
    {s : ℝ} (hs : 0 < s) :
    (∫ t in Icc (0 : ℝ) 1,
      1 - collisionProbability (p.map (quantize s t)) (by simpa using hp.image (quantize s t))) ≤
      Real.sqrt (2 * FiniteProbability.variance p hp id) / s := by
  have he (t : ℝ) := disagreement_eq_expectation_ne p hp (quantize s t)
  have hex : (∫ t in Icc (0 : ℝ) 1,
      1 - collisionProbability (p.map (quantize s t)) (by simpa using hp.image (quantize s t))) =
      expectation p hp (fun x ↦ expectation p hp (fun y ↦
        ∫ t in Icc (0 : ℝ) 1, if quantize s t x ≠ quantize s t y then (1 : ℝ) else 0)) := by
    simp_rw [he]
    rw [integral_expectation p hp _ (fun x _ ↦
      integrable_expectation p hp _ (fun y _ ↦ integrable_indicator_quantize_ne s x y))]
    congr 1
    funext x
    exact integral_expectation p hp _ (fun y _ ↦ integrable_indicator_quantize_ne s x y)
  rw [hex]
  calc
    expectation p hp (fun x ↦ expectation p hp (fun y ↦
        ∫ t in Icc (0 : ℝ) 1, if quantize s t x ≠ quantize s t y then (1 : ℝ) else 0)) ≤
      expectation p hp (fun x ↦ expectation p hp (fun y ↦ |x - y| / s)) := by
        apply expectation_mono p hp
        intro x _
        apply expectation_mono p hp
        exact fun y _ ↦ integral_indicator_quantize_ne_le hs x y
    _ = expectation p hp (fun x ↦ expectation p hp (fun y ↦ |x - y|)) / s := by
      simp_rw [div_eq_mul_inv, mul_comm _ s⁻¹, expectation_const_mul]
    _ ≤ _ := div_le_div_of_nonneg_right
      (pairwise_abs_distance_le_sqrt_two_variance p hp id) hs.le

lemma integrable_grid_disagreement (p : PMF ℝ) (hp : p.support.Finite) (s : ℝ) :
    IntegrableOn (fun t ↦
      1 - collisionProbability (p.map (quantize s t)) (by simpa using hp.image (quantize s t)))
      (Icc (0 : ℝ) 1) volume := by
  simp_rw [disagreement_eq_expectation_ne p hp (quantize s _)]
  apply integrable_expectation p hp
  intro x _
  apply integrable_expectation p hp
  exact fun y _ ↦ integrable_indicator_quantize_ne s x y

end LpSelfSimilar.Entropy
