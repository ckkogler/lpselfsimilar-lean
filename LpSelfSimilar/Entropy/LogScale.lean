module

public import LpSelfSimilar.Entropy.EntropyVariance
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
Entropy and conditional variance on logarithmic scales. All scale functions are
measurable and locally integrable; this permits telescoping entropy increments
inside actual integrals rather than using an assumed regularity statement.
-/

open MeasureTheory Set Real

namespace LpSelfSimilar.Entropy

lemma measurable_gridEntropy (p : PMF ℝ) (hp : p.support.Finite) :
    Measurable (gridEntropy p hp) :=
  (measurable_gridEntropyAt p hp).stronglyMeasurable.integral_prod_right'.measurable

lemma measurable_scaleVariance (p : PMF ℝ) (hp : p.support.Finite) :
    Measurable (scaleVariance p hp) :=
  (measurable_gridVarianceAt p hp).stronglyMeasurable.integral_prod_right'.measurable

lemma gridEntropy_nonneg (p : PMF ℝ) (hp : p.support.Finite) (s : ℝ) :
    0 ≤ gridEntropy p hp s := integral_nonneg (gridEntropyAt_nonneg p hp s)

lemma gridEntropy_le_finiteEntropy (p : PMF ℝ) (hp : p.support.Finite) (s : ℝ) :
    gridEntropy p hp s ≤ finiteEntropy p hp := by
  have h := integral_mono (integrable_gridEntropyAt p hp s)
    (integrable_const (finiteEntropy p hp)) (gridEntropyAt_le p hp s)
  simpa [gridEntropy] using h

noncomputable def entropyOnLogScale (p : PMF ℝ) (hp : p.support.Finite) (x : ℝ) : ℝ :=
  gridEntropy p hp (Real.exp (-x))

noncomputable def varianceOnLogScale (p : PMF ℝ) (hp : p.support.Finite) (x : ℝ) : ℝ :=
  scaleVariance p hp (Real.exp (-x))

@[fun_prop] lemma measurable_entropyOnLogScale (p : PMF ℝ) (hp : p.support.Finite) :
    Measurable (entropyOnLogScale p hp) :=
  (measurable_gridEntropy p hp).comp (by fun_prop)

@[fun_prop] lemma measurable_varianceOnLogScale (p : PMF ℝ) (hp : p.support.Finite) :
    Measurable (varianceOnLogScale p hp) :=
  (measurable_scaleVariance p hp).comp (by fun_prop)

lemma intervalIntegrable_entropyOnLogScale (p : PMF ℝ) (hp : p.support.Finite) (a b : ℝ) :
    IntervalIntegrable (entropyOnLogScale p hp) volume a b := by
  apply IntervalIntegrable.mono_fun (intervalIntegrable_const (c := finiteEntropy p hp))
    (measurable_entropyOnLogScale p hp).aestronglyMeasurable
  apply ae_of_all
  intro x
  change ‖gridEntropy p hp (Real.exp (-x))‖ ≤ ‖finiteEntropy p hp‖
  rw [Real.norm_eq_abs, abs_of_nonneg (gridEntropy_nonneg p hp _),
    Real.norm_eq_abs, abs_of_nonneg (finiteEntropy_nonneg p hp)]
  exact gridEntropy_le_finiteEntropy p hp _

lemma intervalIntegrable_varianceOnLogScale (p : PMF ℝ) (hp : p.support.Finite) (a b : ℝ) :
    IntervalIntegrable (varianceOnLogScale p hp) volume a b := by
  apply IntervalIntegrable.mono_fun (intervalIntegrable_const (c := (1 : ℝ)))
    (measurable_varianceOnLogScale p hp).aestronglyMeasurable
  apply ae_of_all
  intro x
  change ‖scaleVariance p hp (Real.exp (-x))‖ ≤ ‖(1 : ℝ)‖
  rw [Real.norm_eq_abs, abs_of_nonneg (scaleVariance_nonneg p hp _)]
  simpa only [norm_one] using scaleVariance_le_one p hp (Real.exp_pos (-x))

lemma entropyOnLogScale_increment (p : PMF ℝ) (hp : p.support.Finite) (x : ℝ) :
    entropyOnLogScale p hp (x + Real.log 4) - entropyOnLogScale p hp x ≤
      10 * Real.sqrt (Real.sqrt (varianceOnLogScale p hp x)) := by
  have he : Real.exp (-(x + Real.log 4)) = Real.exp (-x) / 4 := by
    rw [neg_add, Real.exp_add, Real.exp_neg (Real.log 4), Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    ring
  unfold entropyOnLogScale varianceOnLogScale
  rw [he]
  exact gridEntropy_increment_le_ten_fourthRoot_scaleVariance p hp (Real.exp_pos _)

end LpSelfSimilar.Entropy
