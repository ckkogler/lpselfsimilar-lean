module

public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Data.ENNReal.BigOperators

@[expose] public section

/-!
# Real probability vectors as actual probability laws

A nonnegative real vector of total mass one defines a PMF on its finite label
space. Mapping the labels to real locations merges any repeated atoms and gives
an actual probability measure. Its Bochner integral is the original weighted
finite sum, so later Fourier estimates concern these measures directly.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace LpSelfSimilar.FiniteProbability

/-- The PMF determined by an ordinary finite nonnegative real probability vector. -/
noncomputable def realVectorPMF {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) : PMF ι :=
  PMF.ofFintype (fun i ↦ ENNReal.ofReal (p i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ hp i), hsum]
    simp)

/-- The constructed PMF has exactly the requested atom weights. -/
theorem realVectorPMF_apply {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (i : ι) :
    realVectorPMF p hp hsum i = ENNReal.ofReal (p i) := rfl

/-- Converting a constructed atom mass back to real numbers recovers the original weight. -/
theorem realVectorPMF_toReal {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (i : ι) :
    (realVectorPMF p hp hsum i).toReal = p i := by
  rw [realVectorPMF_apply, ENNReal.toReal_ofReal (hp i)]

/-- The actual real measure obtained by mapping finite probability labels to their locations. -/
noncomputable def realVectorLaw {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (z : ι → ℝ) : Measure ℝ :=
  ((realVectorPMF p hp hsum).map z).toMeasure

instance realVectorLaw_isProbabilityMeasure {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (z : ι → ℝ) :
    IsProbabilityMeasure (realVectorLaw p hp hsum z) := by
  unfold realVectorLaw
  infer_instance

/-- The mapped law has total mass exactly one. -/
theorem realVectorLaw_univ {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (z : ι → ℝ) :
    realVectorLaw p hp hsum z Set.univ = 1 := measure_univ

/-- A measurable set receives exactly the sum of its atom weights, including collisions. -/
theorem realVectorLaw_apply {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (z : ι → ℝ)
    (s : Set ℝ) (hs : MeasurableSet s) :
    realVectorLaw p hp hsum z s = ∑ i, s.indicator (fun _ ↦ ENNReal.ofReal (p i)) (z i) := by
  classical
  letI : MeasurableSpace ι := ⊤
  have hz : Measurable z := measurable_from_top
  unfold realVectorLaw
  rw [PMF.toMeasure_map_apply z (realVectorPMF p hp hsum) s hz hs,
    PMF.toMeasure_apply _ (hz hs), tsum_fintype]
  simp only [Set.indicator_apply, Set.mem_preimage, realVectorPMF_apply]

/-- The mapped measure is explicitly the finite sum of weighted point masses. -/
theorem realVectorLaw_eq_sum_dirac {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (z : ι → ℝ) :
    realVectorLaw p hp hsum z = ∑ i, ENNReal.ofReal (p i) • Measure.dirac (z i) := by
  classical
  ext s hs
  rw [realVectorLaw_apply p hp hsum z s hs]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Measure.dirac_apply' _ hs, Set.indicator_apply]

/-- Integration against the actual mapped law equals the finite weighted Bochner sum. -/
theorem integral_realVectorLaw {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (z : ι → ℝ)
    (f : ℝ → E) (hf : StronglyMeasurable f) :
    (∫ x, f x ∂realVectorLaw p hp hsum z) = ∑ i, p i • f (z i) := by
  letI : MeasurableSpace ι := ⊤
  have hz : Measurable z := measurable_from_top
  unfold realVectorLaw
  rw [← PMF.toMeasure_map z (realVectorPMF p hp hsum) hz, integral_map hz.aemeasurable hf.aestronglyMeasurable,
    PMF.integral_eq_sum]
  simp only [realVectorPMF_toReal]

end LpSelfSimilar.FiniteProbability
