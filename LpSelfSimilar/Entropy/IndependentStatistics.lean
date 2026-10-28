module

public import LpSelfSimilar.Probability.PairStatistics
public import LpSelfSimilar.Entropy.ChainRule
public import LpSelfSimilar.Entropy.Bounds

@[expose] public section

/-!
# Entropy of statistics of independent finite inputs

Separate statistics have additive joint entropy, including collisions and
zero-probability input atoms. Any deterministic combination consequently has
entropy at most the sum of the two statistic entropies. The statistic codomains
need not be finite; the actual finite supports are supplied by the input maps.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LpSelfSimilar.Entropy

/-- The real masses of a finite PMF sum to one. -/
theorem sum_fintype_toReal {ι : Type*} [Fintype ι] (p : PMF ι) :
    ∑ i, (p i).toReal = 1 := by
  have h := congrArg ENNReal.toReal p.tsum_coe
  simpa only [tsum_fintype, ENNReal.toReal_sum (fun i _ => p.apply_ne_top i),
    ENNReal.toReal_one] using h

/-- Entropy of a statistic as a sum of marginal self-information over every finite input. -/
theorem finiteEntropy_map_eq_sum_fintype {ι A : Type*} [Fintype ι] (p : PMF ι) (X : ι → A) :
    finiteEntropy (p.map X) (by simpa using (Set.toFinite p.support).image X) =
      ∑ i, -(p i).toReal * Real.log ((p.map X) (X i)).toReal := by
  classical
  rw [finiteEntropy_map_eq_sum_log_marginal p (Set.toFinite _) X]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  have hz : p i = 0 := by simpa using hi
  simp [hz]

/-- Joint entropy adds for independent statistics, even if either statistic has collisions. -/
theorem finiteEntropy_independent_pair {ι κ A B : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (p : PMF ι) (q : PMF κ) (X : ι → A) (Y : κ → B) :
    finiteEntropy ((pairPMF p q).map (fun z => (X z.1, Y z.2)))
      (by simpa using (Set.toFinite (pairPMF p q).support).image (fun z => (X z.1, Y z.2))) =
      finiteEntropy (p.map X) (by simpa using (Set.toFinite p.support).image X) +
      finiteEntropy (q.map Y) (by simpa using (Set.toFinite q.support).image Y) := by
  classical
  rw [finiteEntropy_map_eq_sum_fintype, finiteEntropy_map_eq_sum_fintype,
    finiteEntropy_map_eq_sum_fintype]
  simp only [Fintype.sum_prod_type, pairPMF_apply, pairPMF_map_pair_apply, ENNReal.toReal_mul]
  have hterm (i : ι) (j : κ) :
      -((p i).toReal * (q j).toReal) *
          Real.log (((p.map X) (X i)).toReal * ((q.map Y) (Y j)).toReal) =
        (q j).toReal * (-(p i).toReal * Real.log ((p.map X) (X i)).toReal) +
        (p i).toReal * (-(q j).toReal * Real.log ((q.map Y) (Y j)).toReal) := by
    by_cases hp : p i = 0
    · simp [hp]
    by_cases hq : q j = 0
    · simp [hq]
    have hp0 := (ENNReal.toReal_pos hp (p.apply_ne_top i)).trans_le
      (atom_toReal_le_marginal p (Set.toFinite _) X i)
    have hq0 := (ENNReal.toReal_pos hq (q.apply_ne_top j)).trans_le
      (atom_toReal_le_marginal q (Set.toFinite _) Y j)
    rw [Real.log_mul hp0.ne' hq0.ne']
    ring
  simp_rw [hterm, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    sum_fintype_toReal, one_mul]
  rw [← Finset.sum_mul, sum_fintype_toReal, one_mul]

/-- Combining two independent statistics cannot exceed their summed entropy. -/
theorem finiteEntropy_independent_combine_le {ι κ A B E : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (p : PMF ι) (q : PMF κ) (X : ι → A) (Y : κ → B) (F : A × B → E) :
    finiteEntropy ((pairPMF p q).map (fun z => F (X z.1, Y z.2)))
      (by simpa using (Set.toFinite (pairPMF p q).support).image (fun z => F (X z.1, Y z.2))) ≤
      finiteEntropy (p.map X) (by simpa using (Set.toFinite p.support).image X) +
      finiteEntropy (q.map Y) (by simpa using (Set.toFinite q.support).image Y) := by
  have h := finiteEntropy_map_le ((pairPMF p q).map (fun z => (X z.1, Y z.2)))
    (by simpa using (Set.toFinite (pairPMF p q).support).image (fun z => (X z.1, Y z.2))) F
  rw [finiteEntropy_independent_pair] at h
  simpa only [PMF.map_comp, Function.comp_def] using h

end LpSelfSimilar.Entropy
