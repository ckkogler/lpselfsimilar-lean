module

public import LpSelfSimilar.Entropy.ChainRule
public import LpSelfSimilar.Entropy.InjectiveSupport
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-!
Shifted-grid quantization and scale entropy of finite real laws. Scale entropy
is the integral over a uniform shift in `[0,1]`, exactly as in Section 3. The
integrand is proved measurable and bounded by the original finite entropy.
-/

open MeasureTheory Set Real
open scoped ENNReal Classical

namespace LpSelfSimilar.Entropy

/-- Quantization at scale `s` and shift `t`. Analytic assertions use `s > 0`. -/
noncomputable def quantize (s t x : ℝ) : ℤ := ⌊x / s + t⌋

/-- Entropy at a fixed shift of the grid. -/
noncomputable def gridEntropyAt (p : PMF ℝ) (hp : p.support.Finite) (s t : ℝ) : ℝ :=
  finiteEntropy (p.map (quantize s t)) (by simpa using hp.image (quantize s t))

/-- The scale entropy `H(X;s)`, averaged over one unit of the shift. -/
noncomputable def gridEntropy (p : PMF ℝ) (hp : p.support.Finite) (s : ℝ) : ℝ :=
  ∫ t in Icc (0 : ℝ) 1, gridEntropyAt p hp s t

lemma gridEntropyAt_nonneg (p : PMF ℝ) (hp : p.support.Finite) (s t : ℝ) :
    0 ≤ gridEntropyAt p hp s t := finiteEntropy_nonneg _ _

lemma gridEntropyAt_le (p : PMF ℝ) (hp : p.support.Finite) (s t : ℝ) :
    gridEntropyAt p hp s t ≤ finiteEntropy p hp := finiteEntropy_map_le p hp _

@[fun_prop] lemma measurable_quantize_joint :
    Measurable (fun p : ℝ × ℝ × ℝ ↦ quantize p.1 p.2.1 p.2.2) := by
  unfold quantize
  fun_prop

lemma measurable_gridEntropyAt (p : PMF ℝ) (hp : p.support.Finite) :
    Measurable (fun q : ℝ × ℝ ↦ gridEntropyAt p hp q.1 q.2) := by
  have he (q : ℝ × ℝ) : gridEntropyAt p hp q.1 q.2 =
      ∑ a ∈ hp.toFinset, -(p a).toReal * Real.log
        (∑ b ∈ hp.toFinset, if quantize q.1 q.2 b = quantize q.1 q.2 a then
          (p b).toReal else 0) := by
    rw [gridEntropyAt, finiteEntropy_map_eq_sum_log_marginal p hp]
    apply Finset.sum_congr rfl
    intro a _
    rw [marginal_toReal_eq_finite_sum p hp (quantize q.1 q.2)]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro b _
    split_ifs <;> rfl
  simp_rw [he]
  apply Finset.measurable_sum
  intro a _
  apply Measurable.const_mul
  apply Measurable.log
  apply Finset.measurable_sum
  intro b _
  apply Measurable.ite
  · apply measurableSet_eq_fun <;> unfold quantize <;> fun_prop
  · exact measurable_const
  · exact measurable_const

lemma integrable_gridEntropyAt (p : PMF ℝ) (hp : p.support.Finite) (s : ℝ) :
    IntegrableOn (gridEntropyAt p hp s) (Icc (0 : ℝ) 1) volume := by
  have hm : Measurable (gridEntropyAt p hp s) :=
    (measurable_gridEntropyAt p hp).comp (f := fun t : ℝ ↦ (s, t))
      (measurable_const.prodMk measurable_id)
  apply (integrable_const (finiteEntropy p hp)).mono' hm.aestronglyMeasurable
  apply ae_of_all
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg (gridEntropyAt_nonneg p hp s t)]
  exact gridEntropyAt_le p hp s t

lemma abs_sub_lt_of_quantize_eq {s t x y : ℝ} (hs : 0 < s)
    (hxy : quantize s t x = quantize s t y) : |x - y| < s := by
  have hx0 := Int.floor_le (x / s + t)
  have hx1 := Int.lt_floor_add_one (x / s + t)
  have hy0 := Int.floor_le (y / s + t)
  have hy1 := Int.lt_floor_add_one (y / s + t)
  change ⌊x / s + t⌋ = ⌊y / s + t⌋ at hxy
  rw [hxy] at hx0 hx1
  have h1 : x / s - y / s < 1 := by linarith
  have h2 : y / s - x / s < 1 := by linarith
  rw [← sub_div, div_lt_one hs] at h1 h2
  rw [abs_lt]
  constructor <;> linarith

lemma quantize_injective_on_separated {S : Set ℝ} {s : ℝ} (hs : 0 < s)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → s ≤ |x - y|) (t : ℝ) :
    Set.InjOn (quantize s t) S := by
  intro x hx y hy hxy
  by_contra hne
  exact (not_lt_of_ge (hsep x hx y hy hne)) (abs_sub_lt_of_quantize_eq hs hxy)

lemma gridEntropy_eq_of_separated (p : PMF ℝ) (hp : p.support.Finite)
    {s : ℝ} (hs : 0 < s)
    (hsep : ∀ x ∈ p.support, ∀ y ∈ p.support, x ≠ y → s ≤ |x - y|) :
    gridEntropy p hp s = finiteEntropy p hp := by
  have he (t : ℝ) : gridEntropyAt p hp s t = finiteEntropy p hp :=
    finiteEntropy_map_of_injective_support p hp (quantize_injective_on_separated hs hsep t)
  unfold gridEntropy
  simp_rw [he]
  simp

end LpSelfSimilar.Entropy
