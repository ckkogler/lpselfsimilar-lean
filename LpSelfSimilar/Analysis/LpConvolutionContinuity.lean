module

public import LpSelfSimilar.Analysis.FunctionConvolution
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

@[expose] public section

/-!
Continuity of convolution at conjugate finite Lp exponents. Translation is
continuous in Lp, and integration of a product is Mathlib's continuous Holder
pairing. This proof applies to arbitrary Lp representatives.
-/

open MeasureTheory
open scoped ENNReal

namespace LpSelfSimilar

/-- Convolution of conjugate Lp functions is continuous, including noncontinuous inputs. -/
theorem continuous_functionConvolution_of_memLp {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hq : q ≠ ∞) {f g : ℝ → ℝ} (hf : MemLp f p volume) (hg : MemLp g q volume) :
    Continuous (functionConvolution f g) := by
  let T (x : ℝ) : C(ℝ, ℝ) := ⟨fun z ↦ x - z, continuous_const.sub continuous_id⟩
  have hT : Continuous T := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact continuous_fst.sub continuous_snd
  have hMP (x : ℝ) : MeasurePreserving (T x) volume volume :=
    volume.measurePreserving_sub_left x
  have htrans := (continuous_const : Continuous (fun _ : ℝ ↦ hg.toLp g)).compMeasurePreservingLp
    hT hMP hq
  let B : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ
  have hcont := (B.lpPairing volume p q (hf.toLp f)).continuous.comp htrans
  apply hcont.congr
  intro x
  change B.lpPairing volume p q (hf.toLp f)
    (Lp.compMeasurePreserving (T x) (hMP x) (hg.toLp g)) = functionConvolution f g x
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  have hge := (hg.coeFn_toLp).comp_tendsto (hMP x).quasiMeasurePreserving.tendsto_ae
  filter_upwards [hf.coeFn_toLp, Lp.coeFn_compMeasurePreserving (hg.toLp g) (hMP x), hge]
    with z hzf hzg hztrans
  change B ((hf.toLp f) z) ((Lp.compMeasurePreserving (T x) (hMP x) (hg.toLp g)) z) =
    f z * g (x - z)
  rw [hzf, hzg, hztrans]
  rfl

end LpSelfSimilar
