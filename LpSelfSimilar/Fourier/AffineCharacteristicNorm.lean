module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Fourier norms under affine normalization

Translation multiplies the characteristic function by a phase of norm one;
rescaling the measure rescales the frequency. This identity permits different
translations for different conditional labels without claiming equality of the
translated and original mixtures.
-/

open MeasureTheory

namespace LpSelfSimilar.Fourier

/-- Affine normalization preserves the original characteristic norm at the rescaled frequency. -/
theorem norm_charFun_map_sub_div (μ : Measure ℝ) (c r s : ℝ) :
    ‖charFun (μ.map (fun x ↦ (x - c) / r)) s‖ = ‖charFun μ (s / r)‖ := by
  have he : μ.map (fun x ↦ (x - c) / r) =
      (μ.map (fun x ↦ x + (-c))).map (fun x ↦ (1 / r) * x) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext x
    dsimp only [Function.comp_apply]
    ring
  rw [he, charFun_map_mul, charFun_map_add_const, norm_mul,
    Complex.norm_exp_ofReal_mul_I, mul_one]
  congr 2
  ring

end LpSelfSimilar.Fourier
