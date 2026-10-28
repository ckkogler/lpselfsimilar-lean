module

public import LpSelfSimilar.Probability.MapProbability

public import LpSelfSimilar.Probability.RealConditionalLaw
public import LpSelfSimilar.Probability.KernelVariance

@[expose] public section

/-!
Conditional variance given an observed random variable, expressed through its
actual regular conditional law. The first two conditional moments identify the
variance, and integration transfers to the law of the observation. These facts
also show that expected conditional variance depends only on the joint law.
-/

open MeasureTheory ProbabilityTheory

namespace LpSelfSimilar

variable {Ω B : Type*} [MeasurableSpace Ω] [mB : MeasurableSpace B]
  {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} {Y : Ω → B}

lemma condDistrib_ae_memLp_two (hY : Measurable Y) (hX : MemLp X 2 P) :
    ∀ᵐ b ∂P.map Y, MemLp (fun x : ℝ ↦ x) 2 (condDistrib X Y P b) := by
  have hi : ∀ᵐ b ∂P.map Y, Integrable (fun x : ℝ ↦ x ^ 2) (condDistrib X Y P b) := by
    apply Measure.ae_integrable_of_integrable_comp
    rw [condDistrib_comp_map hY.aemeasurable hX.aemeasurable]
    exact (integrable_map_measure (by fun_prop) hX.aemeasurable).2 hX.integrable_sq
  filter_upwards [hi] with b hb
  exact (memLp_two_iff_integrable_sq (by fun_prop)).2 hb

/-- Canonical conditional variance is the variance of the conditional law. -/
lemma condVar_eq_variance_condDistrib (hY : Measurable Y) (hX : MemLp X 2 P) :
    condVar (mB.comap Y) X P =ᵐ[P]
      fun ω ↦ variance (fun x : ℝ ↦ x) (condDistrib X Y P (Y ω)) := by
  have hfirst := condExp_ae_eq_integral_condDistrib hY hX.aemeasurable
    stronglyMeasurable_id (hX.integrable one_le_two)
  have hsecond := condExp_ae_eq_integral_condDistrib hY hX.aemeasurable
    (show StronglyMeasurable (fun x : ℝ ↦ x ^ 2) by fun_prop) hX.integrable_sq
  simp only [id_eq] at hfirst
  filter_upwards [condVar_ae_eq_condExp_sq_sub_sq_condExp hY.comap_le hX,
    hfirst, hsecond, ae_of_ae_map hY.aemeasurable (condDistrib_ae_memLp_two hY hX)]
    with ω hv h1 h2 hLp
  simp only [Pi.sub_apply, Pi.pow_def] at hv
  rw [hv, h1, h2, variance_eq_sub hLp]
  rfl

lemma integral_condVar_eq_integral_variance_condDistrib (hY : Measurable Y)
    (hX : MemLp X 2 P) :
    (∫ ω, condVar (mB.comap Y) X P ω ∂P) =
      ∫ b, variance (fun x : ℝ ↦ x) (condDistrib X Y P b) ∂P.map Y := by
  calc
    _ = ∫ ω, variance (fun x : ℝ ↦ x) (condDistrib X Y P (Y ω)) ∂P :=
      integral_congr_ae (condVar_eq_variance_condDistrib hY hX)
    _ = _ := (integral_map hY.aemeasurable
      (stronglyMeasurable_variance_kernel (condDistrib X Y P)).aestronglyMeasurable).symm

/-- Expected conditional variance is unchanged when a joint law is realized
on a different sample space. -/
theorem integral_condVar_map {Θ : Type*} [MeasurableSpace Θ]
    {Z : Ω → Θ} (hZ : Measurable Z) {F : Θ → ℝ} {G : Θ → B}
    (hG : Measurable G) (hF : MemLp F 2 (P.map Z)) :
    (∫ θ, condVar (mB.comap G) F (P.map Z) θ ∂P.map Z) =
      ∫ ω, condVar (mB.comap (G ∘ Z)) (F ∘ Z) P ω ∂P := by
  letI : IsProbabilityMeasure (P.map Z) := LpSelfSimilar.Probability.isProbabilityMeasure_map hZ.aemeasurable
  have hZp : MeasurePreserving Z P (P.map Z) := ⟨hZ, rfl⟩
  have hFZ : MemLp (F ∘ Z) 2 P := hF.comp_measurePreserving hZp
  rw [integral_condVar_eq_integral_variance_condDistrib hG hF,
    integral_condVar_eq_integral_variance_condDistrib (hG.comp hZ) hFZ,
    Measure.map_map hG hZ]
  apply integral_congr_ae
  filter_upwards [condDistrib_map hG.aemeasurable hF.aemeasurable hZ.aemeasurable]
    with b hb
  rw [hb]

end LpSelfSimilar
