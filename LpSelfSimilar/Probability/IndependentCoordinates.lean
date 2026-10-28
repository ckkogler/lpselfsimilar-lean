module

public import Mathlib.Probability.Independence.InfinitePi

@[expose] public section

/-!
Disjoint, possibly infinite coordinate families of independent variables are
independent as random vectors. The result is expressed using arbitrary
reindexing maps so that tails and residue classes need no special probability
spaces. It follows by independence of the generated sigma algebras.
-/

open MeasureTheory ProbabilityTheory Set MeasurableSpace

namespace LpSelfSimilar

lemma independent_coordinate_families {Ω ι α β X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {P : Measure Ω}
    {Z : ι → Ω → X} (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (f : α → ι) (g : β → ι) (hfg : Disjoint (range f) (range g)) :
    IndepFun (fun ω i ↦ Z (f i) ω) (fun ω j ↦ Z (g j) ω) P := by
  rw [IndepFun_iff_Indep]
  have h := indep_iSup_of_disjoint (fun i ↦ (hZ i).comap_le) hind hfg
  simpa only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
    MeasurableSpace.comap_comp, Function.comp_def, iSup_range] using h

end LpSelfSimilar
