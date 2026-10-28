module

public import LpSelfSimilar.Entropy.ChainRule

@[expose] public section

/-!
Entropy comparison for two statistics of a finite law. If the second statistic
is constant on every fiber of the first, its actual pushforward entropy is no
larger. No injectivity, measurability or chosen quotient representation is needed
for this discrete statement.
-/

namespace LpSelfSimilar.Entropy

lemma finiteEntropy_map_le_of_factorsThrough {Ω E F : Type*} [Nonempty F]
    (p : PMF Ω) (hp : p.support.Finite) (X : Ω → E) (Y : Ω → F)
    (h : Y.FactorsThrough X) :
    finiteEntropy (p.map Y) (by simpa using hp.image Y) ≤
      finiteEntropy (p.map X) (by simpa using hp.image X) := by
  obtain ⟨f, hf⟩ := (Function.factorsThrough_iff Y).mp h
  have hm := finiteEntropy_map_le (p.map X) (by simpa using hp.image X) f
  simpa only [PMF.map_comp, ← hf] using hm

end LpSelfSimilar.Entropy
