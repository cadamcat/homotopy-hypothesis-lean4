import Mathlib.Data.Fin.Tuple.Basic
import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.MixedFlags
import HomotopyHypothesis.Approximation.Zeeman.MixedOriginalPrefix
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
/-!
# Inserting the original-prefix barycentre

For a mixed flag whose original prefix lies outside the fixed subcomplex,
insert that prefix's barycentre immediately after the prefix. If the
barycentre is absent from the flag, this yields another admissible mixed
flag. These two flags form an elementary collapse pair.
-/

universe u

open CategoryTheory Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- An absent exterior prefix barycentre can be inserted at the prefix's end. -/
def MixedPairInsertionStatement : Prop :=
  ∀ {K : SemiSSet.{u}}, K.IsSimplicialComplex →
    ∀ (L : Subfunctor K) (n : ℕ)
      (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk n)))
      (p : MixedOriginalPrefix a)
      (hp : p.face ∉ L.obj (op (Henry.SemiSimplexCategory.mk p.last.val))),
      let v : MixedVertex K L := .inr ⟨⟨p.last.val, p.face⟩, hp⟩
      v ∉ Set.range a.val → MixedAdmissible (Fin.insertNth p.last.succ v a.val)

end HomotopyHypothesis.Approximation.Zeeman
