import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Simplicial.MixedPairs.MixedPairInsertion
import HomotopyHypothesis.Approximation.Zeeman.MixedCollapse
import HomotopyHypothesis.Approximation.Zeeman.MixedFlags
import HomotopyHypothesis.Approximation.Zeeman.RelativeComplex
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
/-!
# Relative derived subdivision with a collapsing prism

The admissible insertion of each exterior prefix barycentre completes the
finite mixed-cell collapse. It gives the relative derived subdivision of
a finite complex, retaining the fixed subcomplex and carrying a pinched
prism that collapses onto the derived end.
-/

universe u

open CategoryTheory Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- The derived end of the mixed prism is anodyne for a finite complex. -/
theorem mixedDerivedInclusion_isAnodyne {K : SemiSSet.{u}} (hK : K.IsFinite)
    (hKs : K.IsSimplicialComplex) (L : Subfunctor K) :
    anodyne (mixedDerivedInclusion L) :=
  mixedDerivedInclusion_anodyne Simplicial.MixedPairs.mixedPairInsertionStatement_proof hK hKs L

/-- The relative derived subdivision, with its linear realization and pinched collapsing prism. -/
noncomputable def derivedSubdivision {K : SemiSSet.{u}} (hK : K.IsFinite)
    (hKs : K.IsSimplicialComplex) (L : Subfunctor K) : RelSubdivision K L :=
  relativeDerivedSubdivision Simplicial.MixedPairs.mixedPairInsertionStatement_proof hK hKs L

/-- The relative derived subdivision is again an ordered simplicial complex. -/
theorem derivedSubdivision_isSimplicialComplex {K : SemiSSet.{u}} (hK : K.IsFinite)
    (hKs : K.IsSimplicialComplex) (L : Subfunctor K) :
    (derivedSubdivision hK hKs L).Y'.IsSimplicialComplex :=
  relativeDerived_isSimplicialComplex hKs L

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.mixedDerivedInclusion_isAnodyne
#print axioms HomotopyHypothesis.Approximation.Zeeman.derivedSubdivision
#print axioms HomotopyHypothesis.Approximation.Zeeman.derivedSubdivision_isSimplicialComplex
