import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.ApproximationAssembly
import HomotopyHypothesis.Approximation.Zeeman.PointwiseCarrierHomotopy
import HomotopyHypothesis.Approximation.Zeeman.VertexStarApproximation
/-!
# Zeeman's relative simplicial approximation theorem

Relative derived subdivisions carry collapsing prisms. The collar and
vertex-star constructions give a coherent simplicial approximation that
agrees with the original map on the retained subcomplex and is homotopic
to it relative to that subcomplex.
-/

universe u

open CategoryTheory

namespace HomotopyHypothesis.Henry.Packages

open SemiSSet

/-- Relative simplicial approximation for finite ordered simplicial complexes. -/
theorem zeeman_relativeApproximation_proof {K M : SemiSSet.{u}} (hK : K.IsFinite)
    (hKs : K.IsSimplicialComplex) (hM : M.IsFinite) (hMs : M.IsSimplicialComplex)
    (L : Subfunctor K) (f : realization.obj K ⟶ realization.obj M)
    (hL : IsSimplicial (realization.map L.ι ≫ f)) :
    ∃ (S : RelSubdivision K L) (g : realization.obj S.Y' ⟶ realization.obj M),
      IsSimplicial g ∧ realization.map S.j ≫ g = realization.map L.ι ≫ f ∧
        g.hom.HomotopicRel (S.h.hom ≫ f).hom (Set.range (realization.map S.j).hom) :=
  Approximation.Zeeman.zeeman_relativeApproximation_of_starApproximation
    Approximation.Zeeman.vertexStarApproximationStatement_proof
    Approximation.Zeeman.pointwiseCarrierHomotopyStatement_proof hK hKs hM hMs L f hL

end HomotopyHypothesis.Henry.Packages

#print axioms HomotopyHypothesis.Henry.Packages.zeeman_relativeApproximation_proof
