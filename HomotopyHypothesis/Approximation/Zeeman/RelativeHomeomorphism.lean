import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.BarycentricPeeling.BarycentricPeeling
import HomotopyHypothesis.Realization.ComplexTopology.ComplexRealizationTopology
import HomotopyHypothesis.Approximation.Zeeman.RealizationTopology
import HomotopyHypothesis.Approximation.Zeeman.RelativeCoverage
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.RelativeInjectivity
import HomotopyHypothesis.Approximation.Zeeman.RelativeLinear
import HomotopyHypothesis.Approximation.Zeeman.RelativeRealization
import HomotopyHypothesis.Approximation.Zeeman.RetainedRealization
import HomotopyHypothesis.Approximation.Zeeman.VertexDistributions
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# Realization of relative derived subdivision

Relative derived subdivision of a finite simplicial complex has the same
realization. Barycentric coverage and uniqueness make the realization map
bijective, and compactness of the source and Hausdorffness of the target
make it an isomorphism. This isomorphism is linear on simplices and fixes
the retained subcomplex.
-/

universe u

open CategoryTheory Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- Barycentric peeling supplies unconditional coverage of the relative derived realization. -/
theorem relativeRealizationMap_surjective {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    (L : Subfunctor K) : Function.Surjective (relativeRealizationMap hK L).hom :=
  relativeRealizationMap_surjective_of_peeling
    Approximation.BarycentricPeeling.barycentricPeelingStatement_proof hK L

/-- The relative derived realization map of a finite simplicial complex is an isomorphism. -/
theorem relativeRealizationMap_isIso {K : SemiSSet.{u}} (hK : K.IsFinite)
    (hKs : K.IsSimplicialComplex) (L : Subfunctor K) :
    IsIso (relativeRealizationMap hKs L) := by
  letI : CompactSpace (realization.obj (relativeDerived K L)) :=
    compactSpace_realization_of_isFinite (relativeDerived_isFinite hK L)
  letI : T2Space (realization.obj K) :=
    (Realization.ComplexTopology.complexRealizationTopologyStatement_proof K hK hKs).1
  exact TopCat.isIso_of_bijective_of_isClosedMap (relativeRealizationMap hKs L)
    ⟨relativeRealizationMap_injective hKs L, relativeRealizationMap_surjective hKs L⟩
    (relativeRealizationMap hKs L).hom.continuous.isClosedMap

/-- The geometric identification of a relative derived subdivision with the original complex. -/
noncomputable def relativeRealizationIso {K : SemiSSet.{u}} (hK : K.IsFinite)
    (hKs : K.IsSimplicialComplex) (L : Subfunctor K) :
    realization.obj (relativeDerived K L) ≅ realization.obj K := by
  letI := relativeRealizationMap_isIso hK hKs L
  exact asIso (relativeRealizationMap hKs L)

/-- The geometric identification has the previously constructed affine realization map. -/
theorem relativeRealizationIso_hom {K : SemiSSet.{u}} (hK : K.IsFinite)
    (hKs : K.IsSimplicialComplex) (L : Subfunctor K) :
    (relativeRealizationIso hK hKs L).hom = relativeRealizationMap hKs L := rfl

/-- Every relative derived simplex is carried linearly into an original simplex. -/
theorem relativeRealizationIso_linear {K : SemiSSet.{u}} (hK : K.IsFinite)
    (hKs : K.IsSimplicialComplex) (L : Subfunctor K)
    (n : ℕ) (y' : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶
      relativeDerived K L) :
    ∃ (m : ℕ) (y : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk m) ⟶ K)
      (e : toTop.obj (Henry.SemiSimplexCategory.mk n) ⟶
        toTop.obj (Henry.SemiSimplexCategory.mk m)),
      IsLinearEmbedding e ∧ simplexChar y' ≫ (relativeRealizationIso hK hKs L).hom =
        e ≫ simplexChar y :=
  relativeRealizationMap_linear hKs L n y'

/-- The geometric identification fixes the retained subcomplex. -/
theorem relativeRealizationIso_retained {K : SemiSSet.{u}} (hK : K.IsFinite)
    (hKs : K.IsSimplicialComplex) (L : Subfunctor K) :
    realization.map (relativeDerivedInclusion hKs L) ≫ (relativeRealizationIso hK hKs L).hom =
      realization.map L.ι :=
  relativeRealizationMap_retained hKs L

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeRealizationMap_isIso
#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeRealizationIso_linear
#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeRealizationIso_retained
