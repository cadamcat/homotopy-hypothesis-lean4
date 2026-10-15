import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.LeastCarrier
import HomotopyHypothesis.Approximation.Zeeman.LocalAffine
import HomotopyHypothesis.Approximation.Zeeman.RealizationMaps
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# The realization map of relative derived subdivision

Local affine maps into the least original carriers agree on faces. They
therefore descend to a continuous map from the relative derived realization
to the original realization.
-/

universe u

open CategoryTheory Limits Opposite Convexity

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- Map a derived simplex into the realization through its least original carrier. -/
noncomputable def relativeSimplexRealizationMap {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n))) :
    toTop.obj (Henry.SemiSimplexCategory.mk n) ⟶ realization.obj K :=
  relativeLocalTopMap hK a ≫ simplexChar (uliftYonedaEquiv.symm (leastRelativeCarrier hK a).2)

/-- The local maps into the original realization agree on faces. -/
theorem relativeSimplexRealizationMap_face {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n m : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk n) :
    toTop.map θ ≫ relativeSimplexRealizationMap hK a =
      relativeSimplexRealizationMap hK ((relativeDerived K L).map θ.op a) := by
  unfold relativeSimplexRealizationMap
  rw [← Category.assoc, relativeLocalTopMap_face, Category.assoc,
    ← simplexChar_naturality]
  have hc : Henry.SemiSSet.stdSimplex.map (relativeCarrierFaceMap hK a θ) ≫
      uliftYonedaEquiv.symm (leastRelativeCarrier hK a).2 =
      uliftYonedaEquiv.symm
        (K.map (relativeCarrierFaceMap hK a θ).op (leastRelativeCarrier hK a).2) :=
    (uliftYonedaEquiv_symm_map (relativeCarrierFaceMap hK a θ).op
      (leastRelativeCarrier hK a).2).symm
  rw [hc, relativeCarrierFaceMap_spec]

/-- The compatible family of derived simplex maps, as a map into the restricted Yoneda functor. -/
noncomputable def relativeRealizationFamily {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L : Subfunctor K) :
    relativeDerived K L ⟶
      (Presheaf.restrictedULiftYoneda.{u, 0, u, 0, u + 1} toTop.{u}).obj
        (realization.obj K) where
  app X := ↾fun a => ULift.up (relativeSimplexRealizationMap hK a)
  naturality X Y θ := by
    apply ConcreteCategory.hom_ext
    intro a
    apply ULift.ext
    exact (relativeSimplexRealizationMap_face hK a θ.unop).symm

/-- The continuous map from the relative derived realization to the original realization. -/
noncomputable def relativeRealizationMap {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L : Subfunctor K) :
    realization.obj (relativeDerived K L) ⟶ realization.obj K :=
  realizationDesc (relativeRealizationFamily hK L)

/-- The realization map restricts to the specified local affine map on each derived simplex. -/
theorem relativeRealizationMap_simplex {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n))) :
    simplexChar (uliftYonedaEquiv.symm a) ≫ relativeRealizationMap hK L =
      relativeLocalTopMap hK a ≫
        simplexChar (uliftYonedaEquiv.symm (leastRelativeCarrier hK a).2) :=
  simplexChar_realizationDesc (relativeRealizationFamily hK L) a

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeRealizationMap_simplex
