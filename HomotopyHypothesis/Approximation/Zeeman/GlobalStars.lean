import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.CollarAffinity
import HomotopyHypothesis.Approximation.Zeeman.CollarMap
import HomotopyHypothesis.Approximation.Zeeman.CollarSubcomplex
import HomotopyHypothesis.Approximation.Zeeman.ExteriorIteration
import HomotopyHypothesis.Approximation.Zeeman.InducedCover
import HomotopyHypothesis.Approximation.Zeeman.RelativeComplex
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.RestrictedAffinity
import HomotopyHypothesis.Approximation.Zeeman.RetainedFull
import HomotopyHypothesis.Approximation.Zeeman.ScalarMesh
import HomotopyHypothesis.Approximation.Zeeman.SimplexSupport
import HomotopyHypothesis.Approximation.Zeeman.SubdivisionIteration
import HomotopyHypothesis.Approximation.Zeeman.TargetStars
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# Global vertex choices for relative approximation

Exterior stars eventually refine the target star cover. Outside the induced
exterior, affine target coordinates on the collar supply the same star
condition. Choosing these images together gives one global map on vertices.
-/

universe u

open CategoryTheory Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- A global vertex map satisfies the star condition for a continuous map. -/
def IsVertexStarMap {W M : SemiSSet.{u}} (F : realization.obj W ⟶ realization.obj M)
    (q : W.obj (op (Henry.SemiSimplexCategory.mk 0)) →
      M.obj (op (Henry.SemiSimplexCategory.mk 0))) : Prop :=
  ∀ w, Set.MapsTo F.hom (vertexOpenStar W w) (vertexOpenStar M (q w))

/-- A collar with affine target coordinates and a disjoint exterior gives global star choices. -/
theorem exists_iterated_vertexStarMap {K M : SemiSSet.{u}}
    (hK : K.IsFinite) (hKs : K.IsSimplicialComplex) (L A B : Subfunctor K)
    (hAB : A ⊔ B = ⊤) (hBL : B ⊓ L = ⊥)
    (F : realization.obj K ⟶ realization.obj M)
    (hF : ∀ a, IsSimplexwiseScalarAffineOn A (vertexCoordinate M a ∘ F.hom)) :
    ∃ (r : ℕ) (q : (derivedSubdivisionIterate hK hKs L r).Y'.obj
      (op (Henry.SemiSimplexCategory.mk 0)) → M.obj (op (Henry.SemiSimplexCategory.mk 0))),
      IsVertexStarMap ((derivedSubdivisionIterate hK hKs L r).h.hom ≫ F) q := by
  classical
  haveI : Finite (K.obj (op (Henry.SemiSimplexCategory.mk 0))) := hK.1 0
  letI : Fintype (K.obj (op (Henry.SemiSimplexCategory.mk 0))) := Fintype.ofFinite _
  obtain ⟨D, hD⟩ := hK.2
  obtain ⟨R, hR⟩ := exists_exterior_targetStar_refinement hK hKs L B hBL D hD F
  let S := derivedSubdivisionIterate hK hKs L R
  let A' := iteratedInducedSubdivision hK hKs L A R
  let B' := iteratedInducedSubdivision hK hKs L B R
  let F' := S.h.hom ≫ F
  have hcover : A' ⊔ B' = ⊤ := iteratedInducedSubdivision_cover hK hKs L A B hAB R
  have hstar (w : S.Y'.obj (op (Henry.SemiSimplexCategory.mk 0))) :
      ∃ a, Set.MapsTo F'.hom (vertexOpenStar S.Y' w) (vertexOpenStar M a) := by
    by_cases hw : w ∈ B'.obj (op (Henry.SemiSimplexCategory.mk 0))
    · obtain ⟨a, ha⟩ := hR R le_rfl w hw
      refine ⟨a, ?_⟩
      intro z hz
      obtain ⟨n, x, p, _, rfl⟩ := exists_simplexChar_nonzero_rep z
      obtain ⟨i, hi, _⟩ := (mem_vertexOpenStar_simplex_iff x p w).mp hz
      exact ha n x i hi p
    · obtain ⟨a, ha⟩ := vertexOpenStar_cover M
        (F'.hom ((simplexChar (uliftYonedaEquiv.symm w)).hom (simplexVertex (n := 0) 0)))
      have hAff := isSimplexwiseScalarAffineOn_iteratedSubdivision hK hKs L A
        (vertexCoordinate M a ∘ F.hom) (hF a) R
      exact ⟨a, mapsTo_vertexOpenStar_of_scalarAffineOn A' B' hcover F' w hw a hAff ha⟩
  choose q hq using hstar
  exact ⟨R, q, hq⟩

/-- After refining the collar and its exterior, the collar-composed map has global star choices. -/
theorem exists_relativeCollar_vertexStarMap {K M : SemiSSet.{u}}
    (hK : K.IsFinite) (hKs : K.IsSimplicialComplex) (L : Subfunctor K)
    (hfull : IsFullSubcomplex L) (f : realization.obj K ⟶ realization.obj M)
    (hL : IsSimplicial (realization.map L.ι ≫ f)) :
    ∃ (r : ℕ) (q : (derivedSubdivisionIterate (relativeDerived_isFinite hK L)
      (relativeDerived_isSimplicialComplex hKs L)
      (Subfunctor.range (relativeDerivedInclusion hKs L)) r).Y'.obj
        (op (Henry.SemiSimplexCategory.mk 0)) → M.obj (op (Henry.SemiSimplexCategory.mk 0))),
      IsVertexStarMap ((derivedSubdivisionIterate (relativeDerived_isFinite hK L)
        (relativeDerived_isSimplicialComplex hKs L)
        (Subfunctor.range (relativeDerivedInclusion hKs L)) r).h.hom ≫
          relativeCollarMap hKs L ≫ f) q :=
  exists_iterated_vertexStarMap (relativeDerived_isFinite hK L)
    (relativeDerived_isSimplicialComplex hKs L)
    (Subfunctor.range (relativeDerivedInclusion hKs L))
    (relativeCollarSubcomplex K L) (relativeCollarExterior K L)
    (relativeCollar_sup_exterior L) (relativeCollarExterior_inf_retained hKs L)
    (relativeCollarMap hKs L ≫ f) (isSimplexwiseScalarAffineOn_collar_comp hKs L hfull f hL)

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.exists_iterated_vertexStarMap
#print axioms HomotopyHypothesis.Approximation.Zeeman.exists_relativeCollar_vertexStarMap
