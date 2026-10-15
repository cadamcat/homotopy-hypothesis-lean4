import Mathlib.Geometry.Convex.ConvexSpace.ModuleTopology
import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.Carriers
import HomotopyHypothesis.Approximation.Zeeman.LeastCarrier
import HomotopyHypothesis.Approximation.Zeeman.Positions
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
/-!
# Affine maps of relative derived simplices

The barycentric positions extend to continuous affine maps on the derived
simplices. These maps commute with face restrictions and carrier inclusions.
-/

universe u

open CategoryTheory Limits Opposite Convexity

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- Affine maps between finite standard simplices are continuous. -/
theorem continuous_simplexAffineMap {n m : ℕ}
    (f : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1)))
      (StdSimplex ℝ (Fin (m + 1)))) : Continuous f := by
  apply (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (m + 1))).continuous_iff.mpr
  apply continuous_pi
  intro j
  apply StdSimplex.continuous_of_isAffineMap
  exact (IsAffineMap.linearMap (Finsupp.lapply j :
    (Fin (m + 1) →₀ ℝ) →ₗ[ℝ] ℝ)).comp
      ((StdSimplex.isAffineMap_weights ℝ (Fin (m + 1))).comp f.isAffineMap)

/-- Extend the positions of a relative derived tuple affinely in a carrier. -/
noncomputable def relativeAffineMapInCarrier {K : SemiSSet.{u}} {L : Subfunctor K}
    {n : ℕ} (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (s : Simplex K) (hs : ∀ i, RelativeVertex.CarriedBy (a.val i) s.2) :
    ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1)))
      (StdSimplex ℝ (Fin (s.1 + 1))) :=
  StdSimplex.affineMapMk (R := ℝ) (fun i => relativeVertexPosition s.2 (a.val i) (hs i))

/-- Restriction and inclusion of carriers commute with the local affine map. -/
theorem relativeAffineMapInCarrier_face {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n m : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk n)
    (s t : Simplex K) (hs : ∀ i, RelativeVertex.CarriedBy (a.val i) s.2)
    (ht : ∀ i, RelativeVertex.CarriedBy
      (((relativeDerived K L).map θ.op a).val i) t.2)
    (η : Henry.SemiSimplexCategory.mk t.1 ⟶ Henry.SemiSimplexCategory.mk s.1)
    (hη : K.map η.op s.2 = t.2) :
    (relativeAffineMapInCarrier a s hs).comp (StdSimplex.affineMap θ.hom.toOrderHom) =
      (StdSimplex.affineMap η.hom.toOrderHom).comp
        (relativeAffineMapInCarrier ((relativeDerived K L).map θ.op a) t ht) := by
  apply StdSimplex.affineMap_ext
  intro i
  simp only [ConvexSpace.AffineMap.comp_apply, Function.comp_apply, StdSimplex.coe_affineMap,
    StdSimplex.map_single, relativeAffineMapInCarrier, StdSimplex.affineMapMk_single]
  exact relativeVertexPosition_face hK η hη
    (a.val (θ.hom.toOrderHom i)) (ht i) (hs (θ.hom.toOrderHom i))

/-- The affine map of a derived simplex into its least original carrier. -/
noncomputable def relativeLocalAffineMap {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n))) :
    ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1)))
      (StdSimplex ℝ (Fin ((leastRelativeCarrier hK a).1 + 1))) :=
  relativeAffineMapInCarrier a (leastRelativeCarrier hK a) (leastRelativeCarrier_spec hK a).1

/-- The local affine map is continuous. -/
theorem relativeLocalAffineMap_continuous {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n))) :
    Continuous (relativeLocalAffineMap hK a) :=
  continuous_simplexAffineMap _

/-- The unique inclusion from the carrier of a face to the carrier of its simplex. -/
noncomputable def relativeCarrierFaceMap {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} {n m : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk n) :
    Henry.SemiSimplexCategory.mk
        (leastRelativeCarrier hK ((relativeDerived K L).map θ.op a)).1 ⟶
      Henry.SemiSimplexCategory.mk (leastRelativeCarrier hK a).1 :=
  Classical.choose (leastRelativeCarrier_faceMap hK a θ)

/-- The carrier inclusion restricts the original carrier to the face's carrier. -/
theorem relativeCarrierFaceMap_spec {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} {n m : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk n) :
    K.map (relativeCarrierFaceMap hK a θ).op (leastRelativeCarrier hK a).2 =
      (leastRelativeCarrier hK ((relativeDerived K L).map θ.op a)).2 :=
  (Classical.choose_spec (leastRelativeCarrier_faceMap hK a θ)).1

/-- Bundle the local affine map as a morphism of topological simplices. -/
noncomputable def relativeLocalTopMap {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n))) :
    toTop.obj (Henry.SemiSimplexCategory.mk n) ⟶
      toTop.obj (Henry.SemiSimplexCategory.mk (leastRelativeCarrier hK a).1) :=
  TopCat.uliftFunctor.{u}.map
    (TopCat.ofHom ⟨relativeLocalAffineMap hK a, relativeLocalAffineMap_continuous hK a⟩)

/-- The topological local maps agree on every face. -/
theorem relativeLocalTopMap_face {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} {n m : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk n) :
    toTop.map θ ≫ relativeLocalTopMap hK a =
      relativeLocalTopMap hK ((relativeDerived K L).map θ.op a) ≫
        toTop.map (relativeCarrierFaceMap hK a θ) := by
  have h := relativeAffineMapInCarrier_face hK a θ
    (leastRelativeCarrier hK a)
    (leastRelativeCarrier hK ((relativeDerived K L).map θ.op a))
    (leastRelativeCarrier_spec hK a).1
    (leastRelativeCarrier_spec hK ((relativeDerived K L).map θ.op a)).1
    (relativeCarrierFaceMap hK a θ) (relativeCarrierFaceMap_spec hK a θ)
  ext x
  exact congrArg ULift.up (DFunLike.congr_fun h x.down)

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.continuous_simplexAffineMap
#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeLocalTopMap_face
