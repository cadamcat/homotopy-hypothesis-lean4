import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.Carriers
import HomotopyHypothesis.Approximation.Zeeman.Faces
import HomotopyHypothesis.Approximation.Zeeman.LeastCarrier
import HomotopyHypothesis.Approximation.Zeeman.LocalAffine
import HomotopyHypothesis.Approximation.Zeeman.Positions
import HomotopyHypothesis.Approximation.Zeeman.RealizationMaps
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.RelativeRealization
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# The retained subcomplex is fixed by relative subdivision

The local realization map may be computed in any original carrier. On a
retained simplex its affine map in the original simplex is the identity,
so the descended realization map fixes the retained subcomplex.
-/

universe u

open CategoryTheory Limits Opposite Convexity

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- The affine extension into any original carrier, as a topological map. -/
noncomputable def relativeTopMapInCarrier {K : SemiSSet.{u}} {L : Subfunctor K}
    {n : ℕ} (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (s : Simplex K) (hs : ∀ i, RelativeVertex.CarriedBy (a.val i) s.2) :
    toTop.obj (Henry.SemiSimplexCategory.mk n) ⟶
      toTop.obj (Henry.SemiSimplexCategory.mk s.1) :=
  TopCat.uliftFunctor.{u}.map
    (TopCat.ofHom ⟨relativeAffineMapInCarrier a s hs, continuous_simplexAffineMap _⟩)

/-- The affine map in the least carrier followed by a carrier inclusion is the map in that carrier. -/
theorem relativeLocalTopMap_toCarrier {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (s : Simplex K) (hs : ∀ i, RelativeVertex.CarriedBy (a.val i) s.2)
    (η : Henry.SemiSimplexCategory.mk (leastRelativeCarrier hK a).1 ⟶
      Henry.SemiSimplexCategory.mk s.1)
    (hη : K.map η.op s.2 = (leastRelativeCarrier hK a).2) :
    relativeLocalTopMap hK a ≫ toTop.map η = relativeTopMapInCarrier a s hs := by
  have h := relativeAffineMapInCarrier_face hK a (𝟙 _) s (leastRelativeCarrier hK a)
    hs (leastRelativeCarrier_spec hK a).1 η hη
  change (relativeAffineMapInCarrier a s hs).comp
      (StdSimplex.affineMap (id : Fin (n + 1) → Fin (n + 1))) =
    (StdSimplex.affineMap η.hom.toOrderHom).comp (relativeLocalAffineMap hK a) at h
  rw [StdSimplex.affineMap_id, ConvexSpace.AffineMap.comp_id] at h
  ext x
  exact congrArg ULift.up (DFunLike.congr_fun h x.down).symm

/-- Computing in any original carrier gives the same map into realization. -/
theorem relativeSimplexRealizationMap_inCarrier {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (s : Simplex K) (hs : ∀ i, RelativeVertex.CarriedBy (a.val i) s.2) :
    relativeSimplexRealizationMap hK a =
      relativeTopMapInCarrier a s hs ≫ simplexChar (uliftYonedaEquiv.symm s.2) := by
  obtain ⟨η, hη, _⟩ := (leastRelativeCarrier_spec hK a).2 s hs
  have hc : Henry.SemiSSet.stdSimplex.map η ≫ uliftYonedaEquiv.symm s.2 =
      uliftYonedaEquiv.symm (leastRelativeCarrier hK a).2 :=
    (uliftYonedaEquiv_symm_map η.op s.2).symm.trans (congrArg uliftYonedaEquiv.symm hη)
  unfold relativeSimplexRealizationMap
  rw [← hc, simplexChar_naturality, ← Category.assoc,
    relativeLocalTopMap_toCarrier hK a s hs η hη]

/-- The original simplex carries all vertices of its retained tuple. -/
theorem retainedTuple_carried {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    (L : Subfunctor K) {n : ℕ}
    (x : L.toFunctor.obj (op (Henry.SemiSimplexCategory.mk n))) (i : Fin (n + 1)) :
    RelativeVertex.CarriedBy
      (((relativeDerivedInclusion hK L).app (op (Henry.SemiSimplexCategory.mk n)) x).val i)
      x.val := by
  change ∃ θ : Henry.SemiSimplexCategory.mk 0 ⟶ Henry.SemiSimplexCategory.mk n,
    K.map θ.op x.val = (vertex x i).val
  exact ⟨vertexInclusion i, rfl⟩

/-- A retained vertex has its original position in its own simplex. -/
theorem retainedVertexPosition {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} {n : ℕ}
    (x : L.toFunctor.obj (op (Henry.SemiSimplexCategory.mk n))) (i : Fin (n + 1))
    (hi : RelativeVertex.CarriedBy (Sum.inl (vertex x i) : RelativeVertex K L) x.val) :
    relativeVertexPosition x.val (.inl (vertex x i)) hi = StdSimplex.single i := by
  rw [relativeVertexPosition_retained]
  have hf : carriedFaceMap x.val (.inl (vertex x i)) hi = vertexInclusion i :=
    faceMap_unique hK _ _ (carriedFaceMap_spec x.val (.inl (vertex x i)) hi) rfl
  rw [hf]
  rfl

/-- In its own original carrier the affine map of a retained simplex is the identity. -/
theorem retainedAffineMap_eq_id {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    (L : Subfunctor K) {n : ℕ}
    (x : L.toFunctor.obj (op (Henry.SemiSimplexCategory.mk n))) :
    relativeAffineMapInCarrier
      ((relativeDerivedInclusion hK L).app (op (Henry.SemiSimplexCategory.mk n)) x)
      ⟨n, x.val⟩ (retainedTuple_carried hK L x) =
        ConvexSpace.AffineMap.id (StdSimplex ℝ (Fin (n + 1))) := by
  apply StdSimplex.affineMap_ext
  intro i
  simp only [relativeAffineMapInCarrier, StdSimplex.affineMapMk_single,
    ConvexSpace.AffineMap.id_apply]
  exact retainedVertexPosition hK x i _

/-- The topological map of a retained simplex in its original carrier is the identity. -/
theorem retainedTopMap_eq_id {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    (L : Subfunctor K) {n : ℕ}
    (x : L.toFunctor.obj (op (Henry.SemiSimplexCategory.mk n))) :
    relativeTopMapInCarrier
      ((relativeDerivedInclusion hK L).app (op (Henry.SemiSimplexCategory.mk n)) x)
      ⟨n, x.val⟩ (retainedTuple_carried hK L x) =
        𝟙 (toTop.obj (Henry.SemiSimplexCategory.mk n)) := by
  ext q
  exact congrArg ULift.up (DFunLike.congr_fun (retainedAffineMap_eq_id hK L x) q.down)

/-- The local realization map of a retained simplex is its original characteristic map. -/
theorem relativeSimplexRealizationMap_retained {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L : Subfunctor K) {n : ℕ}
    (x : L.toFunctor.obj (op (Henry.SemiSimplexCategory.mk n))) :
    relativeSimplexRealizationMap hK
      ((relativeDerivedInclusion hK L).app (op (Henry.SemiSimplexCategory.mk n)) x) =
        simplexChar (uliftYonedaEquiv.symm x.val) := by
  rw [relativeSimplexRealizationMap_inCarrier hK _ ⟨n, x.val⟩
    (retainedTuple_carried hK L x), retainedTopMap_eq_id, Category.id_comp]

/-- Characteristic maps commute with maps of semi-simplicial sets. -/
theorem simplexChar_postcomp {A B : SemiSSet.{u}} {n : ℕ}
    (a : A.obj (op (Henry.SemiSimplexCategory.mk n))) (f : A ⟶ B) :
    simplexChar (uliftYonedaEquiv.symm a) ≫ realization.map f =
      simplexChar (uliftYonedaEquiv.symm (f.app (op (Henry.SemiSimplexCategory.mk n)) a)) := by
  unfold simplexChar realization
  rw [Category.assoc, ← Functor.map_comp, uliftYonedaEquiv_symm_comp]

/-- Relative derived subdivision fixes the realization of the retained subcomplex. -/
theorem relativeRealizationMap_retained {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    (L : Subfunctor K) :
    realization.map (relativeDerivedInclusion hK L) ≫ relativeRealizationMap hK L =
      realization.map L.ι := by
  apply realization_hom_ext
  intro n x
  calc
    simplexChar (uliftYonedaEquiv.symm x) ≫
        (realization.map (relativeDerivedInclusion hK L) ≫ relativeRealizationMap hK L) =
      simplexChar (uliftYonedaEquiv.symm
        ((relativeDerivedInclusion hK L).app (op (Henry.SemiSimplexCategory.mk n)) x)) ≫
          relativeRealizationMap hK L := by
            rw [← Category.assoc, simplexChar_postcomp]
    _ = relativeSimplexRealizationMap hK
        ((relativeDerivedInclusion hK L).app (op (Henry.SemiSimplexCategory.mk n)) x) :=
      relativeRealizationMap_simplex hK _
    _ = simplexChar (uliftYonedaEquiv.symm x.val) :=
      relativeSimplexRealizationMap_retained hK L x
    _ = simplexChar (uliftYonedaEquiv.symm x) ≫ realization.map L.ι :=
      (simplexChar_postcomp x L.ι).symm

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeSimplexRealizationMap_inCarrier
#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeRealizationMap_retained
