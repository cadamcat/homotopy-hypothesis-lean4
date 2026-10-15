import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.Carriers
import HomotopyHypothesis.Approximation.Zeeman.CollarVertices
import HomotopyHypothesis.Approximation.Zeeman.LeastCarrier
import HomotopyHypothesis.Approximation.Zeeman.LocalAffine
import HomotopyHypothesis.Approximation.Zeeman.RealizationMaps
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.RetainedRealization
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# A map towards the retained subcomplex

The preferred source vertices define affine maps on derived simplices.
These maps agree on faces, descend to realization, and fix the retained
subcomplex. Each simplex maps into its original carrier.
-/

universe u

open CategoryTheory Opposite Convexity

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- The vertex map of a derived simplex in an original carrier. -/
noncomputable def relativeCollarTopMapInCarrier {K : SemiSSet.{u}} {L : Subfunctor K}
    {n : ℕ} (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (s : Simplex K) (hs : ∀ i, RelativeVertex.CarriedBy (a.val i) s.2) :
    toTop.obj (Henry.SemiSimplexCategory.mk n) ⟶
      toTop.obj (Henry.SemiSimplexCategory.mk s.1) :=
  vertexMap (fun i => relativeCollarVertexIndex s.2 (a.val i) (hs i))

/-- The local collar maps commute with restriction and carrier inclusions. -/
theorem relativeCollarTopMapInCarrier_face {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n m : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk n)
    (s t : Simplex K) (hs : ∀ i, RelativeVertex.CarriedBy (a.val i) s.2)
    (ht : ∀ i, RelativeVertex.CarriedBy
      (((relativeDerived K L).map θ.op a).val i) t.2)
    (η : Henry.SemiSimplexCategory.mk t.1 ⟶ Henry.SemiSimplexCategory.mk s.1)
    (hη : K.map η.op s.2 = t.2) :
    toTop.map θ ≫ relativeCollarTopMapInCarrier a s hs =
      relativeCollarTopMapInCarrier ((relativeDerived K L).map θ.op a) t ht ≫
        toTop.map η := by
  ext x
  change ULift.up (StdSimplex.map
      (fun i => relativeCollarVertexIndex s.2 (a.val i) (hs i))
      (StdSimplex.map θ.hom.toOrderHom x.down)) =
    ULift.up (StdSimplex.map η.hom.toOrderHom (StdSimplex.map
      (fun i => relativeCollarVertexIndex t.2
        (((relativeDerived K L).map θ.op a).val i) (ht i)) x.down))
  congr 1
  let f := fun i => relativeCollarVertexIndex s.2 (a.val i) (hs i)
  let g := fun i => relativeCollarVertexIndex t.2
    (((relativeDerived K L).map θ.op a).val i) (ht i)
  have hf : f ∘ θ.hom.toOrderHom = η.hom.toOrderHom ∘ g := by
    funext i
    exact relativeCollarVertexIndex_face hK η hη
      (a.val (θ.hom.toOrderHom i)) (ht i) (hs (θ.hom.toOrderHom i))
  exact (StdSimplex.map_comp x.down θ.hom.toOrderHom f).symm.trans
    ((congrArg (fun v => StdSimplex.map v x.down) hf).trans
      (StdSimplex.map_comp x.down g η.hom.toOrderHom))

/-- The local collar map into the original realization. -/
noncomputable def relativeCollarSimplexMap {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n))) :
    toTop.obj (Henry.SemiSimplexCategory.mk n) ⟶ realization.obj K :=
  relativeCollarTopMapInCarrier a (leastRelativeCarrier hK a)
      (leastRelativeCarrier_spec hK a).1 ≫
    simplexChar (uliftYonedaEquiv.symm (leastRelativeCarrier hK a).2)

/-- The local collar maps into realization agree on faces. -/
theorem relativeCollarSimplexMap_face {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n m : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk n) :
    toTop.map θ ≫ relativeCollarSimplexMap hK a =
      relativeCollarSimplexMap hK ((relativeDerived K L).map θ.op a) := by
  unfold relativeCollarSimplexMap
  rw [← Category.assoc, relativeCollarTopMapInCarrier_face hK a θ
    (leastRelativeCarrier hK a)
    (leastRelativeCarrier hK ((relativeDerived K L).map θ.op a))
    (leastRelativeCarrier_spec hK a).1
    (leastRelativeCarrier_spec hK ((relativeDerived K L).map θ.op a)).1
    (relativeCarrierFaceMap hK a θ) (relativeCarrierFaceMap_spec hK a θ),
    Category.assoc, ← simplexChar_naturality]
  have hc : Henry.SemiSSet.stdSimplex.map (relativeCarrierFaceMap hK a θ) ≫
      uliftYonedaEquiv.symm (leastRelativeCarrier hK a).2 =
    uliftYonedaEquiv.symm (leastRelativeCarrier hK ((relativeDerived K L).map θ.op a)).2 :=
    (uliftYonedaEquiv_symm_map (relativeCarrierFaceMap hK a θ).op _).symm.trans
      (congrArg uliftYonedaEquiv.symm (relativeCarrierFaceMap_spec hK a θ))
  rw [hc]

/-- The compatible local collar maps as a restricted Yoneda family. -/
noncomputable def relativeCollarFamily {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L : Subfunctor K) :
    relativeDerived K L ⟶
      (Presheaf.restrictedULiftYoneda.{u, 0, u, 0, u + 1} toTop.{u}).obj
        (realization.obj K) where
  app X := ↾fun a => ULift.up (relativeCollarSimplexMap hK a)
  naturality X Y θ := by
    apply ConcreteCategory.hom_ext
    intro a
    apply ULift.ext
    exact (relativeCollarSimplexMap_face hK a θ.unop).symm

/-- The collar vertex map, descended to realization. -/
noncomputable def relativeCollarMap {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L : Subfunctor K) :
    realization.obj (relativeDerived K L) ⟶ realization.obj K :=
  realizationDesc (relativeCollarFamily hK L)

/-- On each simplex the descended collar map is the specified vertex map. -/
theorem relativeCollarMap_simplex {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n))) :
    simplexChar (uliftYonedaEquiv.symm a) ≫ relativeCollarMap hK L =
      relativeCollarSimplexMap hK a :=
  simplexChar_realizationDesc (relativeCollarFamily hK L) a

/-- The collar map can be computed in any original carrier. -/
theorem relativeCollarSimplexMap_inCarrier {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (s : Simplex K) (hs : ∀ i, RelativeVertex.CarriedBy (a.val i) s.2) :
    relativeCollarSimplexMap hK a =
      relativeCollarTopMapInCarrier a s hs ≫ simplexChar (uliftYonedaEquiv.symm s.2) := by
  obtain ⟨η, hη, _⟩ := (leastRelativeCarrier_spec hK a).2 s hs
  have ht := relativeCollarTopMapInCarrier_face hK a (𝟙 _) s (leastRelativeCarrier hK a)
    hs (leastRelativeCarrier_spec hK a).1 η hη
  have hid : toTop.{u}.map (𝟙 (Henry.SemiSimplexCategory.mk n)) = 𝟙 _ :=
    CategoryTheory.Functor.map_id _ _
  rw [hid, Category.id_comp] at ht
  change relativeCollarTopMapInCarrier a s hs =
    relativeCollarTopMapInCarrier a (leastRelativeCarrier hK a)
      (leastRelativeCarrier_spec hK a).1 ≫ toTop.map η at ht
  have hc : Henry.SemiSSet.stdSimplex.map η ≫ uliftYonedaEquiv.symm s.2 =
    uliftYonedaEquiv.symm (leastRelativeCarrier hK a).2 :=
    (uliftYonedaEquiv_symm_map η.op s.2).symm.trans (congrArg uliftYonedaEquiv.symm hη)
  unfold relativeCollarSimplexMap
  rw [← hc, simplexChar_naturality, ← Category.assoc]
  exact congrArg (fun e => e ≫ simplexChar (uliftYonedaEquiv.symm s.2)) ht.symm

/-- In the carrier of a retained simplex the collar map is the identity. -/
theorem relativeCollarTopMap_retained {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L : Subfunctor K) {n : ℕ}
    (x : L.toFunctor.obj (op (Henry.SemiSimplexCategory.mk n))) :
    relativeCollarTopMapInCarrier
      ((relativeDerivedInclusion hK L).app (op (Henry.SemiSimplexCategory.mk n)) x)
      ⟨n, x.val⟩ (retainedTuple_carried hK L x) =
        𝟙 (toTop.obj (Henry.SemiSimplexCategory.mk n)) := by
  have hf : (fun i => relativeCollarVertexIndex x.val (.inl (vertex x i))
      (retainedTuple_carried hK L x i)) = id :=
    funext (fun i => relativeCollarVertexIndex_retained hK x i _)
  ext q
  change ULift.up (StdSimplex.map (fun i => relativeCollarVertexIndex x.val
    (.inl (vertex x i)) (retainedTuple_carried hK L x i)) q.down) = q
  exact congrArg ULift.up ((congrArg (fun f => StdSimplex.map f q.down) hf).trans
    (StdSimplex.map_id q.down))

/-- The collar map fixes the retained subcomplex. -/
theorem relativeCollarMap_retained {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L : Subfunctor K) :
    realization.map (relativeDerivedInclusion hK L) ≫ relativeCollarMap hK L =
      realization.map L.ι := by
  apply realization_hom_ext
  intro n x
  rw [← Category.assoc, simplexChar_postcomp, relativeCollarMap_simplex,
    relativeCollarSimplexMap_inCarrier hK _ ⟨n, x.val⟩ (retainedTuple_carried hK L x),
    relativeCollarTopMap_retained, Category.id_comp, simplexChar_postcomp]
  rfl

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeCollarMap_simplex
#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeCollarMap_retained
