import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Simplicial.BarycentricSubdivision.DerivedSubdivision
import HomotopyHypothesis.Simplicial.SubdivisionComparison.Base
import HomotopyHypothesis.Simplicial.SubdivisionComparison.Normalize
universe u
open CategoryTheory Limits Opposite
namespace HomotopyHypothesis.Simplicial.SubdivisionComparison
open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- Forget a face incidence to its map of indexing simplices. -/
def faceIndex (W : SemiSSet.{u}) : Simplicial.BarycentricSubdivision.FaceCategory W ⥤ HomotopyHypothesis.Henry.SemiSimplexCategory where
  obj x := x.unop.obj.unop
  map f := Simplicial.BarycentricSubdivision.faceCategoryArrowUnderlying f

instance faceIndex_faithful (W : SemiSSet.{u}) : (faceIndex W).Faithful where
  map_injective {x y} f g h := by
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    exact Quiver.Hom.unop_inj h

lemma faceCategory_mono {W : SemiSSet.{u}} {x y : Simplicial.BarycentricSubdivision.FaceCategory W}
    (f : x ⟶ y) : Mono f := by
  haveI : Mono ((faceIndex W).map f) := semiSimplexCategory_hom_mono _
  exact Functor.mono_of_mono_map (faceIndex W) (by infer_instance)

lemma faceChain_ext_terminal {W : SemiSSet.{u}} {n : ℕ}
    {F G : ComposableArrows (Simplicial.BarycentricSubdivision.FaceCategory W) n}
    (ho : ∀ i, F.obj i = G.obj i)
    (ht : ∀ i, F.map (homOfLE (Fin.le_last i)) ≫ eqToHom (ho (Fin.last n)) =
      eqToHom (ho i) ≫ G.map (homOfLE (Fin.le_last i))) : F = G := by
  refine CategoryTheory.Functor.ext ho ?_
  intro i j f
  haveI := faceCategory_mono (eqToHom (ho j) ≫ G.map (homOfLE (Fin.le_last j)))
  apply (cancel_mono (eqToHom (ho j) ≫ G.map (homOfLE (Fin.le_last j)))).1
  calc
    _ = F.map f ≫ (F.map (homOfLE (Fin.le_last j)) ≫ eqToHom (ho (Fin.last n))) := by rw [ht j]
    _ = F.map (homOfLE (Fin.le_last i)) ≫ eqToHom (ho (Fin.last n)) := by
      rw [← Category.assoc, ← F.map_comp]
      congr 2
    _ = eqToHom (ho i) ≫ G.map (homOfLE (Fin.le_last i)) := ht i
    _ = eqToHom (ho i) ≫ (G.map f ≫ G.map (homOfLE (Fin.le_last j))) := by
      rw [← G.map_comp]
      congr 2
    _ = _ := by simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

lemma faceFunctor_stdFaceObject_of_arrow
    {W : SemiSSet.{u}} {x y : Simplicial.BarycentricSubdivision.FaceCategory W}
    (f : x ⟶ y) (S : Finset (Fin (Simplicial.BarycentricSubdivision.faceDimension y + 1))) (hS : S.Nonempty)
    (hs : HomotopyHypothesis.Henry.SemiSimplexCategory.mk (S.card - 1) = x.unop.obj.unop)
    (hf : Simplicial.BarycentricSubdivision.faceCategoryArrowUnderlying f = eqToHom hs.symm ≫ stdFaceMap S hS) :
    (Simplicial.BarycentricSubdivision.faceFunctor (Simplicial.BarycentricSubdivision.faceObjectSimplexMap y)).obj (stdFaceObject S hS) = x := by
  apply Opposite.unop_injective
  let ho := congrArg Opposite.op hs
  refine Functor.Elements.ext _ _ ho ?_
  change W.map (eqToHom ho)
    ((CategoryTheory.uliftYonedaEquiv.{u}.symm y.unop.val).app _ (ULift.up (stdFaceMap S hS))) = x.unop.val
  rw [CategoryTheory.uliftYonedaEquiv_symm_apply_app]
  have hidx : (stdFaceMap S hS).op ≫ eqToHom ho =
      (Simplicial.BarycentricSubdivision.faceCategoryArrowUnderlying f).op := by
    have he : eqToHom ho = (eqToHom hs.symm).op := by
      rw [eqToHom_op]
    rw [he, hf]
    rfl
  change (W.map (stdFaceMap S hS).op ≫ W.map (eqToHom ho)) y.unop.val = x.unop.val
  rw [← W.map_comp, hidx]
  exact f.unop.map_val

end HomotopyHypothesis.Simplicial.SubdivisionComparison
