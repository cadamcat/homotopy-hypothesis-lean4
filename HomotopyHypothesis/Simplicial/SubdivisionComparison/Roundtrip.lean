import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Simplicial.BarycentricSubdivision.DerivedSubdivision
import HomotopyHypothesis.Simplicial.SubdivisionComparison.Base
import HomotopyHypothesis.Simplicial.SubdivisionComparison.Chain
import HomotopyHypothesis.Simplicial.SubdivisionComparison.Normalize
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Inst42
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdComplex
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits Opposite
namespace HomotopyHypothesis.Simplicial.SubdivisionComparison
open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

lemma stdFaceChain_arrow_comp {k n : ℕ}
    (S : Fin (n + 1) → Finset (Fin (k + 1))) (hS : ∀ i, (S i).Nonempty)
    (hsub : ∀ i : Fin n, S i.castSucc ⊆ S i.succ)
    {i j : Fin (n + 1)} (f : i ⟶ j) :
    Simplicial.BarycentricSubdivision.faceCategoryArrowUnderlying ((stdFaceChain.{u} S hS hsub).map f) ≫
      stdFaceMap (S j) (hS j) = stdFaceMap (S i) (hS i) := by
  have h := Simplicial.BarycentricSubdivision.faceObjectSimplexMap_naturality ((stdFaceChain.{u} S hS hsub).map f)
  rw [faceObjectSimplexMap_eq_stdSimplex_map, faceObjectSimplexMap_eq_stdSimplex_map,
    ← Functor.map_comp] at h
  exact HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.map_injective h

lemma sdSimplexFaceChain_arrow_comp {k n : ℕ}
    (x : (Approximation.Topological.sdComplex k).Simplex n) {i j : Fin (n + 1)} (f : i ⟶ j) :
    Simplicial.BarycentricSubdivision.faceCategoryArrowUnderlying ((sdSimplexFaceChain.{u} x).map f) ≫
      stdFaceMap (sdSimplexFace x j) (sdSimplexFace_nonempty x j) =
        stdFaceMap (sdSimplexFace x i) (sdSimplexFace_nonempty x i) :=
  stdFaceChain_arrow_comp _ _ _ f

lemma faceChain_reconstruct {W : SemiSSet.{u}} {n : ℕ}
    (F : ComposableArrows (Simplicial.BarycentricSubdivision.FaceCategory W) n)
    (hF : StrictMono (fun i : Fin (n + 1) => Simplicial.BarycentricSubdivision.faceDimension (F.obj i))) :
    sdSimplexFaceChain (faceChainDerivedSimplex F hF) ⋙
      Simplicial.BarycentricSubdivision.faceFunctor (Simplicial.BarycentricSubdivision.faceObjectSimplexMap (F.obj (Fin.last n))) = F := by
  let τ := faceChainDerivedSimplex F hF
  let E := stdFaceChain (faceChainSubsetPV F) (faceChainSubsetPV_nonempty F)
    (fun i => faceChainSubsetPV_subset_of_le F (Fin.castSucc_le_succ i))
  have he : sdSimplexFaceChain τ = E := by
    letI : Quiver.IsThin (Simplicial.BarycentricSubdivision.FaceCategory
        (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
          (HomotopyHypothesis.Henry.SemiSimplexCategory.mk
            (Simplicial.BarycentricSubdivision.faceDimension (F.obj (Fin.last n)))))) :=
      standardSimplexFaceCategory_isThin _
    refine CategoryTheory.Functor.ext (fun i => ?_) (fun _ _ _ => Subsingleton.elim _ _)
    change stdFaceObject (sdSimplexFace τ i) _ = stdFaceObject (faceChainSubsetPV F i) _
    congr 1
    exact sdSimplexFace_faceChainDerivedSimplex F hF i
  let G := E ⋙
    Simplicial.BarycentricSubdivision.faceFunctor (Simplicial.BarycentricSubdivision.faceObjectSimplexMap (F.obj (Fin.last n)))
  have hs (i : Fin (n + 1)) :
      HomotopyHypothesis.Henry.SemiSimplexCategory.mk ((faceChainSubsetPV F i).card - 1) =
        (F.obj i).unop.obj.unop := by
    have hc := (faceChainSubsetPV_card F i).trans (faceChainSubset_card F i)
    have hd : (faceChainSubsetPV F i).card - 1 = Simplicial.BarycentricSubdivision.faceDimension (F.obj i) := by omega
    exact congrArg HomotopyHypothesis.Henry.SemiSimplexCategory.mk hd
  have hnorm (i : Fin (n + 1)) : eqToHom (hs i) ≫ chainTerminalFaceArrow F i =
      stdFaceMap (faceChainSubsetPV F i) (faceChainSubsetPV_nonempty F i) := by
    rw [chainTerminalFaceArrow_eq_stdFaceMap F i (hs i) rfl]
    simp
  have ho (i : Fin (n + 1)) : G.obj i = F.obj i := by
    change (Simplicial.BarycentricSubdivision.faceFunctor (Simplicial.BarycentricSubdivision.faceObjectSimplexMap (F.obj (Fin.last n)))).obj
      (stdFaceObject (faceChainSubsetPV F i) _) = F.obj i
    apply faceFunctor_stdFaceObject_of_arrow (F.map (homOfLE (Fin.le_last i)))
      (faceChainSubsetPV F i) (faceChainSubsetPV_nonempty F i) (hs i)
    have ha := chainTerminalFaceArrow_eq_stdFaceMap F i (hs i) rfl
    change chainTerminalFaceArrow F i = eqToHom (hs i).symm ≫
      stdFaceMap (faceChainSubsetPV F i) (faceChainSubsetPV_nonempty F i) ≫ 𝟙 _ at ha
    simp only [Category.comp_id] at ha
    dsimp only [chainTerminalFaceArrow] at ha
    exact ha
  have hidx (i : Fin (n + 1)) : (faceIndex W).map (eqToHom (ho i)) = eqToHom (hs i) := by
    rw [eqToHom_map]
  change sdSimplexFaceChain τ ⋙ _ = F
  rw [he]
  apply faceChain_ext_terminal ho
  intro i
  apply (faceIndex W).map_injective
  simp only [Functor.map_comp, hidx]
  change Simplicial.BarycentricSubdivision.faceCategoryArrowUnderlying
    (E.map (homOfLE (Fin.le_last i))) ≫ eqToHom (hs (Fin.last n)) =
      eqToHom (hs i) ≫ chainTerminalFaceArrow F i
  have hlast : eqToHom (hs (Fin.last n)) =
      stdFaceMap (faceChainSubsetPV F (Fin.last n)) (faceChainSubsetPV_nonempty F (Fin.last n)) := by
    simpa [chainTerminalFaceArrow, Simplicial.BarycentricSubdivision.faceCategoryArrowUnderlying] using hnorm (Fin.last n)
  calc
    _ = Simplicial.BarycentricSubdivision.faceCategoryArrowUnderlying (E.map (homOfLE (Fin.le_last i))) ≫
        stdFaceMap (faceChainSubsetPV F (Fin.last n)) (faceChainSubsetPV_nonempty F (Fin.last n)) :=
      congrArg (fun f => Simplicial.BarycentricSubdivision.faceCategoryArrowUnderlying
        (E.map (homOfLE (Fin.le_last i))) ≫ f) hlast
    _ = stdFaceMap (faceChainSubsetPV F i) (faceChainSubsetPV_nonempty F i) := by
      exact stdFaceChain_arrow_comp _ _ _ (homOfLE (Fin.le_last i))
    _ = _ := (hnorm i).symm

end HomotopyHypothesis.Simplicial.SubdivisionComparison
