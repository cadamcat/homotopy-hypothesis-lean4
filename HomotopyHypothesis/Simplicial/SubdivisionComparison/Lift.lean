import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Simplicial.BarycentricSubdivision.DerivedSubdivision
import HomotopyHypothesis.Simplicial.SubdivisionComparison.Base
import HomotopyHypothesis.Simplicial.SubdivisionComparison.Roundtrip
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Inst42
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdCos
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdLan
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits Opposite
namespace HomotopyHypothesis.Simplicial.SubdivisionComparison
open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

lemma faceChainSubsetPV_standard_image {k n : ℕ}
    (x : (Approximation.Topological.sdComplex k).Simplex n) (i : Fin (n + 1)) :
    (faceChainSubsetPV (sdSimplexFaceChain.{u} x) i).image
      (stdFaceMap (sdSimplexFace x (Fin.last n)) (sdSimplexFace_nonempty x (Fin.last n))).1.toOrderHom =
        sdSimplexFace x i := by
  classical
  unfold faceChainSubsetPV
  rw [Finset.image_image]
  change (faceChainSubset (sdSimplexFaceChain.{u} x) i).image
    (stdFaceMap (sdSimplexFace x (Fin.last n)) (sdSimplexFace_nonempty x (Fin.last n))).1.toOrderHom = _
  unfold faceChainSubset
  rw [Finset.image_image]
  have hc := sdSimplexFaceChain_arrow_comp.{u} x (homOfLE (Fin.le_last i))
  have hf := congrArg (fun f => (f.1.toOrderHom : _ → _)) hc
  change (Finset.univ.image (fun j => _)) = _
  exact (congrArg (fun g => Finset.univ.image g) hf).trans
    (Finset.image_orderEmbOfFin_univ (sdSimplexFace x i)
      (stdFaceCardEq _ (sdSimplexFace_nonempty x i)))

lemma faceChainDerivedSimplex_standard_map {k : ℕ}
    {a : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ}
    (x : (Approximation.Topological.sdCos.{u}.obj (HomotopyHypothesis.Henry.SemiSimplexCategory.mk k)).obj a) :
    (Approximation.Topological.sdCos.{u}.map
      (stdFaceMap (sdSimplexFace x.down (Fin.last a.unop.obj.len))
        (sdSimplexFace_nonempty x.down (Fin.last a.unop.obj.len)))).app a
      (ULift.up (faceChainDerivedSimplex (sdSimplexFaceChain.{u} x.down)
        (sdSimplexFaceChain_dimension_strictMono.{u} x.down))) = x := by
  apply ULift.ext
  apply Subtype.ext
  funext i
  rw [sdSimplexFace_spec x.down i]
  change Approximation.Topological.PV.mid ((faceChainSubsetPV (sdSimplexFaceChain.{u} x.down) i).image _) = _
  congr 1
  exact faceChainSubsetPV_standard_image x.down i

lemma faceChainToSdLan_unit (s : HomotopyHypothesis.Henry.SemiSimplexCategory) :
    sdCosToFirstSubdivision.{u}.app s ≫
      faceChainToSdLan.app (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj s) =
        (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit Approximation.Topological.sdCos.{u}).app s := by
  ext a x
  let F := sdSimplexFaceChain.{u} x.down
  let hF := sdSimplexFaceChain_dimension_strictMono.{u} x.down
  let c := F.obj (Fin.last a.unop.obj.len)
  let τ := faceChainDerivedSimplex F hF
  let γ := stdFaceMap (sdSimplexFace x.down (Fin.last a.unop.obj.len))
    (sdSimplexFace_nonempty x.down (Fin.last a.unop.obj.len))
  let η := HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit Approximation.Topological.sdCos.{u}
  change (Approximation.Topological.sdLan.map (Simplicial.BarycentricSubdivision.faceObjectSimplexMap c)).app a
    ((η.app c.unop.obj.unop).app a (ULift.up τ)) = (η.app s).app a x
  rw [faceObjectSimplexMap_eq_stdSimplex_map]
  change (Approximation.Topological.sdLan.map (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.map γ)).app a
    ((η.app _).app a (ULift.up τ)) = (η.app s).app a x
  have hn := congrArg (fun f => f.app a (ULift.up τ)) (η.naturality γ)
  change (η.app s).app a ((Approximation.Topological.sdCos.map γ).app a (ULift.up τ)) =
    (Approximation.Topological.sdLan.map (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.map γ)).app a
      ((η.app _).app a (ULift.up τ)) at hn
  rw [← hn]
  congr 1
  exact faceChainDerivedSimplex_standard_map x

end HomotopyHypothesis.Simplicial.SubdivisionComparison
