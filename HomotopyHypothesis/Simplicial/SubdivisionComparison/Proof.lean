import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Simplicial.BarycentricSubdivision.DerivedSubdivision
import HomotopyHypothesis.Simplicial.SubdivisionComparison.Base
import HomotopyHypothesis.Simplicial.SubdivisionComparison.Lift
import HomotopyHypothesis.Simplicial.SubdivisionComparison.Roundtrip
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
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

lemma sdLan_comparison_unit (s : HomotopyHypothesis.Henry.SemiSimplexCategory) :
    (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit Approximation.Topological.sdCos.{u}).app s ≫
      sdLanToFirstSubdivision.app (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj s) =
        sdCosToFirstSubdivision.app s := by
  exact Approximation.Topological.sdLan.descOfIsLeftKanExtension_fac_app _ _ _ _

lemma sdLan_comparison_normal_form {W : SemiSSet.{u}}
    {a : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ}
    (z : (Simplicial.BarycentricSubdivision.firstSubdivision.{u}.obj W).obj a) :
    (sdLanToFirstSubdivision.app W).app a (faceChainToSdLanValue z) = z := by
  let F := z.1
  let hF := z.2
  let c := F.obj (Fin.last a.unop.obj.len)
  let s := c.unop.obj.unop
  let τ := faceChainDerivedSimplex F hF
  let σ := Simplicial.BarycentricSubdivision.faceObjectSimplexMap c
  let η := HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit Approximation.Topological.sdCos.{u}
  let v := (η.app s).app a (ULift.up τ)
  have hn := congrArg (fun f => f.app a v) (sdLanToFirstSubdivision.naturality σ)
  have hu := congrArg (fun f => f.app a (ULift.up τ)) (sdLan_comparison_unit.{u} s)
  change (sdLanToFirstSubdivision.app W).app a ((Approximation.Topological.sdLan.map σ).app a v) = z
  change (sdLanToFirstSubdivision.app W).app a ((Approximation.Topological.sdLan.map σ).app a v) =
    (Simplicial.BarycentricSubdivision.firstSubdivision.map σ).app a
      ((sdLanToFirstSubdivision.app (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj s)).app a v) at hn
  rw [hn]
  change (sdLanToFirstSubdivision.app (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj s)).app a v =
    (sdCosToFirstSubdivision.app s).app a (ULift.up τ) at hu
  rw [hu]
  apply Subtype.ext
  exact faceChain_reconstruct F hF

lemma subdivision_comparison_hom_inv :
    sdLanToFirstSubdivision.{u} ≫ faceChainToSdLan = 𝟙 Approximation.Topological.sdLan.{u} := by
  apply Approximation.Topological.sdLan.hom_ext_of_isLeftKanExtension
    (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit Approximation.Topological.sdCos.{u})
  apply CategoryTheory.NatTrans.ext
  funext s
  change _ ≫ (sdLanToFirstSubdivision.app _ ≫ faceChainToSdLan.app _) = _ ≫ 𝟙 _
  rw [← Category.assoc, sdLan_comparison_unit, faceChainToSdLan_unit, Category.comp_id]

lemma subdivision_comparison_inv_hom :
    faceChainToSdLan.{u} ≫ sdLanToFirstSubdivision = 𝟙 Simplicial.BarycentricSubdivision.firstSubdivision.{u} := by
  ext W a z
  exact sdLan_comparison_normal_form z

/-- The derived subdivision is naturally the strict nerve of the face-incidence category. -/
theorem nonempty_sdLanIso_proof : Nonempty (Approximation.Topological.sdLan.{u} ≅ Simplicial.BarycentricSubdivision.firstSubdivision.{u}) :=
  ⟨{ hom := sdLanToFirstSubdivision
     inv := faceChainToSdLan
     hom_inv_id := subdivision_comparison_hom_inv
     inv_hom_id := subdivision_comparison_inv_hom }⟩

#print axioms nonempty_sdLanIso_proof

end HomotopyHypothesis.Simplicial.SubdivisionComparison
