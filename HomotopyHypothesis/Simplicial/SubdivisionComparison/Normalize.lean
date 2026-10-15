import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Simplicial.BarycentricSubdivision.DerivedSubdivision
import HomotopyHypothesis.Simplicial.SubdivisionComparison.Base
universe u
open CategoryTheory Limits Opposite
namespace HomotopyHypothesis.Simplicial.SubdivisionComparison
open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

lemma semi_eqToHom_apply {a b : HomotopyHypothesis.Henry.SemiSimplexCategory}
    (h : a = b) (i : Fin (a.obj.len + 1)) :
    SimplexCategory.Hom.toOrderHom
      (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map (eqToHom h)) i =
        Fin.cast (congrArg (fun s : HomotopyHypothesis.Henry.SemiSimplexCategory => s.obj.len + 1) h) i := by
  subst b
  rfl

lemma chainTerminalFaceArrow_eq_stdFaceMap
    {W : HomotopyHypothesis.Henry.SemiSSet.{u}} {n : ℕ}
    (F : ComposableArrows (Simplicial.BarycentricSubdivision.FaceCategory W) n)
    (i : Fin (n + 1))
    (hSrc : HomotopyHypothesis.Henry.SemiSimplexCategory.mk
      ((faceChainSubsetPV F i).card - 1) = (F.obj i).unop.obj.unop)
    (hTgt : HomotopyHypothesis.Henry.SemiSimplexCategory.mk
      (Simplicial.BarycentricSubdivision.faceDimension (W := W) (F.obj (Fin.last n))) =
        (F.obj (Fin.last n)).unop.obj.unop) :
    chainTerminalFaceArrow F i =
      eqToHom hSrc.symm ≫
      stdFaceMap (faceChainSubsetPV F i) (faceChainSubsetPV_nonempty F i) ≫
      eqToHom hTgt := by
  classical
  let S := faceChainSubsetPV F i
  let α := chainTerminalFaceArrow F i
  let β := eqToHom hSrc ≫ α ≫ eqToHom hTgt.symm
  let q := SimplexCategory.Hom.toOrderHom
    (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map β)
  have hmono : StrictMono q := by
    have hinj : Function.Injective q := by
      rw [← SimplexCategory.mono_iff_injective]
      exact β.property
    exact q.monotone.strictMono_of_injective hinj
  have hmem : ∀ j, q j ∈ S := by
    intro j
    change SimplexCategory.Hom.toOrderHom
      (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map (eqToHom hTgt.symm))
      (α.1.toOrderHom (SimplexCategory.Hom.toOrderHom
        (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map (eqToHom hSrc)) j)) ∈ S
    rw [semi_eqToHom_apply]
    change _ ∈ (faceChainSubset F i).image _
    refine Finset.mem_image.mpr ⟨α.1.toOrderHom
      ((HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map (eqToHom hSrc)).toOrderHom j), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
    · apply Fin.ext
      rfl
  have hq := Finset.orderEmbOfFin_unique (stdFaceCardEq S (faceChainSubsetPV_nonempty F i))
    hmem hmono
  have hβ : β = stdFaceMap S (faceChainSubsetPV_nonempty F i) := by
    apply CategoryTheory.WideSubcategory.hom_ext
    apply SimplexCategory.Hom.ext
    ext j
    exact congrArg Fin.val (congrFun hq j)
  have h := congrArg (fun f => eqToHom hSrc.symm ≫ f ≫ eqToHom hTgt) hβ
  simpa [β, Category.assoc] using h

end HomotopyHypothesis.Simplicial.SubdivisionComparison
