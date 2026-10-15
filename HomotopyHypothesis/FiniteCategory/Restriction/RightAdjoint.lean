import Mathlib.CategoryTheory.Adjunction.Restrict
import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.FinCellEssentiallySmall
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Blueprint.Henry.Topology
universe u

open CategoryTheory Limits HomotopicalAlgebra TopCat HomotopyHypothesis.Henry

namespace HomotopyHypothesis.FiniteCategory.Restriction

theorem finCellRestriction_isRightAdjoint_proof
    (hι : IsCellularRealization (ObjectProperty.ι Top.IsFiniteCellComplex.{u})) :
    (topRestriction hι).IsRightAdjoint := by
  letI : EssentiallySmall.{u} FinCell.{u} :=
    HomotopyHypothesis.Henry.Packages.finCell_essentiallySmall
  let S := SmallModel (FinCell.{u})
  letI : SmallCategory S := inferInstance
  let e : FinCell.{u} ≌ S := equivSmallModel (FinCell.{u})
  let M : FinCell.{u} ⥤ TopCat.{u} := ObjectProperty.ι Top.IsFiniteCellComplex.{u}
  let A : S ⥤ TopCat.{u} := e.inverse ⋙ M
  let U : S ⥤ Sᵒᵖ ⥤ Type u := uliftYoneda.{u}
  let Ls : (Sᵒᵖ ⥤ Type u) ⥤ TopCat.{u} := U.leftKanExtension A
  let Ks : TopCat.{u} ⥤ Sᵒᵖ ⥤ Type u := Presheaf.restrictedULiftYoneda A
  let α := U.leftKanExtensionUnit A
  have adjS : Ls ⊣ Ks := by
    exact Presheaf.uliftYonedaAdjunction.{0} Ls α
  let eP : (FinCell.{u}ᵒᵖ ⥤ Type u) ≌ (Sᵒᵖ ⥤ Type u) := e.op.congrLeft
  let j : Completion.{u} FinCell.{u} ⥤ FinCell.{u}ᵒᵖ ⥤ Type u :=
    ObjectProperty.ι (IsCompletionPresheaf FinCell.{u})
  let iC : Completion.{u} FinCell.{u} ⥤ Sᵒᵖ ⥤ Type u := j ⋙ eP.functor
  let L : Completion.{u} FinCell.{u} ⥤ TopCat.{u} := iC ⋙ Ls
  let R := topRestriction hι
  have hiC : iC.FullyFaithful := by
    exact (ObjectProperty.fullyFaithfulι _).comp eP.fullyFaithfulFunctor
  have hId : (𝟭 TopCat.{u}).FullyFaithful := Functor.FullyFaithful.id _
  let rawC : TopCat.{u} ⥤ FinCell.{u}ᵒᵖ ⥤ Type u :=
    yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj M.op
  let rawS : TopCat.{u} ⥤ Sᵒᵖ ⥤ Type u :=
    yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj A.op
  have hLift : R ⋙ j ≅ rawC := by
    dsimp [R, topRestriction, restrictionAlong, j, rawC, M]
    exact ObjectProperty.liftCompιIso _ _ _
  have hRaw : rawS ≅ rawC ⋙ eP.functor := by
    dsimp [rawS, rawC, eP, A, M]
    rfl
  have hR : Ks ≅ R ⋙ iC := by
    dsimp [Ks, iC, j, eP]
    calc
      Presheaf.restrictedULiftYoneda A ≅ rawS := by
        simpa only [Presheaf.restrictedULiftYoneda] using
          (Functor.isoWhiskerRight (uliftYonedaIsoYoneda.{u} (C := TopCat.{u}))
            ((Functor.whiskeringLeft _ _ _).obj A.op))
      _ ≅ rawC ⋙ eP.functor := hRaw
      _ ≅ R ⋙ j ⋙ eP.functor := Functor.isoWhiskerRight hLift.symm eP.functor
      _ ≅ R ⋙ (j ⋙ eP.functor) := Iso.refl _
  have adj : L ⊣ R :=
    adjS.restrictFullyFaithful hiC hId (Functor.rightUnitor L).symm
      ((Functor.leftUnitor Ks) ≪≫ hR)
  exact ⟨L, ⟨adj⟩⟩

end HomotopyHypothesis.FiniteCategory.Restriction

#print axioms HomotopyHypothesis.FiniteCategory.Restriction.finCellRestriction_isRightAdjoint_proof
