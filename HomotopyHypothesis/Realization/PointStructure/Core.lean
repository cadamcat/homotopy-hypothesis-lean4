import Mathlib.CategoryTheory.Limits.Presheaf
import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Realization.PointStructure

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

noncomputable abbrev realizationElementsDiagram (X : Henry.SemiSSet.{u}) :=
  (Functor.Elements.π X).leftOp ⋙ Henry.SemiSSet.toTop.{u}

noncomputable def realizationRepresentableIso :
    Henry.SemiSSet.stdSimplex.{u} ⋙ Henry.SemiSSet.realization.{u} ≅
      Henry.SemiSSet.toTop.{u} :=
  Presheaf.isExtensionAlongULiftYoneda.{0, 0, u, 0, u + 1}
    Henry.SemiSSet.toTop.{u}

noncomputable def realizationElementsDiagramIso (X : Henry.SemiSSet.{u}) :
    Presheaf.functorToRepresentables.{u} X ⋙ Henry.SemiSSet.realization.{u} ≅
      realizationElementsDiagram X := by
  change (((Functor.Elements.π X).leftOp ⋙ uliftYoneda.{u}) ⋙
      Henry.SemiSSet.realization.{u}) ≅ realizationElementsDiagram X
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Functor.Elements.π X).leftOp realizationRepresentableIso

noncomputable def realizationElementsCocone (X : Henry.SemiSSet.{u}) :
    Cocone (realizationElementsDiagram X) :=
  (Cocone.precompose (realizationElementsDiagramIso X).inv).obj
    (Henry.SemiSSet.realization.{u}.mapCocone (Presheaf.coconeOfRepresentable X))

noncomputable def realizationElementsCocone_isColimit (X : Henry.SemiSSet.{u}) :
    IsColimit (realizationElementsCocone X) := by
  letI : PreservesColimitsOfSize.{0, u, u, u, u + 1, u + 1}
      Henry.SemiSSet.realization.{u} :=
    Presheaf.preservesColimitsOfSize_leftKanExtension.{0, 0, u, 0, 0, u + 1, u}
      Henry.SemiSSet.toTop.{u}
  exact (IsColimit.precomposeHomEquiv (realizationElementsDiagramIso X).symm
      (Henry.SemiSSet.realization.{u}.mapCocone (Presheaf.coconeOfRepresentable X))).symm
    (isColimitOfPreserves Henry.SemiSSet.realization.{u} (Presheaf.colimitOfRepresentable X))

noncomputable def realizationElementsColimitIso (X : Henry.SemiSSet.{u}) :
    Henry.SemiSSet.realization.{u}.obj X ≅ colimit (realizationElementsDiagram X) :=
  (realizationElementsCocone_isColimit X).coconePointUniqueUpToIso (colimit.isColimit _)

noncomputable def simplexElement {X : Henry.SemiSSet.{u}} {n : ℕ}
    (y : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶ X) :
    X.Elements := Functor.elementsMk X (op (Henry.SemiSimplexCategory.mk n))
      (uliftYonedaEquiv y)

theorem simplexChar_colimit {X : Henry.SemiSSet.{u}} {n : ℕ}
    (y : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶ X) :
    Henry.SemiSSet.simplexChar.{u} y ≫ (realizationElementsColimitIso X).hom =
      colimit.ι (realizationElementsDiagram X) (op (simplexElement y)) := by
  let j := op (simplexElement y)
  have hleg :
      (realizationElementsDiagramIso X).inv.app j =
        (uliftYoneda.{u, 0, 0}.leftKanExtensionUnit Henry.SemiSSet.toTop.{u}).app
          (Henry.SemiSimplexCategory.mk n) := by
    change (realizationRepresentableIso.inv.app ((Functor.Elements.π X).leftOp.obj j)) = _
    simp [j, realizationRepresentableIso, Presheaf.isExtensionAlongULiftYoneda,
      simplexElement]
    rfl
  have h := (realizationElementsCocone_isColimit X).comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit _) (op (simplexElement y))
  have hy : (Presheaf.coconeOfRepresentable X).ι.app j = y := by
    change uliftYonedaEquiv.symm (uliftYonedaEquiv y) = y
    exact Equiv.symm_apply_apply _ _
  change ((realizationElementsDiagramIso X).inv.app j ≫ Henry.SemiSSet.realization.{u}.map
      ((Presheaf.coconeOfRepresentable X).ι.app j)) ≫
      (realizationElementsColimitIso X).hom = colimit.ι _ j at h
  rw [hy, hleg] at h
  change (((uliftYoneda.{u, 0, 0}.leftKanExtensionUnit Henry.SemiSSet.toTop.{u}).app
      (Henry.SemiSimplexCategory.mk n)) ≫ Henry.SemiSSet.realization.{u}.map y) ≫
      (realizationElementsColimitIso X).hom =
    colimit.ι (realizationElementsDiagram X) j at h
  change (((uliftYoneda.{u, 0, 0}.leftKanExtensionUnit Henry.SemiSSet.toTop.{u}).app
      (Henry.SemiSimplexCategory.mk n)) ≫ Henry.SemiSSet.realization.{u}.map y) ≫
      (realizationElementsColimitIso X).hom =
    colimit.ι (realizationElementsDiagram X) j
  exact h

theorem sharp_mk_face {X : SemiSSet.{u}} {n k m : ℕ}
    (ι : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk m)
    (v : Fin (n + 1) → Fin (k + 1))
    (x : X.obj (op (Henry.SemiSimplexCategory.mk m))) :
    sharpMk (ι.1.toOrderHom ∘ v) x =
      sharpMk v (X.map ι.op x) := by
  let L := Henry.SemiSimplexCategory.toFinFun.op
  let E := L.leftKanExtension X
  let vf : (⟨n⟩ : Henry.FinFun) ⟶ ⟨k⟩ := v
  let iF : (⟨k⟩ : Henry.FinFun) ⟶ ⟨m⟩ := Henry.SemiSimplexCategory.toFinFun.map ι
  change (E.map (Quiver.Hom.op (vf ≫ iF))
      (((L.leftKanExtensionUnit X).app (op (Henry.SemiSimplexCategory.mk m))) x)) =
    (E.map (Quiver.Hom.op vf))
      (((L.leftKanExtensionUnit X).app (op (Henry.SemiSimplexCategory.mk k)))
        ((X.map ι.op) x))
  have hcomp :
      (Quiver.Hom.op (vf ≫ iF) :
        Opposite.op (⟨m⟩ : Henry.FinFun) ⟶ Opposite.op ⟨n⟩) =
      (Quiver.Hom.op iF :
        Opposite.op (⟨m⟩ : Henry.FinFun) ⟶ Opposite.op ⟨k⟩) ≫
      (Quiver.Hom.op vf : Opposite.op (⟨k⟩ : Henry.FinFun) ⟶ Opposite.op ⟨n⟩) := by
    rw [← op_comp]
  rw [hcomp, Functor.map_comp]
  have hη :
      ((L.leftKanExtensionUnit X).app (op (Henry.SemiSimplexCategory.mk k)))
          ((X.map ι.op) x) =
        (E.map (Quiver.Hom.op iF))
          (((L.leftKanExtensionUnit X).app (op (Henry.SemiSimplexCategory.mk m))) x) := by
    have hn := NatTrans.naturality (L.leftKanExtensionUnit X) ι.op
    change X.map ι.op ≫ (L.leftKanExtensionUnit X).app
        (op (Henry.SemiSimplexCategory.mk k)) =
      (L.leftKanExtensionUnit X).app (op (Henry.SemiSimplexCategory.mk m)) ≫
        E.map (Quiver.Hom.op iF) at hn
    exact congrArg (fun f : X.obj (op (Henry.SemiSimplexCategory.mk m)) ⟶
        E.obj (op (⟨k⟩ : Henry.FinFun)) => f x) hn
  change (E.map vf.op) (E.map iF.op
      (((L.leftKanExtensionUnit X).app (op (Henry.SemiSimplexCategory.mk m))) x)) =
    (E.map vf.op) (((L.leftKanExtensionUnit X).app (op (Henry.SemiSimplexCategory.mk k)))
      ((X.map ι.op) x))
  exact congrArg (fun z => E.map vf.op z) hη.symm

end HomotopyHypothesis.Realization.PointStructure
