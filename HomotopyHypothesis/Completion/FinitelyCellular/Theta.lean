import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Interfaces.Restriction
import HomotopyHypothesis.Completion.FinitelyCellular.Afin
import HomotopyHypothesis.Completion.FinitelyCellular.Phi
/-
# The canonical comparison map into the restricted Yoneda image.

For `P` in the completion and `A` in `Afin`, an element `x ∈ P(A)` induces
a model map `ιA ⟶ Φ(P)` whose components send `z ∈ A(X)` to `P(z̃)(x)`,
where `z̃ : F(X) → A` is the map classified by `z`.  This is natural in `A`.
-/

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck
open HomotopyHypothesis.Blueprint
open HomotopyHypothesis.Henry

noncomputable section

namespace HomotopyHypothesis.Completion.FinitelyCellular

universe u

variable {C : GlobularTheory.{u}} (hC : C.IsCoherator)

/-- The Afin map classified by an element, via Yoneda and fullness. -/
def elemMap (A : Afin C hC) {X : C.Objᵒᵖ}
    (z : ((Afin.ι hC).obj A).presheaf.obj X) :
    (FreeAfin hC).obj X.unop ⟶ A :=
  ObjectProperty.homMk ((yonedaEquiv (X := X.unop)).symm (by simp only [Opposite.op_unop]; exact z) : NatTrans _ _)

/-- The classifying map is natural in the element. -/
theorem elemMap_natural (A : Afin C hC) {X Y : C.Objᵒᵖ} (v : X ⟶ Y)
    (z : ((Afin.ι hC).obj A).presheaf.obj X) :
    elemMap hC A (((Afin.ι hC).obj A).presheaf.map v z) =
      (FreeAfin hC).map v.unop ≫ elemMap hC A z := by
  apply ObjectProperty.hom_ext
  show (yonedaEquiv.symm _ : NatTrans (yoneda.obj Y.unop) ((Afin.ι hC).obj A).presheaf) =
    ((yoneda.map _ ≫ yonedaEquiv.symm _) : NatTrans (yoneda.obj Y.unop) ((Afin.ι hC).obj A).presheaf)
  exact (yonedaEquiv_symm_naturality_left _ _ _).symm

/-- The classifying map is natural for postcomposition. -/
theorem elemMap_postnatural (B' A' : Afin C hC) (k : B' ⟶ A')
    {Y : C.Objᵒᵖ} (w : ((Afin.ι hC).obj B').presheaf.obj Y) :
    elemMap hC A' (((Afin.ι hC).map k).app Y w) =
      elemMap hC B' w ≫ k := by
  apply ObjectProperty.hom_ext
  show (yonedaEquiv.symm _ : NatTrans (yoneda.obj Y.unop) ((Afin.ι hC).obj A').presheaf) =
    ((yonedaEquiv.symm _ ≫ _) : NatTrans (yoneda.obj Y.unop) ((Afin.ι hC).obj A').presheaf)
  exact (yonedaEquiv_symm_naturality_right _ _ _).symm.trans (congrArg _ rfl)

/-- The component of the comparison map at `A` and `X`. -/
def thetaComp (P : Completion.{u} (Afin C hC)) (A : Afin C hC)
    (x : P.obj.obj (op A)) {X : C.Objᵒᵖ}
    (z : ((Afin.ι hC).obj A).presheaf.obj X) :
    P.obj.obj (op ((FreeAfin hC).obj X.unop)) :=
  P.obj.map (elemMap hC A z).op x

/-- The comparison map `ιA ⟶ Φ(P)` induced by `x ∈ P(A)`. -/
def thetaMap (P : Completion.{u} (Afin C hC)) (A : Afin C hC)
    (x : P.obj.obj (op A)) :
    NatTrans ((Afin.ι hC).obj A).presheaf ((Phi hC).obj P).presheaf where
  app X := ↾(fun z => thetaComp hC P A x z)
  naturality := by
    intro X Y v
    apply ConcreteCategory.hom_ext
    intro z
    have eL : P.obj.map (elemMap hC A (((Afin.ι hC).obj A).presheaf.map v z)).op x =
        thetaComp hC P A x (((Afin.ι hC).obj A).presheaf.map v z) := rfl
    have r1 : ((Phi hC).obj P).presheaf.map v (thetaComp hC P A x z) =
        P.obj.map ((FreeAfin hC).map v.unop).op (P.obj.map (elemMap hC A z).op x) := rfl
    have r3 : P.obj.map ((FreeAfin hC).map v.unop).op (P.obj.map (elemMap hC A z).op x) =
        P.obj.map ((elemMap hC A z).op ≫ ((FreeAfin hC).map v.unop).op) x :=
      ConcreteCategory.congr_hom (P.obj.map_comp _ _).symm x
    have r4 : P.obj.map ((elemMap hC A z).op ≫ ((FreeAfin hC).map v.unop).op) x =
        P.obj.map (((FreeAfin hC).map v.unop ≫ elemMap hC A z)).op x :=
      congrArg (fun K => P.obj.map K x) op_comp.symm
    have mid : P.obj.map (elemMap hC A (((Afin.ι hC).obj A).presheaf.map v z)).op x =
        P.obj.map (((FreeAfin hC).map v.unop ≫ elemMap hC A z)).op x :=
      congrArg (fun E : (FreeAfin hC).obj Y.unop ⟶ A => P.obj.map E.op x)
        (elemMap_natural hC A v z)
    have sL : thetaComp hC P A x (((Afin.ι hC).obj A).presheaf.map v z) =
        P.obj.map (elemMap hC A (((Afin.ι hC).obj A).presheaf.map v z)).op x := rfl
    have sR : ((Phi hC).obj P).presheaf.map v (thetaComp hC P A x z) =
        P.obj.map (((FreeAfin hC).map v.unop ≫ elemMap hC A z)).op x :=
      r1.trans (r3.trans r4)
    have sL0 : (ConcreteCategory.hom (((Afin.ι hC).obj A).presheaf.map v ≫
          ↾(fun w => thetaComp hC P A x w))) z =
        thetaComp hC P A x (((Afin.ι hC).obj A).presheaf.map v z) := rfl
    have sR0 : (ConcreteCategory.hom ((↾(fun w => thetaComp hC P A x w)) ≫
          ((Phi hC).obj P).presheaf.map v)) z =
        ((Phi hC).obj P).presheaf.map v (thetaComp hC P A x z) := rfl
    exact sL0.trans (eL.symm.trans (mid.trans (sR0.trans sR).symm))

/-- The comparison natural transformation `P ⇒ R(Φ(P))`. -/
def theta (P : Completion.{u} (Afin C hC)) :
    NatTrans P.obj (((Packages.restriction hC).obj ((Phi hC).obj P)).obj) where
  app A := ↾(fun x => thetaMap hC P A.unop (by simpa using x))
  naturality := by
    intro A B g
    apply ConcreteCategory.hom_ext
    intro x
    -- Both sides are model maps `ιB' ⟶ Φ(P)`; compare as presheaf maps.
    show (_ : NatTrans ((Afin.ι hC).obj B.unop).presheaf ((Phi hC).obj P).presheaf) = _
    apply NatTrans.ext
    funext Y
    apply ConcreteCategory.hom_ext
    intro w
    -- Unfold both sides to `P.map _ _` terms.
    have hL : (ConcreteCategory.hom (((ConcreteCategory.hom (P.obj.map g ≫ ↾fun x => thetaMap hC P (unop B) (id x))) x).app Y)) w =
        P.obj.map (elemMap hC B.unop w).op (P.obj.map g x) := rfl
    have hR : (ConcreteCategory.hom
            (((ConcreteCategory.hom
                    ((↾fun x => thetaMap hC P (unop A) (id x)) ≫
                      ((Packages.restriction hC).obj ((Phi hC).obj P)).obj.map g))
                x).app
              Y))
          w =
        P.obj.map (elemMap hC A.unop (((Afin.ι hC).map g.unop).app Y w)).op x := by
      rfl
    have hpost : elemMap hC A.unop (((Afin.ι hC).map g.unop).app Y w) =
        elemMap hC B.unop w ≫ g.unop :=
      elemMap_postnatural hC B.unop A.unop g.unop w
    have hcomp : P.obj.map (elemMap hC B.unop w).op (P.obj.map g x) =
        P.obj.map (g ≫ (elemMap hC B.unop w).op) x :=
      ConcreteCategory.congr_hom (P.obj.map_comp _ _).symm x
    have hop : (g ≫ (elemMap hC B.unop w).op) =
        (elemMap hC B.unop w ≫ g.unop).op := by
      simp only [op_comp, Quiver.Hom.op_unop]
    have hmid : P.obj.map (elemMap hC B.unop w).op (P.obj.map g x) =
        P.obj.map (elemMap hC A.unop (((Afin.ι hC).map g.unop).app Y w)).op x := by
      rw [hcomp, hop, hpost]
    exact hL.trans (hmid.trans hR.symm)

end HomotopyHypothesis.Completion.FinitelyCellular
