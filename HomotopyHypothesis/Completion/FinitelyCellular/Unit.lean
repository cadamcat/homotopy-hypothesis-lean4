import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Interfaces.Restriction
import HomotopyHypothesis.Completion.FinitelyCellular.Afin
import HomotopyHypothesis.Completion.FinitelyCellular.Phi
import HomotopyHypothesis.Completion.FinitelyCellular.Theta
/-
# The unit isomorphism for the comparison.

For a model `M`, the double restriction `Φ(R(M))` at `X` is
`Hom(F(X), M)`, which is `M(X)` by the Yoneda lemma.
-/

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck
open HomotopyHypothesis.Blueprint
open HomotopyHypothesis.Henry

noncomputable section

namespace HomotopyHypothesis.Completion.FinitelyCellular

universe u

variable {C : GlobularTheory.{u}} (hC : C.IsCoherator)

/-- The unit map `M ⟶ Φ(R(M))` at an object, via Yoneda. -/
def unitApp (M : C.Model) {X : C.Objᵒᵖ}
    (x : M.presheaf.obj X) :
    ((Phi hC).obj ((Packages.restriction hC).obj M)).presheaf.obj X :=
  yonedaEquiv.symm (by simpa using x)

/-- The unit map as a natural transformation of presheaves. -/
def unitNat (M : C.Model) :
    NatTrans M.presheaf (((Phi hC).obj ((Packages.restriction hC).obj M)).presheaf) where
  app X := ↾(fun x => unitApp hC M x)
  naturality := by
    intro X Y v
    apply ConcreteCategory.hom_ext
    intro x
    have hL : (ConcreteCategory.hom (M.presheaf.map v ≫ ↾(fun y => unitApp hC M y))) x =
        unitApp hC M (M.presheaf.map v x) := rfl
    have hR : (ConcreteCategory.hom (↾(fun y => unitApp hC M y) ≫
        (((Phi hC).obj ((Packages.restriction hC).obj M)).presheaf.map v))) x =
        (((Phi hC).obj ((Packages.restriction hC).obj M)).presheaf.map v) (unitApp hC M x) := rfl
    have hmap : (((Phi hC).obj ((Packages.restriction hC).obj M)).presheaf.map v)
        (unitApp hC M x) =
        (yoneda.map v.unop ≫ unitApp hC M x : NatTrans _ _) := rfl
    have hmid : unitApp hC M (M.presheaf.map v x) =
        yoneda.map v.unop ≫ unitApp hC M x := by
      show yonedaEquiv.symm (M.presheaf.map v x) =
        yoneda.map v.unop ≫ yonedaEquiv.symm x
      have h := yonedaEquiv_symm_naturality_left v.unop M.presheaf (by simpa using x)
      simpa [Quiver.Hom.op_unop] using h.symm
    exact hL.trans (hmid.trans hR.symm)

/-- The inverse unit map, via Yoneda. -/
def invApp (M : C.Model) {X : C.Objᵒᵖ}
    (y : ((Phi hC).obj ((Packages.restriction hC).obj M)).presheaf.obj X) :
    M.presheaf.obj X :=
  yonedaEquiv (X := X.unop) y

/-- Pointwise isomorphism for the unit. -/
def unitIsoApp (M : C.Model) (X : C.Objᵒᵖ) :
    M.presheaf.obj X ≅
      ((Phi hC).obj ((Packages.restriction hC).obj M)).presheaf.obj X where
  hom := ↾(fun x => unitApp hC M x)
  inv := ↾(fun y => invApp hC M y)
  hom_inv_id := by
    apply ConcreteCategory.hom_ext
    intro x
    show invApp hC M (unitApp hC M x) = x
    show yonedaEquiv (yonedaEquiv.symm _) = _
    exact yonedaEquiv.apply_symm_apply _
  inv_hom_id := by
    apply ConcreteCategory.hom_ext
    intro y
    show unitApp hC M (invApp hC M y) = y
    show yonedaEquiv.symm (yonedaEquiv _) = _
    exact yonedaEquiv.symm_apply_apply _

/-- The unit isomorphism of presheaves. -/
def unitIsoPresheaf (M : C.Model) :
    M.presheaf ≅ (((Phi hC).obj ((Packages.restriction hC).obj M)).presheaf) :=
  NatIso.ofComponents (fun X => unitIsoApp hC M X)
    (fun {X Y} v => (unitNat hC M).naturality v)

/-- The unit isomorphism of models. -/
def unitIsoModel (M : C.Model) :
    M ≅ ((Packages.restriction hC ⋙ Phi hC).obj M) where
  hom := (unitIsoPresheaf hC M).hom
  inv := (unitIsoPresheaf hC M).inv
  hom_inv_id := (unitIsoPresheaf hC M).hom_inv_id
  inv_hom_id := (unitIsoPresheaf hC M).inv_hom_id

/-- The unit isomorphism between functors, natural in the model. -/
def unitNatIso :
    𝟭 C.Model ≅ Packages.restriction hC ⋙ Phi hC :=
  NatIso.ofComponents (fun M => unitIsoModel hC M) (by
    intro X Y f
    show (_ : NatTrans X.presheaf ((Phi hC).obj ((Packages.restriction hC).obj Y)).presheaf) = _
    apply NatTrans.ext
    funext Z
    apply ConcreteCategory.hom_ext
    intro x
    have hL : (ConcreteCategory.hom (((𝟭 C.Model).map f ≫ (unitIsoModel hC Y).hom).app Z)) x =
        unitApp hC Y (f.app Z x) := rfl
    have hR : (ConcreteCategory.hom (((unitIsoModel hC X).hom ≫ (Packages.restriction hC ⋙ Phi hC).map f).app Z)) x =
        (((Packages.restriction hC ⋙ Phi hC).map f).app Z) (unitApp hC X x) := rfl
    have hmap : (((Packages.restriction hC ⋙ Phi hC).map f).app Z) (unitApp hC X x) =
        unitApp hC X x ≫ f := rfl
    have hmid : unitApp hC Y (f.app Z x) =
        unitApp hC X x ≫ f := by
      have h := yonedaEquiv_symm_naturality_right (X := Z.unop)
        (F := X.presheaf) (F' := Y.presheaf) (f := f) (x := x)
      exact h.symm
    exact hL.trans (hmid.trans hR.symm))

end HomotopyHypothesis.Completion.FinitelyCellular
