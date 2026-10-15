import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import HomotopyHypothesis.Blueprint.Defs
/-!+# Models represented by a theory interpretation

A globular-sum preserving interpretation of a globular theory in a category defines a
model-valued nerve. The partial left adjoint of this nerve is defined on the representable
models and on initial models.
-/

noncomputable section

universe u v

open CategoryTheory Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Blueprint

namespace HomotopyHypothesis.FiniteCategory.Lifting

variable {C : GlobularTheory.{v}} {X : Type u} [Category.{v} X]

/-- An interpretation of a globular theory that preserves its defining globular sums. -/
structure TheoryInterpretation (C : GlobularTheory.{v}) (X : Type u) [Category.{v} X] where
  functor : C.Obj ⥤ X
  sums : ∀ (S : Shape) (b h : ℕ) (hl : b < S.1) (hr : b < h),
    IsPushout (functor.map (C.base (S.seam hl))) (functor.map (C.base (Shape.face hr false)))
      (functor.map (C.base (S.inl b h hl hr))) (functor.map (C.base (S.inr b h hl hr)))

namespace TheoryInterpretation

/-- The model of maps from the interpreted shapes into an object. -/
def model (R : TheoryInterpretation C X) (Y : X) : C.Model where
  presheaf := R.functor.op ⋙ yoneda.obj Y
  sums S b h hl hr := ((R.sums S b h hl hr).op.map (yoneda.obj Y)).flip

/-- The model-valued nerve associated to an interpretation. -/
def nerve (R : TheoryInterpretation C X) : X ⥤ C.Model where
  obj := R.model
  map f := Functor.whiskerLeft R.functor.op (yoneda.map f)
  map_id Y := by
    apply NatTrans.ext
    funext S
    apply ConcreteCategory.hom_ext
    intro a
    exact Category.comp_id a
  map_comp f g := by
    apply NatTrans.ext
    funext S
    apply ConcreteCategory.hom_ext
    intro a
    exact (Category.assoc a f g).symm

/-- The value of an interpretation corepresents maps out of the corresponding free shape. -/
def freeShapeCorepresentable (R : TheoryInterpretation C X) (S : Shape) :
    (R.nerve ⋙ coyoneda.obj (op (freeShape C S))).CorepresentableBy
      (R.functor.obj ⟨S⟩) where
  homEquiv {Y} := (yonedaEquiv (F := (R.model Y).presheaf) (X := (⟨S⟩ : C.Obj))).symm
  homEquiv_comp {Y Y'} f g := by
    change (yonedaEquiv (F := (R.model Y').presheaf)).symm (g ≫ f) =
      (yonedaEquiv (F := (R.model Y).presheaf)).symm g ≫ R.nerve.map f
    exact (yonedaEquiv_symm_naturality_right (⟨S⟩ : C.Obj) (R.nerve.map f) g).symm

/-- A partial left adjoint to the nerve is defined at every free shape. -/
theorem freeShape_leftAdjointObjIsDefined (R : TheoryInterpretation C X) (S : Shape) :
    R.nerve.leftAdjointObjIsDefined (freeShape C S) :=
  (R.freeShapeCorepresentable S).isCorepresentable

/-- Initial objects corepresent maps from initial models into the nerve. -/
def initialCorepresentable (R : TheoryInterpretation C X)
    {I : C.Model} (hI : IsInitial I) {O : X} (hO : IsInitial O) :
    (R.nerve ⋙ coyoneda.obj (op I)).CorepresentableBy O where
  homEquiv {Y} :=
    { toFun := fun _ => hI.to (R.nerve.obj Y)
      invFun := fun _ => hO.to Y
      left_inv := fun _ => hO.hom_ext _ _
      right_inv := fun _ => hI.hom_ext _ _ }
  homEquiv_comp _ _ := hI.hom_ext _ _

/-- A partial left adjoint to the nerve is defined at an initial model. -/
theorem initial_leftAdjointObjIsDefined (R : TheoryInterpretation C X)
    {I : C.Model} (hI : IsInitial I) {O : X} (hO : IsInitial O) :
    R.nerve.leftAdjointObjIsDefined I := (R.initialCorepresentable hI hO).isCorepresentable

/-- Restrict the partial left adjoint to finite cellular objects once its domain contains them. -/
def finiteRealization (R : TheoryInterpretation C X) (hC : C.IsCoherator)
    (h : ∀ M : C.Model, IsFinitelyCellular C M → R.nerve.leftAdjointObjIsDefined M) :
    Afin C hC ⥤ X :=
  ObjectProperty.lift R.nerve.leftAdjointObjIsDefined (Afin.ι hC)
    (fun M => h M.obj M.property) ⋙ R.nerve.partialLeftAdjoint

end TheoryInterpretation

#print axioms TheoryInterpretation.freeShape_leftAdjointObjIsDefined
#print axioms TheoryInterpretation.initial_leftAdjointObjIsDefined

end HomotopyHypothesis.FiniteCategory.Lifting
