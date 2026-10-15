import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.FiniteCategory.Lifting.AfinInterpretation
import HomotopyHypothesis.FiniteCategory.Lifting.EndomorphismTheory
import HomotopyHypothesis.FiniteCategory.Lifting.FillerLift
import HomotopyHypothesis.FiniteCategory.Lifting.ModelShapes
import HomotopyHypothesis.FiniteCategory.Lifting.Nerve
universe u v

open CategoryTheory Limits HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Blueprint HomotopyHypothesis.Henry

namespace HomotopyHypothesis.FiniteCategory.Lifting

/-- A framed theory interpretation realizes model boundaries, with cofibrant boundary
inclusions under the partial adjoint of its nerve. -/
def FrameBoundaryAdjointStatement {C : GlobularTheory.{u}} {X : Type v} [Category.{u} X]
    [CategoryWithCofibrations X] [IsCofibrationCategory X]
    (R : ShapeInterpretation X) (_F : FramedShapeInterpretation R)
    (a : GlobularTheory.Morphism C R.endTheory) : Prop :=
  ∃ hb : ∀ n, (R.interpretation a).nerve.leftAdjointObjIsDefined (boundaryDisk C n),
    ∀ n, cofibrations X ((R.interpretation a).nerve.partialLeftAdjoint.map
      (ObjectProperty.homMk (I C n) :
        (⟨boundaryDisk C n, hb n⟩ : (R.interpretation a).nerve.PartialLeftAdjointSource) ⟶
          ⟨disk C n, (R.interpretation a).freeShape_leftAdjointObjIsDefined (Shape.globe n)⟩))

/-- Isomorphisms between the representable restrictions of exact finite-cell functors extend to
the finite cellular category, retaining their prescribed components on representables. -/
def AfinFunctorComparisonStatement {C : GlobularTheory.{u}} (hC : C.IsCoherator)
    {Y : Type v} [Category.{u} Y] [CategoryWithCofibrations Y] [IsCofibrationCategory Y]
    (F G : Afin C hC ⥤ Y) (_hF : IsCofibrationMorphism F) (_hG : IsCofibrationMorphism G)
    (e : afinRepresentables hC ⋙ F ≅ afinRepresentables hC ⋙ G) : Prop :=
  ∃ α : F ≅ G, Functor.isoWhiskerLeft (afinRepresentables hC) α = e

end HomotopyHypothesis.FiniteCategory.Lifting
