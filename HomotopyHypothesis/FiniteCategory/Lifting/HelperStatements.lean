import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.FiniteCategory.Subcategory.DiskFinitelyCellular
import HomotopyHypothesis.FiniteCategory.Lifting.Nerve
noncomputable section

universe u v

open CategoryTheory Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Blueprint HomotopyHypothesis.Henry

namespace HomotopyHypothesis.FiniteCategory.Lifting

/-- Finite cellular objects lie in the domain of the partial left adjoint, and the resulting
functor is a morphism of cofibration categories, when the boundary generators have cofibrant
images. -/
def FiniteRealizationStatement {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    {X : Type u} [Category.{v} X] [CategoryWithCofibrations X] [IsCofibrationCategory X]
    (R : TheoryInterpretation C X)
    (hb : ∀ n, R.nerve.leftAdjointObjIsDefined (boundaryDisk C n))
    (_hc : ∀ n, cofibrations X (R.nerve.partialLeftAdjoint.map
      (ObjectProperty.homMk (I C n) :
        (⟨boundaryDisk C n, hb n⟩ : R.nerve.PartialLeftAdjointSource) ⟶
          ⟨disk C n, R.freeShape_leftAdjointObjIsDefined (Shape.globe n)⟩))) : Prop :=
  ∃ H : ∀ M : C.Model, IsFinitelyCellular C M → R.nerve.leftAdjointObjIsDefined M,
    IsCofibrationMorphism (R.finiteRealization hC H)

/-- The source endpoint between finite cellular disks. -/
def finiteEndpoint {C : GlobularTheory.{v}} (hC : C.IsCoherator) (n : ℕ) :
    (⟨disk C n, FiniteCategory.Subcategory.disk_finitelyCellular_proof C n⟩ : Afin C hC) ⟶
      ⟨disk C (n+1), FiniteCategory.Subcategory.disk_finitelyCellular_proof C (n+1)⟩ :=
  ObjectProperty.homMk (J C n)

/-- Preserving the generating cylinder endpoints and cofibration colimits is enough to preserve
all weak equivalences between finite cellular models. -/
def EndpointExactnessStatement {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    {X : Type u} [Category.{v} X] [CategoryWithCofibrations X]
    [CategoryWithWeakEquivalences X] [IsCylinderCategory X] : Prop :=
  ∀ F : Afin C hC ⥤ X, IsCofibrationMorphism F →
    (∀ n, weakEquivalences X (F.map (finiteEndpoint hC n))) → IsCylinderMorphism F

/-- Homotopical terminality is invariant under weak equivalences. -/
def HTerminalInvariantStatement (X : Type u) [Category.{v} X]
    [CategoryWithCofibrations X] [CategoryWithWeakEquivalences X] [IsCylinderCategory X] : Prop :=
  ∀ {A B : X} (w : A ⟶ B), weakEquivalences X w → (IsHTerminal A ↔ IsHTerminal B)

end HomotopyHypothesis.FiniteCategory.Lifting
