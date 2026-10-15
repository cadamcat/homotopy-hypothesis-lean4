import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.FiniteCategory.BoundaryExtension.EndpointExactness
import HomotopyHypothesis.FiniteCategory.Lifting.EndomorphismTheory
import HomotopyHypothesis.FiniteCategory.Lifting.Exactness
import HomotopyHypothesis.FiniteCategory.Lifting.FiniteGlobularShapes
import HomotopyHypothesis.FiniteCategory.Lifting.FrameShapes
import HomotopyHypothesis.FiniteCategory.Lifting.LiftedTheory
import HomotopyHypothesis.FiniteCategory.Lifting.ModelShapes
import HomotopyHypothesis.FiniteCategory.Lifting.Nerve
/-!
# Finite realization on representables

The partial-adjoint realization agrees naturally with the original theory interpretation on
representable objects. Preserving the source endpoints then makes it a cylinder morphism.
-/

noncomputable section

universe u v

open CategoryTheory Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Blueprint HomotopyHypothesis.Henry

namespace HomotopyHypothesis.FiniteCategory.Lifting

variable {C : GlobularTheory.{v}} {X : Type u} [Category.{v} X]

namespace TheoryInterpretation

/-- The representable diagram lies in the domain of the partial adjoint. -/
def representableDomain (R : TheoryInterpretation C X) : C.Obj ⥤ R.nerve.PartialLeftAdjointSource :=
  ObjectProperty.lift R.nerve.leftAdjointObjIsDefined (representables C)
    (fun S => R.freeShape_leftAdjointObjIsDefined S.shape)

/-- Compare an interpreted shape with its chosen partial-adjoint value. -/
def representableIso (R : TheoryInterpretation C X) (S : C.Obj) :
    R.functor.obj S ≅ (R.representableDomain ⋙ R.nerve.partialLeftAdjoint).obj S := by
  letI := (R.freeShapeCorepresentable S.shape).isCorepresentable
  exact (R.freeShapeCorepresentable S.shape).isoCoreprX

set_option backward.isDefEq.respectTransparency false in
/-- The chosen comparison carries the canonical universal element. -/
theorem representableIso_equiv (R : TheoryInterpretation C X) (S : C.Obj) :
    (R.freeShapeCorepresentable S.shape).homEquiv (R.representableIso S).hom =
      R.nerve.partialLeftAdjointHomEquiv (X := R.representableDomain.obj S) (𝟙 _) := by
  simp [representableIso, Functor.CorepresentableBy.isoCoreprX,
    Functor.CorepresentableBy.uniqueUpToIso_hom, Coyoneda.fullyFaithful_preimage,
    Functor.partialLeftAdjointHomEquiv, representableDomain]
  exact (R.freeShapeCorepresentable S.shape).homEquiv.apply_symm_apply _

set_option backward.isDefEq.respectTransparency false in
/-- The free-shape corepresentation is natural in every theory operation. -/
theorem freeShapeCorepresentable_left (R : TheoryInterpretation C X) {S T : C.Obj}
    (f : S ⟶ T) {Y : X} (a : R.functor.obj T ⟶ Y) :
    (R.freeShapeCorepresentable S.shape).homEquiv (R.functor.map f ≫ a) =
      (representables C).map f ≫ (R.freeShapeCorepresentable T.shape).homEquiv a := by
  change (yonedaEquiv (F := (R.model Y).presheaf)).symm (R.functor.map f ≫ a) =
    yoneda.map f ≫ (yonedaEquiv (F := (R.model Y).presheaf)).symm a
  exact (yonedaEquiv_symm_naturality_left f (R.model Y).presheaf a).symm

set_option backward.isDefEq.respectTransparency false in
/-- The comparisons with chosen partial-adjoint values are natural. -/
theorem representableIso_naturality (R : TheoryInterpretation C X) {S T : C.Obj} (f : S ⟶ T) :
    R.functor.map f ≫ (R.representableIso T).hom = (R.representableIso S).hom ≫
      (R.representableDomain ⋙ R.nerve.partialLeftAdjoint).map f := by
  apply (R.freeShapeCorepresentable S.shape).homEquiv.injective
  rw [freeShapeCorepresentable_left, representableIso_equiv,
    (R.freeShapeCorepresentable S.shape).homEquiv_comp, representableIso_equiv]
  change (representables C).map f ≫ R.nerve.partialLeftAdjointHomEquiv
      (X := R.representableDomain.obj T) (𝟙 _) =
    R.nerve.partialLeftAdjointHomEquiv (X := R.representableDomain.obj S) (𝟙 _) ≫
      R.nerve.map (R.nerve.partialLeftAdjoint.map (R.representableDomain.map f))
  have hl := R.nerve.partialLeftAdjointHomEquiv_map_comp (R.representableDomain.map f) (𝟙 _)
  have hr := R.nerve.partialLeftAdjointHomEquiv_comp
    (X := R.representableDomain.obj S) (𝟙 _)
    (R.nerve.partialLeftAdjoint.map (R.representableDomain.map f))
  simp only [Category.comp_id] at hl
  simp only [Category.id_comp] at hr
  exact hl.symm.trans hr

/-- Realization and interpretation agree naturally on representables. -/
def representablesIso (R : TheoryInterpretation C X) :
    R.functor ≅ R.representableDomain ⋙ R.nerve.partialLeftAdjoint :=
  NatIso.ofComponents (R.representableIso) (fun f => R.representableIso_naturality f)

/-- The restriction of finite realization to representables is the original interpretation. -/
def finiteRealizationRepresentablesIso (R : TheoryInterpretation C X) (hC : C.IsCoherator)
    (H : ∀ M : C.Model, IsFinitelyCellular C M → R.nerve.leftAdjointObjIsDefined M) :
    afinRepresentables hC ⋙ R.finiteRealization hC H ≅ R.functor :=
  R.representablesIso.symm

variable [CategoryWithCofibrations X] [CategoryWithWeakEquivalences X] [IsCylinderCategory X]

/-- Finite realization is a cylinder morphism when it preserves cofibrations and the source
operations of the interpreted theory are weak equivalences. -/
theorem finiteRealization_isCylinderMorphism (R : TheoryInterpretation C X) (hC : C.IsCoherator)
    (H : ∀ M : C.Model, IsFinitelyCellular C M → R.nerve.leftAdjointObjIsDefined M)
    (hF : IsCofibrationMorphism (R.finiteRealization hC H))
    (hJ : ∀ n, weakEquivalences X (R.functor.map (C.base (Shape.source n)))) :
    IsCylinderMorphism (R.finiteRealization hC H) := by
  apply FiniteCategory.BoundaryExtension.endpointExactnessStatement_proof hC _ hF
  intro n
  exact map_mem_of_natIso _ (IsCylinderCategory.weakEquivalences_isMultiplicative (C := X))
    (IsCylinderCategory.isomorphisms_le_weakEquivalences (C := X))
    (R.finiteRealizationRepresentablesIso hC H).symm (C.base (Shape.source n)) (hJ n)

end TheoryInterpretation

variable [CategoryWithCofibrations X] [CategoryWithWeakEquivalences X] [IsCylinderCategory X]

/-- A lifted finite-frame action interprets the source operations by weak equivalences. -/
theorem finiteFrame_action_source_weak (B : GlobularFrame X)
    (hB : ∀ n,
      (cofibrations X (B.diagram.source n) ∧ weakEquivalences X (B.diagram.source n)) ∧
        (cofibrations X (B.diagram.target n) ∧ weakEquivalences X (B.diagram.target n)))
    (a : GlobularTheory.Morphism C (finiteFrameInterpretation B hB).endTheory) (n : ℕ) :
    weakEquivalences X (((finiteFrameInterpretation B hB).interpretation a).functor.map
      (C.base (Shape.source n))) := by
  change weakEquivalences X (a.map (C.base (Shape.source n)))
  rw [a.map_base]
  exact (frameSmallFace_trivial B hB (Nat.lt_succ_self n) false).2

#print axioms TheoryInterpretation.finiteRealizationRepresentablesIso
#print axioms TheoryInterpretation.finiteRealization_isCylinderMorphism
#print axioms finiteFrame_action_source_weak

end HomotopyHypothesis.FiniteCategory.Lifting
