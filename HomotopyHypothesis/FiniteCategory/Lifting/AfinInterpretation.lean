import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.FiniteCategory.Lifting.AfinFrame
import HomotopyHypothesis.FiniteCategory.Lifting.EndomorphismTheory
import HomotopyHypothesis.FiniteCategory.Lifting.ModelShapes
import HomotopyHypothesis.FiniteCategory.Lifting.Nerve
/-!
# Theory and shape interpretations induced by finite cellular models

An exact functor from finite cellular models restricts to the representable theory diagram.
Its underlying shape diagram preserves globular sums, and the theory action gives a morphism
into that diagram's endomorphism theory.
-/

noncomputable section

universe u v

open CategoryTheory Limits HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Blueprint HomotopyHypothesis.Henry

namespace HomotopyHypothesis.FiniteCategory.Lifting

variable {C : GlobularTheory.{u}} {Y : Type v} [Category.{u} Y]

/-- Restrict a theory interpretation to its underlying shape diagram. -/
def shapeOfTheory (R : TheoryInterpretation C Y) : ShapeInterpretation Y where
  functor := C.toTheoryData.arity ⋙ R.functor
  sums := R.sums

set_option backward.isDefEq.respectTransparency false in
/-- The theory action is a morphism into its interpreted endomorphism theory. -/
def theoryToEndomorphisms (R : TheoryInterpretation C Y) :
    GlobularTheory.Morphism C (shapeOfTheory R).endTheory where
  map {S T} f := R.functor.map (show (⟨S⟩ : C.Obj) ⟶ ⟨T⟩ from f)
  map_id S := R.functor.map_id (⟨S⟩ : C.Obj)
  map_comp {A B D} f g := R.functor.map_comp
    (show (⟨A⟩ : C.Obj) ⟶ ⟨B⟩ from f) (show (⟨B⟩ : C.Obj) ⟶ ⟨D⟩ from g)
  map_base _ := rfl

variable [CategoryWithCofibrations Y] [CategoryWithWeakEquivalences Y]

set_option backward.isDefEq.respectTransparency false in
/-- The representable theory interpretation induced by an exact finite-cell functor. -/
def afinTheoryInterpretation (hC : C.IsCoherator) (h : Afin C hC ⥤ Y)
    (hh : IsCylinderMorphism h) : TheoryInterpretation C Y where
  functor := afinRepresentables hC ⋙ h
  sums S b n hl hr := hh.map_isPushout _ _ _ _
    (afinShapeDiagram_isPushout hC S b n hl hr) (afinShapeDiagram_seam_cof hC S b hl)

/-- The original finite-cell functor on the shape diagram. -/
def afinShapeInterpretation (hC : C.IsCoherator) (h : Afin C hC ⥤ Y)
    (hh : IsCylinderMorphism h) : ShapeInterpretation Y :=
  shapeOfTheory (afinTheoryInterpretation hC h hh)

/-- The coherator action on the original functor's interpreted shapes. -/
def afinTheoryMorphism (hC : C.IsCoherator) (h : Afin C hC ⥤ Y)
    (hh : IsCylinderMorphism h) :
    GlobularTheory.Morphism C (afinShapeInterpretation hC h hh).endTheory :=
  theoryToEndomorphisms (afinTheoryInterpretation hC h hh)

#print axioms afinTheoryInterpretation
#print axioms afinTheoryMorphism

end HomotopyHypothesis.FiniteCategory.Lifting
