import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Interfaces.Disk0
import HomotopyHypothesis.FiniteCategory.Lifting.AfinFrame
import HomotopyHypothesis.FiniteCategory.Lifting.Assembly
import HomotopyHypothesis.FiniteCategory.Lifting.EndomorphismTheory
import HomotopyHypothesis.FiniteCategory.Lifting.FillerLift
import HomotopyHypothesis.FiniteCategory.Lifting.FiniteGlobularShapes
import HomotopyHypothesis.FiniteCategory.Lifting.FrameLift
import HomotopyHypothesis.FiniteCategory.Lifting.LiftedTheory
import HomotopyHypothesis.FiniteCategory.Lifting.ModelShapes
import HomotopyHypothesis.FiniteCategory.Lifting.RealizationStatements
/-!
# Pointed lifting from boundary realization and functor comparison

The two finite-realization inputs imply relative cofibrancy and lifting at homotopically terminal
objects. The test categories have the same universes as the finite cellular category.
-/

noncomputable section

universe u

open CategoryTheory Limits HomotopicalAlgebra
open OAI.Grothendieck HomotopyHypothesis.Blueprint HomotopyHypothesis.Henry

namespace HomotopyHypothesis.FiniteCategory.Lifting

/-- Boundary adjoints for every framed interpretation in the required universes. -/
def BoundaryAdjointFamily (C : GlobularTheory.{u}) : Prop :=
  ∀ (X : Type (u+1)) [Category.{u} X] [CategoryWithCofibrations X] [IsCofibrationCategory X]
    (R : ShapeInterpretation X) (F : FramedShapeInterpretation R)
    (a : GlobularTheory.Morphism C R.endTheory), FrameBoundaryAdjointStatement R F a

/-- Extension of representable comparisons in the required universes. -/
def AfinFunctorComparisonFamily {C : GlobularTheory.{u}} (hC : C.IsCoherator) : Prop :=
  ∀ (Y : Type (u+1)) [Category.{u} Y] [CategoryWithCofibrations Y] [IsCofibrationCategory Y]
    (F G : Afin C hC ⥤ Y) (hF : IsCofibrationMorphism F) (hG : IsCofibrationMorphism G)
    (e : afinRepresentables hC ⋙ F ≅ afinRepresentables hC ⋙ G),
    AfinFunctorComparisonStatement hC F G hF hG e

/-- Boundary realization and extension of representable comparisons imply relative cofibrancy. -/
theorem afin_isCofibrantAt_of_helpers {C : GlobularTheory.{u}} (hC : C.IsCoherator)
    (hBoundary : BoundaryAdjointFamily C) (hCompare : AfinFunctorComparisonFamily hC) :
    IsCofibrantAt.{u+1,u} (Afin C hC) (Packages.disk0 hC) := by
  intro X _ _ _ Y _ _ _ p hp x _ h hh hx
  rcases hp with ⟨hX, hY, hm, hpre, hiso, hacy⟩
  letI : IsCylinderCategory X := hX
  letI : IsCylinderCategory Y := hY
  obtain ⟨L, h₀, hpoint⟩ := liftedAfinFrame_pointed_exists hC hpre hm h hh x hx
  obtain ⟨d⟩ := liftedAfinTheory_acyclic_exists hC h hh hpre hm (hacy rfl) L
  exact d.strictLift_of_boundary_and_comparison hiso hm
    (hBoundary X (finiteFrameInterpretation L.frame L.endpoints)
      (finiteFrameFramed L.frame L.inc_cof L.endpoints) d.action)
    (fun F hF e => hCompare Y F h hF hh.toIsCofibrationMorphism e) x hx h₀ hpoint

/-- The same realization inputs imply lifting at homotopically terminal marked objects. -/
theorem afin_liftsAtHTerminal_of_helpers {C : GlobularTheory.{u}} (hC : C.IsCoherator)
    (hBoundary : BoundaryAdjointFamily C) (hCompare : AfinFunctorComparisonFamily hC) :
    LiftsAtHTerminal.{u+1,u} (Afin C hC) (Packages.disk0 hC) := by
  intro X _ _ _ Y _ _ _ p hp x hxGood h hh hx
  rcases hp with ⟨hX, hY, hm, hpre, hiso, _⟩
  letI : IsCylinderCategory X := hX
  letI : IsCylinderCategory Y := hY
  change IsHTerminal x ∧ IsHTerminal (p.obj x) at hxGood
  obtain ⟨L, h₀, hpoint⟩ := liftedAfinFrame_pointed_exists hC hpre hm h hh x hx
  have hL₀ : IsHTerminal (L.frame.obj 0) := by rw [h₀]; exact hxGood.1
  have hpL₀ : IsHTerminal (p.obj (L.frame.obj 0)) := by rw [h₀]; exact hxGood.2
  obtain ⟨d⟩ := liftedAfinTheory_hterminal_exists hC h hh hpre hm L hL₀ hpL₀
  exact d.strictLift_of_boundary_and_comparison hiso hm
    (hBoundary X (finiteFrameInterpretation L.frame L.endpoints)
      (finiteFrameFramed L.frame L.inc_cof L.endpoints) d.action)
    (fun F hF e => hCompare Y F h hF hh.toIsCofibrationMorphism e) x hx h₀ hpoint

#print axioms afin_isCofibrantAt_of_helpers
#print axioms afin_liftsAtHTerminal_of_helpers

end HomotopyHypothesis.FiniteCategory.Lifting
