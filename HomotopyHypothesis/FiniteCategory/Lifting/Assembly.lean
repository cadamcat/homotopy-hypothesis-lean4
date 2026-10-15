import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Interfaces.Disk0
import HomotopyHypothesis.FiniteCategory.Realization.FiniteRealizationStatement
import HomotopyHypothesis.FiniteCategory.Lifting.AfinFrame
import HomotopyHypothesis.FiniteCategory.Lifting.EndomorphismTheory
import HomotopyHypothesis.FiniteCategory.Lifting.FiniteGlobularShapes
import HomotopyHypothesis.FiniteCategory.Lifting.FrameLift
import HomotopyHypothesis.FiniteCategory.Lifting.HelperStatements
import HomotopyHypothesis.FiniteCategory.Lifting.LiftedTheory
import HomotopyHypothesis.FiniteCategory.Lifting.ModelShapes
import HomotopyHypothesis.FiniteCategory.Lifting.Nerve
import HomotopyHypothesis.FiniteCategory.Lifting.PointedRealization
import HomotopyHypothesis.FiniteCategory.Lifting.RealizationStatements
/-!
# Assembling pointed lifts from finite realization

Representable boundary adjoints produce a finite realization. Extending its comparison on
representables then gives a strict lift with the prescribed zero disk.
-/

noncomputable section

universe u v

open CategoryTheory Limits HomotopicalAlgebra
open OAI.Grothendieck HomotopyHypothesis.Blueprint HomotopyHypothesis.Henry

namespace HomotopyHypothesis.FiniteCategory.Lifting

variable {C : GlobularTheory.{u}} {hC : C.IsCoherator}
  {X : Type v} [Category.{u} X] [CategoryWithCofibrations X]
  [CategoryWithWeakEquivalences X] [IsCylinderCategory X]
  {Y : Type (u+1)} [Category.{u} Y] [CategoryWithCofibrations Y]
  [CategoryWithWeakEquivalences Y] [IsCylinderCategory Y]
  {p : X ⥤ Y} {h : Afin C hC ⥤ Y} {hh : IsCylinderMorphism h}
  {L : LiftedFrame p (imageDiskFrame hC h hh)}

namespace LiftedAfinTheory

/-- Boundary realization and extension of representable comparisons complete a pointed lift. -/
theorem strictLift_of_boundary_and_comparison (d : LiftedAfinTheory hC h hh L)
    (hp : IsIsofibration p) (hm : IsCylinderMorphism p)
    (hbd : FrameBoundaryAdjointStatement (finiteFrameInterpretation L.frame L.endpoints)
      (finiteFrameFramed L.frame L.inc_cof L.endpoints) d.action)
    (hCompare : ∀ (F : Afin C hC ⥤ Y) (hF : IsCofibrationMorphism F)
      (e : afinRepresentables hC ⋙ F ≅ afinRepresentables hC ⋙ h),
      AfinFunctorComparisonStatement hC F h hF hh.toIsCofibrationMorphism e)
    (x : X) (hx : h.obj (Packages.disk0 hC) = p.obj x) (h₀ : L.frame.obj 0 = x)
    (hpoint : L.objIso 0 = eqToIso (congrArg p.obj h₀) ≪≫ eqToIso hx.symm) :
    ∃ l : Afin C hC ⥤ X,
      IsCylinderMorphism l ∧ l ⋙ p = h ∧ l.obj (Packages.disk0 hC) = x := by
  obtain ⟨hb, hc⟩ := hbd
  obtain ⟨H, hF⟩ :=
    FiniteCategory.Realization.finiteRealizationStatement_proof hC d.interpretation hb hc
  let F := d.interpretation.finiteRealization hC H
  have hFp : IsCofibrationMorphism (F ⋙ p) :=
    { map_cofibration := fun {A B} f hf => hm.map_cofibration _ (hF.map_cofibration f hf)
      map_initial := by
        intro I hI
        obtain ⟨hFI⟩ := hF.map_initial hI
        exact hm.map_initial hFI
      map_isPushout := by
        intro A B Z Q i f k j hs hi
        exact hm.map_isPushout _ _ _ _ (hF.map_isPushout i f k j hs hi)
          (hF.map_cofibration i hi) }
  obtain ⟨α, hα⟩ := hCompare (F ⋙ p) hFp (d.realizationComparison H)
  exact d.strictLift_of_realizationComparison H hp hF α hα x hx h₀ hpoint

#print axioms strictLift_of_boundary_and_comparison

end LiftedAfinTheory

end HomotopyHypothesis.FiniteCategory.Lifting
