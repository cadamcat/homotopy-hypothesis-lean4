import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Comparison.GlobularShapes.ShapeComparison
import HomotopyHypothesis.FiniteCategory.Lifting.AfinFrame
import HomotopyHypothesis.FiniteCategory.Lifting.AfinInterpretation
import HomotopyHypothesis.FiniteCategory.Lifting.EndomorphismTheory
import HomotopyHypothesis.FiniteCategory.Lifting.FillerLift
import HomotopyHypothesis.FiniteCategory.Lifting.FiniteGlobularShapes
import HomotopyHypothesis.FiniteCategory.Lifting.FrameLift
import HomotopyHypothesis.FiniteCategory.Lifting.LiftedShapes
import HomotopyHypothesis.FiniteCategory.Lifting.ModelShapes
import HomotopyHypothesis.FiniteCategory.Lifting.Nerve
import HomotopyHypothesis.FiniteCategory.Lifting.TerminalShapes
/-!
# Lifting the coherator action on a globular frame

The shape comparison and filler lifting extend the action of a cellular coherator to a lifted
frame. The resulting theory comparison retains the prescribed isomorphisms on disks.
-/

noncomputable section

universe u v v₁

open CategoryTheory Limits HomotopicalAlgebra
open OAI.Grothendieck HomotopyHypothesis.Blueprint HomotopyHypothesis.Henry

namespace HomotopyHypothesis.FiniteCategory.Lifting

section Comparisons

variable {X : Type v} [Category.{u} X] {Y : Type v₁} [Category.{u} Y]

set_option backward.isDefEq.respectTransparency false in
/-- Equality after applying an endomorphism-theory map induces a comparison of interpretations. -/
def interpretationComparison {C : GlobularTheory.{u}}
    (R : ShapeInterpretation X) (S : ShapeInterpretation Y) (p : X ⥤ Y)
    (α : R.functor ⋙ p ≅ S.functor) (a : GlobularTheory.Morphism C R.endTheory)
    (f : GlobularTheory.Morphism C S.endTheory) (ha : a.comp (R.map S p α) = f) :
    (R.interpretation a).functor ⋙ p ≅ (S.interpretation f).functor :=
  NatIso.ofComponents (fun T => α.app T.shape) (by
    intro A B g
    have hg := congrArg (fun z : GlobularTheory.Morphism C S.endTheory => z.map g) ha
    change (α.app A.shape).inv ≫ p.map (a.map g) ≫ (α.app B.shape).hom = f.map g at hg
    change p.map (a.map g) ≫ (α.app B.shape).hom = (α.app A.shape).hom ≫ f.map g
    rw [← cancel_epi (α.app A.shape).inv]
    simpa only [ShapeInterpretation.endTheory, ShapeInterpretation.endData, Category.assoc,
      Iso.inv_hom_id_assoc] using hg)

end Comparisons

variable {C : GlobularTheory.{u}} (hC : C.IsCoherator)
  {X : Type v} [Category.{u} X] [CategoryWithCofibrations X]
  [CategoryWithWeakEquivalences X] [IsCylinderCategory X]
  {Y : Type (u+1)} [Category.{u} Y] [CategoryWithCofibrations Y]
  [CategoryWithWeakEquivalences Y] [IsCylinderCategory Y]
  {p : X ⥤ Y} (h : Afin C hC ⥤ Y) (hh : IsCylinderMorphism h)

/-- The lifted shape diagram compares to the original one with the specified disk components. -/
theorem liftedAfinShapes_comparison (hm : IsCylinderMorphism p)
    (L : LiftedFrame p (imageDiskFrame hC h hh)) :
    ∃ α : (finiteFrameInterpretation L.frame L.endpoints).functor ⋙ p ≅
        (afinShapeInterpretation hC h hh).functor,
      ∀ n, α.app (Shape.globe n) = liftedShapeGlobeIso hC h hh L n :=
  Comparison.GlobularShapes.shapeComparisonStatement_proof
    (finiteFrameInterpretation L.frame L.endpoints) (afinShapeInterpretation hC h hh) p
    hm.toIsCofibrationMorphism (finiteFrame_seam_cof L.frame L.endpoints)
    (liftedShapeGlobeIso hC h hh L) (liftedShapeGlobeIso_source hC h hh L)
    (liftedShapeGlobeIso_target hC h hh L)

/-- A coherator action on the lifted frame, together with its prescribed comparison. -/
structure LiftedAfinTheory (L : LiftedFrame p (imageDiskFrame hC h hh)) where
  shapeIso : (finiteFrameInterpretation L.frame L.endpoints).functor ⋙ p ≅
    (afinShapeInterpretation hC h hh).functor
  globe : ∀ n, shapeIso.app (Shape.globe n) = liftedShapeGlobeIso hC h hh L n
  action : GlobularTheory.Morphism C (finiteFrameInterpretation L.frame L.endpoints).endTheory
  commutes : action.comp ((finiteFrameInterpretation L.frame L.endpoints).map
    (afinShapeInterpretation hC h hh) p shapeIso) = afinTheoryMorphism hC h hh

/-- Filler lifting yields a lifted coherator action with the prescribed disk comparisons. -/
theorem liftedAfinTheory_exists (hm : IsCylinderMorphism p)
    (L : LiftedFrame p (imageDiskFrame hC h hh))
    (hFill : ∀ α : (finiteFrameInterpretation L.frame L.endpoints).functor ⋙ p ≅
        (afinShapeInterpretation hC h hh).functor,
      GlobularTheory.LiftsFillers ((finiteFrameInterpretation L.frame L.endpoints).map
        (afinShapeInterpretation hC h hh) p α)) :
    Nonempty (LiftedAfinTheory hC h hh L) := by
  obtain ⟨α, hα⟩ := liftedAfinShapes_comparison hC h hh hm L
  obtain ⟨a, ha⟩ := hC.1.some.lift
    ((finiteFrameInterpretation L.frame L.endpoints).map (afinShapeInterpretation hC h hh) p α)
    (hFill α) (afinTheoryMorphism hC h hh)
  exact ⟨⟨α, hα, a, ha⟩⟩

/-- Acyclic pre-fibrations lift the coherator action on the finite frame. -/
theorem liftedAfinTheory_acyclic_exists (hp : IsPreFibration p) (hm : IsCylinderMorphism p)
    (ha : IsAcyclic p) (L : LiftedFrame p (imageDiskFrame hC h hh)) :
    Nonempty (LiftedAfinTheory hC h hh L) :=
  liftedAfinTheory_exists hC h hh hm L (fun α =>
    (finiteFrameFramed L.frame L.inc_cof L.endpoints).liftsFillers_acyclic
      (afinShapeInterpretation hC h hh) hp hm ha α)

/-- The coherator action also lifts when both marked disks are h-terminal. -/
theorem liftedAfinTheory_hterminal_exists (hp : IsPreFibration p) (hm : IsCylinderMorphism p)
    (L : LiftedFrame p (imageDiskFrame hC h hh))
    (h₀ : IsHTerminal (L.frame.obj 0)) (hp₀ : IsHTerminal (p.obj (L.frame.obj 0))) :
    Nonempty (LiftedAfinTheory hC h hh L) :=
  liftedAfinTheory_exists hC h hh hm L (fun α =>
    (finiteFrameFramed L.frame L.inc_cof L.endpoints).liftsFillers_hterminal
      (afinShapeInterpretation hC h hh) hp hm α
      (finiteFrame_shapes_hterminal_over L.frame L.endpoints p hm h₀ hp₀))

namespace LiftedAfinTheory

variable {hC h hh} {L : LiftedFrame p (imageDiskFrame hC h hh)}

/-- The lifted theory interpretation compares to the original functor on representables. -/
def comparison (d : LiftedAfinTheory hC h hh L) :
    ((finiteFrameInterpretation L.frame L.endpoints).interpretation d.action).functor ⋙ p ≅
      afinRepresentables hC ⋙ h :=
  interpretationComparison _ _ p d.shapeIso d.action (afinTheoryMorphism hC h hh) d.commutes

/-- Its comparison at each disk is exactly the comparison prescribed by the lifted frame. -/
theorem comparison_globe (d : LiftedAfinTheory hC h hh L) (n : ℕ) :
    d.comparison.app (⟨Shape.globe n⟩ : C.Obj) = liftedShapeGlobeIso hC h hh L n :=
  d.globe n

end LiftedAfinTheory

#print axioms liftedAfinShapes_comparison
#print axioms liftedAfinTheory_acyclic_exists
#print axioms liftedAfinTheory_hterminal_exists
#print axioms LiftedAfinTheory.comparison_globe

end HomotopyHypothesis.FiniteCategory.Lifting
