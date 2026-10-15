import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Cylinder.FiniteCellCategory.CellCylinders
import HomotopyHypothesis.FiniteCategory.Lifting.AfinFrame
import HomotopyHypothesis.FiniteCategory.Lifting.AfinInterpretation
import HomotopyHypothesis.FiniteCategory.Lifting.EndomorphismTheory
import HomotopyHypothesis.FiniteCategory.Lifting.FillerLift
import HomotopyHypothesis.FiniteCategory.Lifting.FiniteGlobularShapes
import HomotopyHypothesis.FiniteCategory.Lifting.FrameLift
import HomotopyHypothesis.FiniteCategory.Lifting.FrameShapes
import HomotopyHypothesis.FiniteCategory.Lifting.ModelShapes
import HomotopyHypothesis.FiniteCategory.Lifting.ShapeComparisonStatement
import HomotopyHypothesis.FiniteCategory.Lifting.TerminalShapes
/-!
# Comparing lifted finite globular sums

The realized frame has cofibrant globular-sum seams. Its comparison on disks is compatible
with both endpoints, so a comparison on all finite shapes can retain the prescribed disk data.
-/

noncomputable section

universe u v

open CategoryTheory Limits HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Blueprint HomotopyHypothesis.Henry

namespace HomotopyHypothesis.FiniteCategory.Lifting

variable {X : Type v} [Category.{u} X] [CategoryWithCofibrations X]
  [CategoryWithWeakEquivalences X] [IsCylinderCategory X]

/-- The gluing seams of the finite frame realization are cofibrations. -/
theorem finiteFrame_seam_cof (B : GlobularFrame X)
    (hB : ∀ n,
      (cofibrations X (B.diagram.source n) ∧ weakEquivalences X (B.diagram.source n)) ∧
        (cofibrations X (B.diagram.target n) ∧ weakEquivalences X (B.diagram.target n)))
    (S : Shape) (b : ℕ) (hb : b < S.1) :
    cofibrations X ((finiteFrameInterpretation B hB).functor.map (S.seam hb)) := by
  change cofibrations X
    ((finiteFrameRealization B hB).map (Shape.face hb true ≫ lastShapeInclusion S))
  rw [Functor.map_comp]
  exact (IsCofibrationCategory.isMultiplicative (C := X)).comp_mem _ _
    (frameSmallFace_trivial B hB hb true).1 (finiteFrame_last_trivial B hB S).1

variable {C : GlobularTheory.{u}} (hC : C.IsCoherator)
  {Y : Type (u+1)} [Category.{u} Y] [CategoryWithCofibrations Y]
  [CategoryWithWeakEquivalences Y]

/-- The source map of the image disk frame agrees with the interpreted source operation. -/
theorem imageDiskFrame_source (h : Afin C hC ⥤ Y) (hh : IsCylinderMorphism h) (n : ℕ) :
    (imageDiskFrame hC h hh).diagram.source n =
      (afinShapeInterpretation hC h hh).functor.map (Shape.source n) := by
  change h.map ((afinDiskFrame hC).left n) ≫ h.map ((afinDiskFrame hC).inc (n+1)) =
    h.map ((afinShapeDiagram hC).map (Shape.source n))
  rw [← h.map_comp]
  congr 1
  apply ObjectProperty.hom_ext
  exact Cylinder.FiniteCellCategory.boundary_inl_I n

/-- The target map of the image disk frame agrees with the interpreted target operation. -/
theorem imageDiskFrame_target (h : Afin C hC ⥤ Y) (hh : IsCylinderMorphism h) (n : ℕ) :
    (imageDiskFrame hC h hh).diagram.target n =
      (afinShapeInterpretation hC h hh).functor.map (Shape.target n) := by
  change h.map ((afinDiskFrame hC).right n) ≫ h.map ((afinDiskFrame hC).inc (n+1)) =
    h.map ((afinShapeDiagram hC).map (Shape.target n))
  rw [← h.map_comp]
  congr 1
  apply ObjectProperty.hom_ext
  exact Cylinder.FiniteCellCategory.boundary_inr_I n

variable {p : X ⥤ Y} (h : Afin C hC ⥤ Y) (hh : IsCylinderMorphism h)

/-- The disk comparison induced by a lifted frame and its finite realization. -/
def liftedShapeGlobeIso (L : LiftedFrame p (imageDiskFrame hC h hh)) (n : ℕ) :
    p.obj ((finiteFrameInterpretation L.frame L.endpoints).functor.obj (Shape.globe n)) ≅
      (afinShapeInterpretation hC h hh).functor.obj (Shape.globe n) :=
  (p.mapIso ((frameSmallGlobesComparison L.frame).app (Globe.mk n))).symm ≪≫ L.objIso n

variable [IsCylinderCategory Y]

set_option backward.isDefEq.respectTransparency false in
/-- The realized disk comparisons commute with source operations. -/
theorem liftedShapeGlobeIso_source (L : LiftedFrame p (imageDiskFrame hC h hh)) (n : ℕ) :
    p.map ((finiteFrameInterpretation L.frame L.endpoints).functor.map (Shape.source n)) ≫
        (liftedShapeGlobeIso hC h hh L (n+1)).hom =
      (liftedShapeGlobeIso hC h hh L n).hom ≫
        (afinShapeInterpretation hC h hh).functor.map (Shape.source n) := by
  let F := finiteFrameFramed L.frame L.inc_cof L.endpoints
  have hs : (finiteFrameInterpretation L.frame L.endpoints).functor.map (Shape.source n) ≫
      (F.diskIso (n+1)).inv = (F.diskIso n).inv ≫ L.frame.diagram.source n := by
    have hs := congrArg (fun f => (F.diskIso n).inv ≫ f ≫ (F.diskIso (n+1)).inv)
      (F.source n)
    simpa only [F, finiteFrameFramed, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.inv_hom_id_assoc]
      using hs.symm
  change p.map ((finiteFrameInterpretation L.frame L.endpoints).functor.map (Shape.source n)) ≫
      (p.map (F.diskIso (n+1)).inv ≫ (L.objIso (n+1)).hom) =
    (p.map (F.diskIso n).inv ≫ (L.objIso n).hom) ≫ _
  calc
    _ = p.map ((finiteFrameInterpretation L.frame L.endpoints).functor.map (Shape.source n) ≫
        (F.diskIso (n+1)).inv) ≫ (L.objIso (n+1)).hom := by
      rw [p.map_comp, Category.assoc]
    _ = p.map ((F.diskIso n).inv ≫ L.frame.diagram.source n) ≫
        (L.objIso (n+1)).hom := by rw [hs]
    _ = p.map (F.diskIso n).inv ≫
        (p.map (L.frame.diagram.source n) ≫ (L.objIso (n+1)).hom) := by
      rw [p.map_comp, Category.assoc]
    _ = p.map (F.diskIso n).inv ≫
        ((L.objIso n).hom ≫ (imageDiskFrame hC h hh).diagram.source n) := by
      rw [L.source_over]
    _ = _ := by rw [imageDiskFrame_source]; exact (Category.assoc _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
/-- The realized disk comparisons commute with target operations. -/
theorem liftedShapeGlobeIso_target (L : LiftedFrame p (imageDiskFrame hC h hh)) (n : ℕ) :
    p.map ((finiteFrameInterpretation L.frame L.endpoints).functor.map (Shape.target n)) ≫
        (liftedShapeGlobeIso hC h hh L (n+1)).hom =
      (liftedShapeGlobeIso hC h hh L n).hom ≫
        (afinShapeInterpretation hC h hh).functor.map (Shape.target n) := by
  let F := finiteFrameFramed L.frame L.inc_cof L.endpoints
  have ht : (finiteFrameInterpretation L.frame L.endpoints).functor.map (Shape.target n) ≫
      (F.diskIso (n+1)).inv = (F.diskIso n).inv ≫ L.frame.diagram.target n := by
    have ht := congrArg (fun f => (F.diskIso n).inv ≫ f ≫ (F.diskIso (n+1)).inv)
      (F.target n)
    simpa only [F, finiteFrameFramed, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.inv_hom_id_assoc]
      using ht.symm
  change p.map ((finiteFrameInterpretation L.frame L.endpoints).functor.map (Shape.target n)) ≫
      (p.map (F.diskIso (n+1)).inv ≫ (L.objIso (n+1)).hom) =
    (p.map (F.diskIso n).inv ≫ (L.objIso n).hom) ≫ _
  calc
    _ = p.map ((finiteFrameInterpretation L.frame L.endpoints).functor.map (Shape.target n) ≫
        (F.diskIso (n+1)).inv) ≫ (L.objIso (n+1)).hom := by
      rw [p.map_comp, Category.assoc]
    _ = p.map ((F.diskIso n).inv ≫ L.frame.diagram.target n) ≫
        (L.objIso (n+1)).hom := by rw [ht]
    _ = p.map (F.diskIso n).inv ≫
        (p.map (L.frame.diagram.target n) ≫ (L.objIso (n+1)).hom) := by
      rw [p.map_comp, Category.assoc]
    _ = p.map (F.diskIso n).inv ≫
        ((L.objIso n).hom ≫ (imageDiskFrame hC h hh).diagram.target n) := by
      rw [L.target_over]
    _ = _ := by rw [imageDiskFrame_target]; exact (Category.assoc _ _ _).symm

#print axioms finiteFrame_seam_cof
#print axioms imageDiskFrame_source
#print axioms imageDiskFrame_target
#print axioms liftedShapeGlobeIso_source
#print axioms liftedShapeGlobeIso_target

end HomotopyHypothesis.FiniteCategory.Lifting
