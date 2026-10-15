import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Interfaces.Disk0
import HomotopyHypothesis.FiniteCategory.Lifting.AfinFrame
import HomotopyHypothesis.FiniteCategory.Lifting.AfinInterpretation
import HomotopyHypothesis.FiniteCategory.Lifting.EndomorphismTheory
import HomotopyHypothesis.FiniteCategory.Lifting.Exactness
import HomotopyHypothesis.FiniteCategory.Lifting.FiniteGlobularShapes
import HomotopyHypothesis.FiniteCategory.Lifting.FrameLift
import HomotopyHypothesis.FiniteCategory.Lifting.FrameShapes
import HomotopyHypothesis.FiniteCategory.Lifting.LiftedShapes
import HomotopyHypothesis.FiniteCategory.Lifting.LiftedTheory
import HomotopyHypothesis.FiniteCategory.Lifting.ModelShapes
import HomotopyHypothesis.FiniteCategory.Lifting.Nerve
import HomotopyHypothesis.FiniteCategory.Lifting.RealizationComparison
/-!
# Pointed strictification of finite realization

The comparison on representables determines the prescribed comparison at the zero disk.
An extension of this comparison therefore strictifies while retaining the marked object.
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

/-- The interpretation supplied by the lifted coherator action. -/
def interpretation (d : LiftedAfinTheory hC h hh L) : TheoryInterpretation C X :=
  (finiteFrameInterpretation L.frame L.endpoints).interpretation d.action

variable (d : LiftedAfinTheory hC h hh L)
  (H : ∀ M : C.Model, IsFinitelyCellular C M → d.interpretation.nerve.leftAdjointObjIsDefined M)

/-- Compare the finite realization and the original functor on representables. -/
def realizationComparison :
    afinRepresentables hC ⋙ (d.interpretation.finiteRealization hC H ⋙ p) ≅
      afinRepresentables hC ⋙ h :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (d.interpretation.finiteRealizationRepresentablesIso hC H) p ≪≫
      d.comparison

set_option backward.isDefEq.respectTransparency false in
/-- The comparison has the specified lifted-frame component at every disk. -/
theorem realizationComparison_globe_hom (n : ℕ) :
    ((d.realizationComparison H).app (⟨Shape.globe n⟩ : C.Obj)).hom =
      p.map ((d.interpretation.finiteRealizationRepresentablesIso hC H).app
        (⟨Shape.globe n⟩ : C.Obj)).hom ≫
          p.map ((frameSmallGlobesComparison L.frame).app (Globe.mk n)).inv ≫
            (L.objIso n).hom := by
  change 𝟙 _ ≫ (p.map ((d.interpretation.finiteRealizationRepresentablesIso hC H).app
      (⟨Shape.globe n⟩ : C.Obj)).hom ≫ (d.comparison.app (⟨Shape.globe n⟩ : C.Obj)).hom) = _
  rw [d.comparison_globe]
  simp only [Category.id_comp, liftedShapeGlobeIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_inv]

/-- The finite realization carries the zero disk to the chosen marked object up to isomorphism. -/
def realizationPointIso (x : X) (h₀ : L.frame.obj 0 = x) :
    (d.interpretation.finiteRealization hC H).obj (Packages.disk0 hC) ≅ x :=
  (d.interpretation.finiteRealizationRepresentablesIso hC H).app (⟨Shape.globe 0⟩ : C.Obj) ≪≫
    ((frameSmallGlobesComparison L.frame).app (Globe.mk 0)).symm ≪≫ eqToIso h₀

set_option backward.isDefEq.respectTransparency false in
/-- Any extension of the representable comparison has the required marked-point coherence. -/
theorem realizationPointIso_over
    (α : d.interpretation.finiteRealization hC H ⋙ p ≅ h)
    (hα : Functor.isoWhiskerLeft (afinRepresentables hC) α = d.realizationComparison H)
    (x : X) (hx : h.obj (Packages.disk0 hC) = p.obj x) (h₀ : L.frame.obj 0 = x)
    (hpoint : L.objIso 0 = eqToIso (congrArg p.obj h₀) ≪≫ eqToIso hx.symm) :
    p.map (d.realizationPointIso H x h₀).hom =
      (α.app (Packages.disk0 hC)).hom ≫ eqToHom hx := by
  have hα₀ := congrArg (fun e => (e.app (⟨Shape.globe 0⟩ : C.Obj)).hom) hα
  change (α.app (Packages.disk0 hC)).hom =
    ((d.realizationComparison H).app (⟨Shape.globe 0⟩ : C.Obj)).hom at hα₀
  rw [hα₀, d.realizationComparison_globe_hom H 0]
  have hp₀ : p.map (eqToHom h₀) = eqToHom (congrArg p.obj h₀) := by
    cases h₀
    exact p.map_id _
  change p.map (((d.interpretation.finiteRealizationRepresentablesIso hC H).app
      (⟨Shape.globe 0⟩ : C.Obj)).hom ≫
        ((frameSmallGlobesComparison L.frame).app (Globe.mk 0)).inv ≫ eqToHom h₀) = _
  simp only [p.map_comp, hp₀, hpoint, Iso.trans_hom, eqToIso.hom, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- An extension of the representable comparison gives a strict pointed cylinder-morphism lift. -/
theorem strictLift_of_realizationComparison (hp : IsIsofibration p)
    (hF : IsCofibrationMorphism (d.interpretation.finiteRealization hC H))
    (α : d.interpretation.finiteRealization hC H ⋙ p ≅ h)
    (hα : Functor.isoWhiskerLeft (afinRepresentables hC) α = d.realizationComparison H)
    (x : X) (hx : h.obj (Packages.disk0 hC) = p.obj x) (h₀ : L.frame.obj 0 = x)
    (hpoint : L.objIso 0 = eqToIso (congrArg p.obj h₀) ≪≫ eqToIso hx.symm) :
    ∃ l : Afin C hC ⥤ X,
      IsCylinderMorphism l ∧ l ⋙ p = h ∧ l.obj (Packages.disk0 hC) = x := by
  have hFCyl : IsCylinderMorphism (d.interpretation.finiteRealization hC H) :=
    d.interpretation.finiteRealization_isCylinderMorphism hC H hF
      (finiteFrame_action_source_weak L.frame L.endpoints d.action)
  exact strictify_pointed_cylinder hp _ hFCyl h α (Packages.disk0 hC) x hx
    (d.realizationPointIso H x h₀) (d.realizationPointIso_over H α hα x hx h₀ hpoint)

#print axioms realizationComparison_globe_hom
#print axioms realizationPointIso_over
#print axioms strictLift_of_realizationComparison

end LiftedAfinTheory

end HomotopyHypothesis.FiniteCategory.Lifting
