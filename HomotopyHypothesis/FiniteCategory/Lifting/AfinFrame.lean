import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Interfaces.Disk0
import HomotopyHypothesis.Blueprint.Interfaces.WeakEquivalenceClosure
import HomotopyHypothesis.FiniteCategory.Subcategory.DiskFinitelyCellular
import HomotopyHypothesis.Cylinder.FiniteCellCategory.CellCylinders
import HomotopyHypothesis.Cylinder.FiniteCellCategory.Cofibrations
import HomotopyHypothesis.Cylinder.FiniteCellCategory.FiniteCells
import HomotopyHypothesis.Cylinder.FiniteCellCategory.WeakEquivalences
import HomotopyHypothesis.FiniteCategory.Lifting.FrameLift
/-!
# The finite cellular disk frame

The disk frame of a globular theory lies in its finite cellular models. Its image under a
cylinder morphism has the codiagonal factorizations used to construct a lifted globular frame.
-/

noncomputable section

universe u

open CategoryTheory Limits HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Blueprint HomotopyHypothesis.Henry
open HomotopyHypothesis.Cylinder.FiniteCellCategory

namespace HomotopyHypothesis.FiniteCategory.Lifting

variable {C : GlobularTheory.{u}} (hC : C.IsCoherator)

/-- Boundary disks are finite cellular models. -/
theorem boundary_finitelyCellular (C : GlobularTheory.{u}) (n : ℕ) :
    IsFinitelyCellular C (boundaryDisk C n) := by
  cases n with
  | zero => exact initial_finitelyCellular C
  | succ n =>
    exact isFinitelyCellular_of_finiteCellMap (FiniteCategory.Subcategory.disk_finitelyCellular_proof C n)
      (pushout.inr (I C n) (I C n))
      ((finiteCellMaps C).of_isPushout (IsPushout.of_hasPushout (I C n) (I C n)).flip
        (finiteCellMaps_I n))

/-- The globular boundary frame inside finite cellular models. -/
def afinDiskFrame : GlobularFrame (Afin C hC) where
  obj n := ⟨disk C n, FiniteCategory.Subcategory.disk_finitelyCellular_proof C n⟩
  bd n := ⟨boundaryDisk C n, boundary_finitelyCellular C n⟩
  inc n := ObjectProperty.homMk (I C n)
  left n := ObjectProperty.homMk (pushout.inl (I C n) (I C n))
  right n := ObjectProperty.homMk (pushout.inr (I C n) (I C n))
  square n := IsPushout.of_map_of_faithful (Afin.ι hC) (IsPushout.of_hasPushout _ _)
  initial := IsInitial.ofUniqueHom (fun M => ObjectProperty.homMk (initial.to M.obj))
    (fun _ _ => by apply ObjectProperty.hom_ext; exact initialIsInitial.hom_ext _ _)

/-- Boundary inclusions are cofibrations of the finite cellular category. -/
theorem afinDiskFrame_inc_cof (n : ℕ) : cofibrations (Afin C hC) ((afinDiskFrame hC).inc n) :=
  finiteCellMaps_I n

/-- The unit map of the finite cellular disk frame. -/
def afinDiskUnit (n : ℕ) : (afinDiskFrame hC).obj (n+1) ⟶ (afinDiskFrame hC).obj n :=
  ObjectProperty.homMk (unitMap C hC n)

/-- The source endpoint followed by the unit is the identity. -/
theorem afinDiskFrame_left_unit (n : ℕ) :
    (afinDiskFrame hC).left n ≫ (afinDiskFrame hC).inc (n+1) ≫ afinDiskUnit hC n = 𝟙 _ := by
  apply ObjectProperty.hom_ext
  change pushout.inl (I C n) (I C n) ≫ I C (n+1) ≫ unitMap C hC n = 𝟙 _
  exact (boundary_inl_I_assoc n (unitMap C hC n)).trans (J_comp_unitMap C hC n)

/-- The target endpoint followed by the unit is the identity. -/
theorem afinDiskFrame_right_unit (n : ℕ) :
    (afinDiskFrame hC).right n ≫ (afinDiskFrame hC).inc (n+1) ≫ afinDiskUnit hC n = 𝟙 _ := by
  apply ObjectProperty.hom_ext
  change pushout.inr (I C n) (I C n) ≫ I C (n+1) ≫ unitMap C hC n = 𝟙 _
  exact (boundary_inr_I_assoc n (unitMap C hC n)).trans (target_comp_unitMap hC n)

/-- The auxiliary unit leg is a weak equivalence. -/
theorem afinDiskUnit_weak (n : ℕ) : weakEquivalences (Afin C hC) (afinDiskUnit hC n) := by
  change W hC (unitMap C hC n)
  have hJ : W hC (J C n) := source_llp_weakEquivalence hC _
    ((sourceMaps C).le_llp_rlp _ (MorphismProperty.ofHoms.mk n))
    (finiteCellMaps_le_cofibrations C _ (FiniteCategory.Subcategory.disk_finitelyCellular_proof C n))
  apply (W hC).of_precomp (J C n) (unitMap C hC n) hJ
  rw [J_comp_unitMap]
  exact (Packages.weakEquivalence_closure hC).1 _ inferInstance

variable {Y : Type (u+1)} [Category.{u} Y] [CategoryWithCofibrations Y]
  [CategoryWithWeakEquivalences Y]

/-- The disk frame after applying an exact functor. -/
def imageDiskFrame (h : Afin C hC ⥤ Y) (hm : IsCylinderMorphism h) : GlobularFrame Y where
  obj n := h.obj ((afinDiskFrame hC).obj n)
  bd n := h.obj ((afinDiskFrame hC).bd n)
  inc n := h.map ((afinDiskFrame hC).inc n)
  left n := h.map ((afinDiskFrame hC).left n)
  right n := h.map ((afinDiskFrame hC).right n)
  square n := hm.map_isPushout _ _ _ _ ((afinDiskFrame hC).square n) (afinDiskFrame_inc_cof hC n)
  initial := Classical.choice (hm.map_initial (afinDiskFrame hC).initial)

/-- Every exact functor out of finite cellular models has a lifted disk frame along a
pre-fibration, with the specified zero disk. -/
theorem liftedAfinFrame_exists
    {X : Type (u+1)} [Category.{u} X] [CategoryWithCofibrations X]
    [CategoryWithWeakEquivalences X] [IsCylinderCategory X] [IsCylinderCategory Y]
    {p : X ⥤ Y} (hp : IsPreFibration p) (hm : IsCylinderMorphism p)
    (h : Afin C hC ⥤ Y) (hh : IsCylinderMorphism h) (x : X)
    (hx : h.obj (Packages.disk0 hC) = p.obj x) :
    ∃ L : LiftedFrame p (imageDiskFrame hC h hh), L.frame.obj 0 = x := by
  apply liftedFrame_exists hp hm (imageDiskFrame hC h hh)
    (fun n => hh.map_cofibration _ (afinDiskFrame_inc_cof hC n))
    (fun n => h.map (afinDiskUnit hC n))
    (fun n => hh.map_weakEquivalence _ (afinDiskUnit_weak hC n))
    (fun n => ?_) (fun n => ?_) x (eqToIso hx.symm)
  · change h.map ((afinDiskFrame hC).left n) ≫ h.map ((afinDiskFrame hC).inc (n+1)) ≫
      h.map (afinDiskUnit hC n) = 𝟙 _
    rw [← h.map_comp, ← h.map_comp, afinDiskFrame_left_unit, h.map_id]
  · change h.map ((afinDiskFrame hC).right n) ≫ h.map ((afinDiskFrame hC).inc (n+1)) ≫
      h.map (afinDiskUnit hC n) = 𝟙 _
    rw [← h.map_comp, ← h.map_comp, afinDiskFrame_right_unit, h.map_id]

/-- The finite-cell disk frame has a lift with the prescribed comparison at the zero disk. -/
theorem liftedAfinFrame_pointed_exists
    {X : Type (u+1)} [Category.{u} X] [CategoryWithCofibrations X]
    [CategoryWithWeakEquivalences X] [IsCylinderCategory X] [IsCylinderCategory Y]
    {p : X ⥤ Y} (hp : IsPreFibration p) (hm : IsCylinderMorphism p)
    (h : Afin C hC ⥤ Y) (hh : IsCylinderMorphism h) (x : X)
    (hx : h.obj (Packages.disk0 hC) = p.obj x) :
    ∃ L : LiftedFrame p (imageDiskFrame hC h hh), ∃ h₀ : L.frame.obj 0 = x,
      L.objIso 0 = eqToIso (congrArg p.obj h₀) ≪≫ eqToIso hx.symm := by
  apply liftedFrame_pointed_exists hp hm (imageDiskFrame hC h hh)
    (fun n => hh.map_cofibration _ (afinDiskFrame_inc_cof hC n))
    (fun n => h.map (afinDiskUnit hC n))
    (fun n => hh.map_weakEquivalence _ (afinDiskUnit_weak hC n))
    (fun n => ?_) (fun n => ?_) x (eqToIso hx.symm)
  · change h.map ((afinDiskFrame hC).left n) ≫ h.map ((afinDiskFrame hC).inc (n+1)) ≫
      h.map (afinDiskUnit hC n) = 𝟙 _
    rw [← h.map_comp, ← h.map_comp, afinDiskFrame_left_unit, h.map_id]
  · change h.map ((afinDiskFrame hC).right n) ≫ h.map ((afinDiskFrame hC).inc (n+1)) ≫
      h.map (afinDiskUnit hC n) = 𝟙 _
    rw [← h.map_comp, ← h.map_comp, afinDiskFrame_right_unit, h.map_id]

#print axioms boundary_finitelyCellular
#print axioms afinDiskUnit_weak
#print axioms liftedAfinFrame_exists
#print axioms liftedAfinFrame_pointed_exists

end HomotopyHypothesis.FiniteCategory.Lifting
