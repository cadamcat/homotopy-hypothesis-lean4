import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.FiniteCategory.Subcategory.DiskFinitelyCellular
import HomotopyHypothesis.Cylinder.FiniteCellCategory.CellCylinders
import HomotopyHypothesis.Cylinder.FiniteCellCategory.FiniteCells
import HomotopyHypothesis.FiniteCategory.Lifting.EndomorphismTheory
import HomotopyHypothesis.FiniteCategory.Lifting.FiniteGlobularShapes
import HomotopyHypothesis.FiniteCategory.Lifting.FunctorFaceClosure
/-!
# Globular sums of representable models

Representable models preserve the globular sums of a theory, by the defining pullback condition
of its models and the Yoneda lemma.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Blueprint HomotopyHypothesis.Henry

namespace HomotopyHypothesis.FiniteCategory.Lifting

/-- Representable models, restricted to the category of finite globular shapes. -/
def modelShapeDiagram (C : GlobularTheory.{u}) : Shape ⥤ C.Model :=
  C.toTheoryData.arity ⋙ representables C

/-- The Yoneda equivalence for a representable model. -/
def shapeModelHomEquiv (C : GlobularTheory.{u}) (S : Shape) (Z : C.Model) :
    (freeShape C S ⟶ Z) ≃ Z.presheaf.obj (op (⟨S⟩ : C.Obj)) := yonedaEquiv

set_option backward.isDefEq.respectTransparency false in
/-- The representable-model Yoneda equivalence is natural in shape maps. -/
theorem shapeModelHomEquiv_left (C : GlobularTheory.{u}) {S T : Shape}
    (f : S ⟶ T) (Z : C.Model) (a : freeShape C T ⟶ Z) :
    shapeModelHomEquiv C S Z ((modelShapeDiagram C).map f ≫ a) =
      Z.eval (C.base f) (shapeModelHomEquiv C T Z a) :=
  (yonedaEquiv_naturality a (show (⟨S⟩ : C.Obj) ⟶ ⟨T⟩ from C.base f)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The representable models form globular-sum pushouts in the model category. -/
theorem modelShapeDiagram_isPushout (C : GlobularTheory.{u}) (S : Shape)
    (b h : ℕ) (hl : b < S.1) (hr : b < h) :
    IsPushout ((modelShapeDiagram C).map (S.seam hl))
      ((modelShapeDiagram C).map (Shape.face hr false))
      ((modelShapeDiagram C).map (S.inl b h hl hr))
      ((modelShapeDiagram C).map (S.inr b h hl hr)) := by
  let R := modelShapeDiagram C
  have comm := (C.sums S b h hl hr).toCommSq.map (representables C)
  let c := PushoutCocone.mk (R.map (S.inl b h hl hr)) (R.map (S.inr b h hl hr)) comm.w
  have hc : IsColimit c := by
    apply PushoutCocone.isColimitAux' c
    intro s
    let Z := s.pt
    let a := shapeModelHomEquiv C S Z s.inl
    let d := shapeModelHomEquiv C (Shape.globe h) Z s.inr
    have w : Z.eval (C.base (S.seam hl)) a = Z.eval (C.base (Shape.face hr false)) d := by
      have he := congrArg (shapeModelHomEquiv C (Shape.globe b) Z) s.condition
      change shapeModelHomEquiv C (Shape.globe b) Z (R.map (S.seam hl) ≫ s.inl) =
        shapeModelHomEquiv C (Shape.globe b) Z (R.map (Shape.face hr false) ≫ s.inr) at he
      exact (shapeModelHomEquiv_left C (S.seam hl) Z s.inl).symm.trans
        (he.trans (shapeModelHomEquiv_left C (Shape.face hr false) Z s.inr))
    let t := Z.sumTuple S b h hl hr a d w
    let q := (shapeModelHomEquiv C (S.attach b h hl hr) Z).symm t
    have hq : shapeModelHomEquiv C (S.attach b h hl hr) Z q = t :=
      (shapeModelHomEquiv C (S.attach b h hl hr) Z).apply_symm_apply t
    refine ⟨q, ?_, ?_, ?_⟩
    · apply (shapeModelHomEquiv C S Z).injective
      exact (shapeModelHomEquiv_left C (S.inl b h hl hr) Z q).trans
        ((congrArg (fun z => Z.eval (C.base (S.inl b h hl hr)) z) hq).trans
          (Z.sumTuple_left S b h hl hr a d w))
    · apply (shapeModelHomEquiv C (Shape.globe h) Z).injective
      exact (shapeModelHomEquiv_left C (S.inr b h hl hr) Z q).trans
        ((congrArg (fun z => Z.eval (C.base (S.inr b h hl hr)) z) hq).trans
          (Z.sumTuple_right S b h hl hr a d w))
    · intro m hm₀ hm₁
      apply (shapeModelHomEquiv C (S.attach b h hl hr) Z).injective
      simp only [q, Equiv.apply_symm_apply]
      apply Types.ext_of_isPullback (Z.sums S b h hl hr)
      · calc
          Z.eval (C.base (S.inl b h hl hr)) (shapeModelHomEquiv C (S.attach b h hl hr) Z m) =
              shapeModelHomEquiv C S Z (R.map (S.inl b h hl hr) ≫ m) :=
            (shapeModelHomEquiv_left C _ Z m).symm
          _ = a := congrArg (shapeModelHomEquiv C S Z) hm₀
          _ = Z.eval (C.base (S.inl b h hl hr)) t := (Z.sumTuple_left S b h hl hr a d w).symm
      · calc
          Z.eval (C.base (S.inr b h hl hr)) (shapeModelHomEquiv C (S.attach b h hl hr) Z m) =
              shapeModelHomEquiv C (Shape.globe h) Z (R.map (S.inr b h hl hr) ≫ m) :=
            (shapeModelHomEquiv_left C _ Z m).symm
          _ = d := congrArg (shapeModelHomEquiv C (Shape.globe h) Z) hm₁
          _ = Z.eval (C.base (S.inr b h hl hr)) t := (Z.sumTuple_right S b h hl hr a d w).symm
  exact IsPushout.of_isColimit hc

/-- The target endpoint of a model disk is a finite boundary-cell map. -/
theorem modelTarget_finite (C : GlobularTheory.{u}) (n : ℕ) :
    finiteCellMaps C (targetDisk C n) := by
  have h : finiteCellMaps C (pushout.inr (I C n) (I C n) ≫ I C (n+1)) :=
    (finiteCellMaps C).comp_mem _ _
      ((finiteCellMaps C).of_isPushout (IsPushout.of_hasPushout (I C n) (I C n)).flip
        (Cylinder.FiniteCellCategory.finiteCellMaps_I n)) (Cylinder.FiniteCellCategory.finiteCellMaps_I (n+1))
  exact (Cylinder.FiniteCellCategory.boundary_inr_I n) ▸ h

set_option backward.isDefEq.respectTransparency false in
/-- All proper disk face maps are finite boundary-cell maps. -/
theorem modelFace_finite (C : GlobularTheory.{u}) {m n : ℕ} (h : m < n) (side : Bool) :
    finiteCellMaps C ((modelShapeDiagram C).map (Shape.face h side)) := by
  change finiteCellMaps C ((C.globes ⋙ representables C).map (Globe.face h side))
  apply functorFace_mem (C.globes ⋙ representables C) (finiteCellMaps C) inferInstance
  · intro n
    exact Cylinder.FiniteCellCategory.finiteCellMaps_J n
  · intro n
    exact modelTarget_finite C n

set_option backward.isDefEq.respectTransparency false in
/-- A free shape is finitely cellular, and its last disk enters by a finite boundary-cell map. -/
theorem modelTable_finite (C : GlobularTheory.{u}) {n : ℕ} (T : Table n) :
    IsFinitelyCellular C (freeShape C ⟨n, T⟩) ∧
      finiteCellMaps C ((modelShapeDiagram C).map (lastShapeInclusion ⟨n, T⟩)) := by
  induction T with
  | globe n =>
    refine ⟨FiniteCategory.Subcategory.disk_finitelyCellular_proof C n, ?_⟩
    change finiteCellMaps C ((modelShapeDiagram C).map (𝟙 (Shape.globe n)))
    exact ((modelShapeDiagram C).map_id (Shape.globe n)).symm ▸ (finiteCellMaps C).id_mem _
  | @attach n T b h hl hr ih =>
    let S : Shape := ⟨n, T⟩
    have hf : finiteCellMaps C ((modelShapeDiagram C).map (S.seam hl)) := by
      change finiteCellMaps C ((modelShapeDiagram C).map (Shape.face hl true ≫ lastShapeInclusion S))
      rw [Functor.map_comp]
      exact (finiteCellMaps C).comp_mem _ _ (modelFace_finite C hl true) ih.2
    have sq := modelShapeDiagram_isPushout C S b h hl hr
    have hj : finiteCellMaps C ((modelShapeDiagram C).map (S.inr b h hl hr)) :=
      (finiteCellMaps C).of_isPushout sq.flip hf
    exact ⟨Cylinder.FiniteCellCategory.isFinitelyCellular_of_finiteCellMap
      (FiniteCategory.Subcategory.disk_finitelyCellular_proof C h) _ hj, hj⟩

/-- Every representable globular shape is finitely cellular. -/
theorem freeShape_finitelyCellular (C : GlobularTheory.{u}) (S : Shape) :
    IsFinitelyCellular C (freeShape C S) := (modelTable_finite C S.2).1

/-- The last-disk inclusion of a free shape is a finite boundary-cell map. -/
theorem modelShape_last_finite (C : GlobularTheory.{u}) (S : Shape) :
    finiteCellMaps C ((modelShapeDiagram C).map (lastShapeInclusion S)) :=
  (modelTable_finite C S.2).2

/-- Every globular-sum seam between free models is a finite boundary-cell map. -/
theorem modelShape_seam_finite (C : GlobularTheory.{u}) (S : Shape) (b : ℕ) (hb : b < S.1) :
    finiteCellMaps C ((modelShapeDiagram C).map (S.seam hb)) := by
  change finiteCellMaps C ((modelShapeDiagram C).map (Shape.face hb true ≫ lastShapeInclusion S))
  rw [Functor.map_comp]
  exact (finiteCellMaps C).comp_mem _ _ (modelFace_finite C hb true) (modelShape_last_finite C S)

/-- The representable theory diagram valued in finite cellular models. -/
def afinRepresentables {C : GlobularTheory.{u}} (hC : C.IsCoherator) : C.Obj ⥤ Afin C hC :=
  ObjectProperty.lift (IsFinitelyCellular C) (representables C)
    (fun S => freeShape_finitelyCellular C S.shape)

/-- The finite shape diagram valued in finite cellular models. -/
def afinShapeDiagram {C : GlobularTheory.{u}} (hC : C.IsCoherator) : Shape ⥤ Afin C hC :=
  C.toTheoryData.arity ⋙ afinRepresentables hC

/-- Globular-sum pushouts between representables hold already in the finite cellular category. -/
theorem afinShapeDiagram_isPushout {C : GlobularTheory.{u}} (hC : C.IsCoherator) (S : Shape)
    (b h : ℕ) (hl : b < S.1) (hr : b < h) :
    IsPushout ((afinShapeDiagram hC).map (S.seam hl))
      ((afinShapeDiagram hC).map (Shape.face hr false))
      ((afinShapeDiagram hC).map (S.inl b h hl hr))
      ((afinShapeDiagram hC).map (S.inr b h hl hr)) :=
  IsPushout.of_map_of_faithful (Afin.ι hC) (modelShapeDiagram_isPushout C S b h hl hr)

/-- Seams in the finite cellular shape diagram are cofibrations. -/
theorem afinShapeDiagram_seam_cof {C : GlobularTheory.{u}} (hC : C.IsCoherator)
    (S : Shape) (b : ℕ) (hb : b < S.1) :
    cofibrations (Afin C hC) ((afinShapeDiagram hC).map (S.seam hb)) :=
  modelShape_seam_finite C S b hb

#print axioms modelShapeDiagram_isPushout
#print axioms freeShape_finitelyCellular
#print axioms afinShapeDiagram_isPushout

end HomotopyHypothesis.FiniteCategory.Lifting
