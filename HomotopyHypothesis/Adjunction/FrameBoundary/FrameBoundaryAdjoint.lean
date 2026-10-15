import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.FiniteCategory.Realization.FiniteRealizationStatement
import HomotopyHypothesis.FiniteCategory.Lifting.EndomorphismTheory
import HomotopyHypothesis.FiniteCategory.Lifting.FillerLift
import HomotopyHypothesis.FiniteCategory.Lifting.Nerve
import HomotopyHypothesis.FiniteCategory.Lifting.RealizationStatements
noncomputable section

universe u v

open CategoryTheory Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Blueprint HomotopyHypothesis.Henry

namespace HomotopyHypothesis.Adjunction.FrameBoundary

variable {C : GlobularTheory.{u}} {X : Type v} [Category.{u} X]
  (R : HomotopyHypothesis.FiniteCategory.Lifting.ShapeInterpretation X)
  (a : GlobularTheory.Morphism C R.endTheory)

private theorem interpreted_source
    (n : ℕ) :
    (R.interpretation a).functor.map (C.globes.map (Globe.source n)) =
      R.functor.map (Shape.source n) := by
  change a.map (C.base (Shape.source n)) = R.functor.map (Shape.source n)
  exact a.map_base _

private theorem interpreted_target
    (n : ℕ) :
    (R.interpretation a).functor.map (C.globes.map (Globe.target n)) =
      R.functor.map (Shape.target n) := by
  change a.map (C.base (Shape.target n)) = R.functor.map (Shape.target n)
  exact a.map_base _

set_option backward.isDefEq.respectTransparency false

variable [CategoryWithCofibrations X]
  (F : HomotopyHypothesis.FiniteCategory.Lifting.FramedShapeInterpretation R)

/-- Cells of the interpreted nerve agree with maps out of the framed disks. -/
def nerveFrameGlobularMap (Y : X) :
    ((R.interpretation a).nerve.obj Y).underlying.Hom (F.frame.homGlob Y) where
  app n f := (F.diskIso n).hom ≫ f
  source_app n f := by
    change (F.diskIso n).hom ≫
        ((R.interpretation a).functor.map (C.globes.map (Globe.source n)) ≫ f) =
      F.frame.diagram.source n ≫ ((F.diskIso (n+1)).hom ≫ f)
    rw [← Category.assoc, interpreted_source, ← Category.assoc, F.source n]
  target_app n f := by
    change (F.diskIso n).hom ≫
        ((R.interpretation a).functor.map (C.globes.map (Globe.target n)) ≫ f) =
      F.frame.diagram.target n ≫ ((F.diskIso (n+1)).hom ≫ f)
    rw [← Category.assoc, interpreted_target, ← Category.assoc, F.target n]

/-- The comparison on cells induces an equivalence on globular boundaries. -/
noncomputable def nerveFrameBoundaryEquiv (Y : X) (n : ℕ) :
    ((R.interpretation a).nerve.obj Y).underlying.Boundary n ≃
      (F.frame.homGlob Y).Boundary n :=
  Equiv.ofBijective ((nerveFrameGlobularMap R a F Y).boundaryMap n)
    (GlobularSet.Hom.boundaryMap_bijective (nerveFrameGlobularMap R a F Y)
      (fun j => by
        constructor
        · intro f g h
          exact (cancel_epi (F.diskIso j).hom).1 h
        · intro f
          refine ⟨(F.diskIso j).inv ≫ f, ?_⟩
          change (F.diskIso j).hom ≫ ((F.diskIso j).inv ≫ f) = f
          simp) n)

theorem nerveFrameBoundary_naturality {Y Y' : X} (g : Y ⟶ Y') (n : ℕ)
    (b : ((R.interpretation a).nerve.obj Y).underlying.Boundary n) :
    nerveFrameBoundaryEquiv R a F Y' n
        ((underlyingMap ((R.interpretation a).nerve.map g)).boundaryMap n b) =
      (F.frame.post g).boundaryMap n (nerveFrameBoundaryEquiv R a F Y n b) := by
  change (nerveFrameGlobularMap R a F Y').boundaryMap n
      ((underlyingMap ((R.interpretation a).nerve.map g)).boundaryMap n b) =
    (F.frame.post g).boundaryMap n ((nerveFrameGlobularMap R a F Y).boundaryMap n b)
  have h : (nerveFrameGlobularMap R a F Y).comp (F.frame.post g) =
      (underlyingMap ((R.interpretation a).nerve.map g)).comp
        (nerveFrameGlobularMap R a F Y') := by
    ext j x
    simp [GlobularSet.Hom.comp, GlobularFrame.post, nerveFrameGlobularMap,
      HomotopyHypothesis.FiniteCategory.Lifting.TheoryInterpretation.nerve,
      OAI.Grothendieck.GlobularTheory.Model.underlyingMap,
      GlobularPresheaf.underlyingMap, Functor.whiskerLeft_app, Category.assoc]
    change (F.diskIso j).hom ≫ x ≫ g =
      (F.diskIso j).hom ≫
        (𝟙 ((R.interpretation a).functor.obj (C.globes.obj (Globe.mk j)) ⟶ Y)) x ≫ g
    simp
  have hb := congrArg (fun e : GlobularSet.Hom _ _ => e.boundaryMap n b) h
  simpa only [GlobularSet.Hom.boundaryMap_comp] using hb.symm

/-- The interpreted nerve represents maps from a model boundary by the framed boundary. -/
def framedBoundaryCorepresentable (n : ℕ) :
    ((R.interpretation a).nerve ⋙ coyoneda.obj (op (boundaryDisk C n))).CorepresentableBy
      (F.frame.bd n) where
  homEquiv {Y} :=
    (F.frame.boundaryEquiv n).equiv Y |>.trans
      ((nerveFrameBoundaryEquiv R a F Y n).symm.trans
        ((boundaryRepresentation C n).equiv ((R.interpretation a).nerve.obj Y)).symm)
  homEquiv_comp {Y Y'} g f := by
    change
      ((boundaryRepresentation C n).equiv ((R.interpretation a).nerve.obj Y')).symm
          ((nerveFrameBoundaryEquiv R a F Y' n).symm
            ((F.frame.boundaryEquiv n).equiv Y' (f ≫ g))) =
        (((boundaryRepresentation C n).equiv ((R.interpretation a).nerve.obj Y)).symm
          ((nerveFrameBoundaryEquiv R a F Y n).symm
            ((F.frame.boundaryEquiv n).equiv Y f))) ≫ (R.interpretation a).nerve.map g
    apply ((boundaryRepresentation C n).equiv
      ((R.interpretation a).nerve.obj Y')).injective
    rw [BoundaryRepresentation.naturality]
    apply (nerveFrameBoundaryEquiv R a F Y' n).injective
    simp only [Equiv.apply_symm_apply]
    rw [nerveFrameBoundary_naturality]
    simp only [Equiv.apply_symm_apply]
    exact (F.frame.boundaryEquiv n).naturality f g

/-- An interpreted disk is represented by the corresponding frame disk. -/
def framedDiskCorepresentable (n : ℕ) :
    ((R.interpretation a).nerve ⋙ coyoneda.obj (op (disk C n))).CorepresentableBy
      (F.frame.obj n) :=
  Functor.CorepresentableBy.ofIsoObj
    ((R.interpretation a).freeShapeCorepresentable (Shape.globe n)) (F.diskIso n)

theorem framedDiskCorepresentable_cell (n : ℕ) (Y : X)
    (f : F.frame.obj n ⟶ Y) :
    cellEquiv ((R.interpretation a).nerve.obj Y) n
        ((framedDiskCorepresentable R a F n).homEquiv f) =
      (F.diskIso n).inv ≫ f := by
  change yonedaEquiv (F := ((R.interpretation a).nerve.obj Y).presheaf)
      (X := (⟨Shape.globe n⟩ : C.Obj))
      ((yonedaEquiv (F := ((R.interpretation a).nerve.obj Y).presheaf)
          (X := (⟨Shape.globe n⟩ : C.Obj))).symm ((F.diskIso n).inv ≫ f)) = _
  exact Equiv.apply_symm_apply _ _

theorem framedBoundary_inclusion_compatible (n : ℕ) (Y : X)
    (f : F.frame.obj n ⟶ Y) :
    (framedBoundaryCorepresentable R a F n).homEquiv (F.frame.inc n ≫ f) =
      I C n ≫ (framedDiskCorepresentable R a F n).homEquiv f := by
  change ((boundaryRepresentation C n).equiv
      ((R.interpretation a).nerve.obj Y)).symm
      ((nerveFrameBoundaryEquiv R a F Y n).symm
        ((F.frame.boundaryEquiv n).equiv Y (F.frame.inc n ≫ f))) =
    I C n ≫ (framedDiskCorepresentable R a F n).homEquiv f
  apply ((boundaryRepresentation C n).equiv ((R.interpretation a).nerve.obj Y)).injective
  rw [BoundaryRepresentation.inclusion_boundary]
  apply (nerveFrameBoundaryEquiv R a F Y n).injective
  simp only [Equiv.apply_symm_apply]
  rw [(F.frame.boundaryEquiv n).inc_boundary]
  rw [framedDiskCorepresentable_cell]
  change (F.frame.homGlob Y).boundary n f =
    (nerveFrameGlobularMap R a F Y).boundaryMap n
      (((R.interpretation a).nerve.obj Y).underlying.boundary n
        ((F.diskIso n).inv ≫ f))
  rw [GlobularSet.Hom.boundary_app]
  simp [nerveFrameGlobularMap]

noncomputable def framedBoundaryPartialAdjointIso
    (n : ℕ)
    (hbd : (R.interpretation a).nerve.leftAdjointObjIsDefined (boundaryDisk C n)) :
    F.frame.bd n ≅
      ((R.interpretation a).nerve.partialLeftAdjoint).obj
        (⟨boundaryDisk C n, hbd⟩ : (R.interpretation a).nerve.PartialLeftAdjointSource) := by
  letI : ((R.interpretation a).nerve ⋙ coyoneda.obj (op (boundaryDisk C n))).IsCorepresentable := hbd
  exact (framedBoundaryCorepresentable R a F n).isoCoreprX

noncomputable def framedDiskPartialAdjointIso (n : ℕ) :
    F.frame.obj n ≅
      ((R.interpretation a).nerve.partialLeftAdjoint).obj
        (⟨disk C n,
          (R.interpretation a).freeShape_leftAdjointObjIsDefined (Shape.globe n)⟩ :
          (R.interpretation a).nerve.PartialLeftAdjointSource) := by
  letI : ((R.interpretation a).nerve ⋙ coyoneda.obj (op (disk C n))).IsCorepresentable :=
    (R.interpretation a).freeShape_leftAdjointObjIsDefined (Shape.globe n)
  exact (framedDiskCorepresentable R a F n).isoCoreprX

theorem framedBoundaryPartialAdjointIso_equiv
    (n : ℕ)
    (hbd : (R.interpretation a).nerve.leftAdjointObjIsDefined (boundaryDisk C n)) :
    (framedBoundaryCorepresentable R a F n).homEquiv
        (framedBoundaryPartialAdjointIso R a F n hbd).hom =
      (R.interpretation a).nerve.partialLeftAdjointHomEquiv
        (X := (⟨boundaryDisk C n, hbd⟩ :
          (R.interpretation a).nerve.PartialLeftAdjointSource)) (𝟙 _) := by
  simp [framedBoundaryPartialAdjointIso, Functor.CorepresentableBy.isoCoreprX,
    Functor.CorepresentableBy.uniqueUpToIso_hom, Coyoneda.fullyFaithful_preimage,
    Functor.partialLeftAdjointHomEquiv]
  exact (framedBoundaryCorepresentable R a F n).homEquiv.apply_symm_apply _

theorem framedDiskPartialAdjointIso_equiv (n : ℕ) :
    (framedDiskCorepresentable R a F n).homEquiv
        (framedDiskPartialAdjointIso R a F n).hom =
      (R.interpretation a).nerve.partialLeftAdjointHomEquiv
        (X := (⟨disk C n,
          (R.interpretation a).freeShape_leftAdjointObjIsDefined (Shape.globe n)⟩ :
          (R.interpretation a).nerve.PartialLeftAdjointSource)) (𝟙 _) := by
  simp [framedDiskPartialAdjointIso, Functor.CorepresentableBy.isoCoreprX,
    Functor.CorepresentableBy.uniqueUpToIso_hom, Coyoneda.fullyFaithful_preimage,
    Functor.partialLeftAdjointHomEquiv]
  exact (framedDiskCorepresentable R a F n).homEquiv.apply_symm_apply _

theorem framedBoundaryPartialAdjoint_map_conjugate
    (n : ℕ)
    (hbd : (R.interpretation a).nerve.leftAdjointObjIsDefined (boundaryDisk C n)) :
    (framedBoundaryPartialAdjointIso R a F n hbd).hom ≫
        (R.interpretation a).nerve.partialLeftAdjoint.map
          (ObjectProperty.homMk (I C n) :
            (⟨boundaryDisk C n, hbd⟩ :
              (R.interpretation a).nerve.PartialLeftAdjointSource) ⟶
            ⟨disk C n,
              (R.interpretation a).freeShape_leftAdjointObjIsDefined (Shape.globe n)⟩) =
      F.frame.inc n ≫ (framedDiskPartialAdjointIso R a F n).hom := by
  let N := (R.interpretation a).nerve
  let A : N.PartialLeftAdjointSource := ⟨boundaryDisk C n, hbd⟩
  let B : N.PartialLeftAdjointSource :=
    ⟨disk C n, (R.interpretation a).freeShape_leftAdjointObjIsDefined (Shape.globe n)⟩
  let i : A ⟶ B := ObjectProperty.homMk (I C n)
  apply (framedBoundaryCorepresentable R a F n).homEquiv.injective
  calc
    (framedBoundaryCorepresentable R a F n).homEquiv
        ((framedBoundaryPartialAdjointIso R a F n hbd).hom ≫ N.partialLeftAdjoint.map i) =
      N.partialLeftAdjointHomEquiv (X := A) (𝟙 _) ≫
        N.map (N.partialLeftAdjoint.map i) := by
        rw [(framedBoundaryCorepresentable R a F n).homEquiv_comp,
          framedBoundaryPartialAdjointIso_equiv]
        change N.partialLeftAdjointHomEquiv (X := A) (𝟙 _) ≫
          N.map (N.partialLeftAdjoint.map i) = _
        rfl
    _ = N.partialLeftAdjointHomEquiv (X := A)
          (N.partialLeftAdjoint.map i) := by
          rw [← N.partialLeftAdjointHomEquiv_comp]
          simp
    _ = i.hom ≫ N.partialLeftAdjointHomEquiv (X := B) (𝟙 _) := by
          change N.partialLeftAdjointHomEquiv (N.partialLeftAdjointMap i) = _
          rw [N.partialLeftAdjointHomEquiv_map]
    _ = (I C n) ≫ (framedDiskCorepresentable R a F n).homEquiv
          ((framedDiskPartialAdjointIso R a F n).hom) := by
          rw [framedDiskPartialAdjointIso_equiv]
          rfl
    _ = (framedBoundaryCorepresentable R a F n).homEquiv
          (F.frame.inc n ≫ (framedDiskPartialAdjointIso R a F n).hom) := by
          exact (framedBoundary_inclusion_compatible R a F n _ _).symm

theorem framedBoundary_map_isCofibration [IsCofibrationCategory X]
    (F : HomotopyHypothesis.FiniteCategory.Lifting.FramedShapeInterpretation R)
    (n : ℕ)
    (hbd : (R.interpretation a).nerve.leftAdjointObjIsDefined (boundaryDisk C n)) :
    cofibrations X ((R.interpretation a).nerve.partialLeftAdjoint.map
      (ObjectProperty.homMk (I C n) :
        (⟨boundaryDisk C n, hbd⟩ :
          (R.interpretation a).nerve.PartialLeftAdjointSource) ⟶
        ⟨disk C n,
          (R.interpretation a).freeShape_leftAdjointObjIsDefined (Shape.globe n)⟩)) := by
  let N := (R.interpretation a).nerve
  let A : N.PartialLeftAdjointSource := ⟨boundaryDisk C n, hbd⟩
  let B : N.PartialLeftAdjointSource :=
    ⟨disk C n, (R.interpretation a).freeShape_leftAdjointObjIsDefined (Shape.globe n)⟩
  let i : A ⟶ B := ObjectProperty.homMk (I C n)
  let eA := framedBoundaryPartialAdjointIso R a F n hbd
  let eB := framedDiskPartialAdjointIso R a F n
  have hconj : eA.hom ≫ N.partialLeftAdjoint.map i = F.frame.inc n ≫ eB.hom :=
    framedBoundaryPartialAdjoint_map_conjugate R a F n hbd
  have hmap : (eA.inv ≫ F.frame.inc n) ≫ eB.hom = N.partialLeftAdjoint.map i := by
    calc
      (eA.inv ≫ F.frame.inc n) ≫ eB.hom =
          eA.inv ≫ (F.frame.inc n ≫ eB.hom) := Category.assoc _ _ _
      _ = eA.inv ≫ (eA.hom ≫ N.partialLeftAdjoint.map i) := by rw [← hconj]
      _ = N.partialLeftAdjoint.map i := by simp
  have hleft : cofibrations X (eA.inv ≫ F.frame.inc n) :=
    (IsCofibrationCategory.isMultiplicative (C := X)).comp_mem _ _
      (IsCofibrationCategory.isomorphisms_le _ inferInstance) (F.inc_cof n)
  have hright : cofibrations X ((eA.inv ≫ F.frame.inc n) ≫ eB.hom) :=
    (IsCofibrationCategory.isMultiplicative (C := X)).comp_mem _ _ hleft
      (IsCofibrationCategory.isomorphisms_le _ inferInstance)
  rw [hmap] at hright
  exact hright

theorem frameBoundaryAdjointStatement_proof
    {C : GlobularTheory.{u}} {X : Type v} [Category.{u} X]
    [CategoryWithCofibrations X] [IsCofibrationCategory X]
    (R : HomotopyHypothesis.FiniteCategory.Lifting.ShapeInterpretation X)
    (F : HomotopyHypothesis.FiniteCategory.Lifting.FramedShapeInterpretation R)
    (a : GlobularTheory.Morphism C R.endTheory) :
    HomotopyHypothesis.FiniteCategory.Lifting.FrameBoundaryAdjointStatement R F a := by
  let T := R.interpretation a
  have hb : ∀ n, T.nerve.leftAdjointObjIsDefined (boundaryDisk C n) := by
    intro n
    induction n with
    | zero =>
        simpa [boundaryDisk, boundaryRepresentation, BoundaryRepresentation.zero] using
          T.initial_leftAdjointObjIsDefined initialIsInitial F.frame.initial
    | succ n ih =>
        let P := boundaryDisk C (n+1)
        have hPush : IsPushout (I C n) (I C n)
            (pushout.inl (I C n) (I C n)) (pushout.inr (I C n) (I C n)) :=
          IsPushout.of_hasPushout _ _
        have hcof := framedBoundary_map_isCofibration R a F n ih
        exact HomotopyHypothesis.FiniteCategory.Realization.leftAdjointObjIsDefined_of_pushout
          T (I C n) (I C n) (pushout.inl (I C n) (I C n))
          (pushout.inr (I C n) (I C n)) hPush ih
          (T.freeShape_leftAdjointObjIsDefined (Shape.globe n))
          (T.freeShape_leftAdjointObjIsDefined (Shape.globe n)) hcof
  refine ⟨hb, ?_⟩
  intro n
  exact framedBoundary_map_isCofibration R a F n (hb n)

example {C : GlobularTheory.{u}} {X : Type v} [Category.{u} X]
    [CategoryWithCofibrations X] [IsCofibrationCategory X]
    (R : HomotopyHypothesis.FiniteCategory.Lifting.ShapeInterpretation X)
    (F : HomotopyHypothesis.FiniteCategory.Lifting.FramedShapeInterpretation R)
    (a : GlobularTheory.Morphism C R.endTheory) :
    HomotopyHypothesis.FiniteCategory.Lifting.FrameBoundaryAdjointStatement R F a :=
  frameBoundaryAdjointStatement_proof R F a

#print axioms frameBoundaryAdjointStatement_proof

end HomotopyHypothesis.Adjunction.FrameBoundary
