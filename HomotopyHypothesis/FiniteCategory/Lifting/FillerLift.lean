import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.FiniteCategory.Lifting.EndomorphismTheory
import HomotopyHypothesis.FiniteCategory.Lifting.Extensions
import HomotopyHypothesis.FiniteCategory.Lifting.FrameLift
/-!
# Admissible pairs and boundary extensions

An admissible pair in an endomorphism theory determines a map from a globular boundary.
Prescribed boundary extension lifting therefore gives filler lifting of endomorphism theories.
-/

noncomputable section

universe u v u₁

open CategoryTheory Limits HomotopicalAlgebra
open OAI.Grothendieck
open HomotopyHypothesis.Henry

namespace HomotopyHypothesis.FiniteCategory.Lifting

variable {X : Type u} [Category.{v} X] [CategoryWithCofibrations X]

/-- A shape interpretation with a cofibrant boundary frame for its globes. -/
structure FramedShapeInterpretation (R : ShapeInterpretation X) where
  frame : GlobularFrame X
  diskIso : ∀ n, frame.obj n ≅ R.functor.obj (Shape.globe n)
  source : ∀ n, frame.diagram.source n ≫ (diskIso (n+1)).hom =
    (diskIso n).hom ≫ R.functor.map (Shape.source n)
  target : ∀ n, frame.diagram.target n ≫ (diskIso (n+1)).hom =
    (diskIso n).hom ≫ R.functor.map (Shape.target n)
  inc_cof : ∀ n, cofibrations X (frame.inc n)

namespace FramedShapeInterpretation

set_option backward.isDefEq.respectTransparency false in
/-- Parallel arrows in the endomorphism theory give parallel cells in the frame's hom globular
set after identifying the disks. -/
theorem parallel {R : ShapeInterpretation X} (F : FramedShapeInterpretation R)
    {n : ℕ} {S : Shape} (s t : R.endTheory.Hom (Shape.globe n) S)
    (h : R.endTheory.Parallel n s t) :
    (F.frame.homGlob (R.functor.obj S)).Parallel n
      ((F.diskIso n).hom ≫ s) ((F.diskIso n).hom ≫ t) := by
  dsimp only [ShapeInterpretation.endTheory, ShapeInterpretation.endData] at s t
  cases n with
  | zero => trivial
  | succ n =>
    change (R.functor.map (Shape.source n) ≫ s = R.functor.map (Shape.source n) ≫ t) ∧
      (R.functor.map (Shape.target n) ≫ s = R.functor.map (Shape.target n) ≫ t) at h
    change (F.frame.diagram.source n ≫ (F.diskIso (n+1)).hom ≫ s =
        F.frame.diagram.source n ≫ (F.diskIso (n+1)).hom ≫ t) ∧
      (F.frame.diagram.target n ≫ (F.diskIso (n+1)).hom ≫ s =
        F.frame.diagram.target n ≫ (F.diskIso (n+1)).hom ≫ t)
    constructor
    · calc
        F.frame.diagram.source n ≫ (F.diskIso (n+1)).hom ≫ s =
            (F.frame.diagram.source n ≫ (F.diskIso (n+1)).hom) ≫ s :=
          (Category.assoc _ _ _).symm
        _ = ((F.diskIso n).hom ≫ R.functor.map (Shape.source n)) ≫ s :=
          congrArg (fun f => f ≫ s) (F.source n)
        _ = (F.diskIso n).hom ≫ (R.functor.map (Shape.source n) ≫ s) := Category.assoc _ _ _
        _ = (F.diskIso n).hom ≫ (R.functor.map (Shape.source n) ≫ t) :=
          congrArg (fun f => (F.diskIso n).hom ≫ f) h.1
        _ = ((F.diskIso n).hom ≫ R.functor.map (Shape.source n)) ≫ t :=
          (Category.assoc _ _ _).symm
        _ = (F.frame.diagram.source n ≫ (F.diskIso (n+1)).hom) ≫ t :=
          congrArg (fun f => f ≫ t) (F.source n).symm
        _ = F.frame.diagram.source n ≫ (F.diskIso (n+1)).hom ≫ t := Category.assoc _ _ _
    · calc
        F.frame.diagram.target n ≫ (F.diskIso (n+1)).hom ≫ s =
            (F.frame.diagram.target n ≫ (F.diskIso (n+1)).hom) ≫ s :=
          (Category.assoc _ _ _).symm
        _ = ((F.diskIso n).hom ≫ R.functor.map (Shape.target n)) ≫ s :=
          congrArg (fun f => f ≫ s) (F.target n)
        _ = (F.diskIso n).hom ≫ (R.functor.map (Shape.target n) ≫ s) := Category.assoc _ _ _
        _ = (F.diskIso n).hom ≫ (R.functor.map (Shape.target n) ≫ t) :=
          congrArg (fun f => (F.diskIso n).hom ≫ f) h.2
        _ = ((F.diskIso n).hom ≫ R.functor.map (Shape.target n)) ≫ t :=
          (Category.assoc _ _ _).symm
        _ = (F.frame.diagram.target n ≫ (F.diskIso (n+1)).hom) ≫ t :=
          congrArg (fun f => f ≫ t) (F.target n).symm
        _ = F.frame.diagram.target n ≫ (F.diskIso (n+1)).hom ≫ t := Category.assoc _ _ _

/-- An admissible pair determines its boundary map through the boundary pushout. -/
theorem boundary_exists {R : ShapeInterpretation X} (F : FramedShapeInterpretation R)
    (a : R.endTheory.AdmissiblePair) :
    ∃ b : F.frame.bd (a.n+1) ⟶ R.functor.obj a.arity,
      F.frame.left a.n ≫ b = (F.diskIso a.n).hom ≫ a.source ∧
        F.frame.right a.n ≫ b = (F.diskIso a.n).hom ≫ a.target := by
  let s : F.frame.obj a.n ⟶ R.functor.obj a.arity := (F.diskIso a.n).hom ≫ a.source
  let t : F.frame.obj a.n ⟶ R.functor.obj a.arity := (F.diskIso a.n).hom ≫ a.target
  have heq : (F.frame.homGlob (R.functor.obj a.arity)).boundary a.n s =
      (F.frame.homGlob (R.functor.obj a.arity)).boundary a.n t :=
    (GlobularSet.parallel_iff_boundary_eq _ _ _ _).1 (F.parallel _ _ a.parallel)
  let E := F.frame.boundaryEquiv a.n
  have hi : F.frame.inc a.n ≫ s = F.frame.inc a.n ≫ t :=
    (E.equiv _).injective ((E.inc_boundary s).trans (heq.trans (E.inc_boundary t).symm))
  exact ⟨(F.frame.square a.n).desc s t hi,
    (F.frame.square a.n).inl_desc _ _ _, (F.frame.square a.n).inr_desc _ _ _⟩

end FramedShapeInterpretation

variable {Y : Type u₁} [Category.{v} Y]

/-- Exact extension lifting with codomain one of the interpreted shapes. -/
def ShapeExtensionLifting (R : ShapeInterpretation X) (p : X ⥤ Y) : Prop :=
  ∀ ⦃A B : X⦄ (i : A ⟶ B), cofibrations X i → ∀ (S : Shape)
    (a : A ⟶ R.functor.obj S) (w : p.obj B ⟶ p.obj (R.functor.obj S)),
    p.map i ≫ w = p.map a →
      ∃ b : B ⟶ R.functor.obj S, i ≫ b = a ∧ p.map b = w

set_option backward.isDefEq.respectTransparency false in
/-- Conjugating a filler back along the diagram isomorphism gives the required boundary images. -/
theorem filler_boundary_images (R : ShapeInterpretation X) (S : ShapeInterpretation Y)
    (p : X ⥤ Y) (α : R.functor ⋙ p ≅ S.functor) (a : R.endTheory.AdmissiblePair)
    (z : S.endTheory.Hom (Shape.globe (a.n+1)) a.arity)
    (hz : GlobularTheory.Fills (R.map S p α) a z) :
    let w := (α.app (Shape.globe (a.n+1))).hom ≫ z ≫ (α.app a.arity).inv
    (p.map (R.functor.map (Shape.source a.n)) ≫ w = p.map a.source) ∧
      (p.map (R.functor.map (Shape.target a.n)) ≫ w = p.map a.target) := by
  dsimp only [ShapeInterpretation.endTheory, ShapeInterpretation.endData] at z
  change
    (p.map (R.functor.map (Shape.source a.n)) ≫
      ((α.app (Shape.globe (a.n+1))).hom ≫ z ≫ (α.app a.arity).inv) = p.map a.source) ∧
    (p.map (R.functor.map (Shape.target a.n)) ≫
      ((α.app (Shape.globe (a.n+1))).hom ≫ z ≫ (α.app a.arity).inv) = p.map a.target)
  have hs := hz.1
  have ht := hz.2
  change S.functor.map (Shape.source a.n) ≫ z =
    (α.app (Shape.globe a.n)).inv ≫ p.map a.source ≫ (α.app a.arity).hom at hs
  change S.functor.map (Shape.target a.n) ≫ z =
    (α.app (Shape.globe a.n)).inv ≫ p.map a.target ≫ (α.app a.arity).hom at ht
  constructor
  · have hn := α.hom.naturality (Shape.source a.n)
    change p.map (R.functor.map (Shape.source a.n)) ≫ (α.app (Shape.globe (a.n+1))).hom =
      (α.app (Shape.globe a.n)).hom ≫ S.functor.map (Shape.source a.n) at hn
    calc
      _ = (α.app (Shape.globe a.n)).hom ≫
          (S.functor.map (Shape.source a.n) ≫ z) ≫ (α.app a.arity).inv := by
        simp only [← Category.assoc, hn]
      _ = p.map a.source := by rw [hs]; simp [Category.assoc]
  · have hn := α.hom.naturality (Shape.target a.n)
    change p.map (R.functor.map (Shape.target a.n)) ≫ (α.app (Shape.globe (a.n+1))).hom =
      (α.app (Shape.globe a.n)).hom ≫ S.functor.map (Shape.target a.n) at hn
    calc
      _ = (α.app (Shape.globe a.n)).hom ≫
          (S.functor.map (Shape.target a.n) ≫ z) ≫ (α.app a.arity).inv := by
        simp only [← Category.assoc, hn]
      _ = p.map a.target := by rw [ht]; simp [Category.assoc]

variable [CategoryWithWeakEquivalences X] [IsCylinderCategory X]
  [CategoryWithCofibrations Y] [CategoryWithWeakEquivalences Y] [IsCylinderCategory Y]

namespace FramedShapeInterpretation

set_option backward.isDefEq.respectTransparency false in
/-- Boundary extension lifting implies filler lifting of endomorphism theories. -/
theorem liftsFillers {R : ShapeInterpretation X} (F : FramedShapeInterpretation R)
    (S : ShapeInterpretation Y) (p : X ⥤ Y) (hm : IsCylinderMorphism p)
    (α : R.functor ⋙ p ≅ S.functor) (hExt : ShapeExtensionLifting R p) :
    GlobularTheory.LiftsFillers (R.map S p α) := by
  intro a z hz
  dsimp only [ShapeInterpretation.endTheory, ShapeInterpretation.endData] at z
  obtain ⟨b, hb₀, hb₁⟩ := F.boundary_exists a
  let i : F.frame.bd (a.n+1) ⟶ R.functor.obj (Shape.globe (a.n+1)) :=
    F.frame.inc (a.n+1) ≫ (F.diskIso (a.n+1)).hom
  have hi : cofibrations X i :=
    (IsCofibrationCategory.isMultiplicative (C := X)).comp_mem _ _ (F.inc_cof _)
      (IsCofibrationCategory.isomorphisms_le _ inferInstance)
  let w : p.obj (R.functor.obj (Shape.globe (a.n+1))) ⟶ p.obj (R.functor.obj a.arity) :=
    (α.app (Shape.globe (a.n+1))).hom ≫ z ≫ (α.app a.arity).inv
  have himages := filler_boundary_images R S p α a z hz
  have psq := hm.map_isPushout _ _ _ _ (F.frame.square a.n) (F.inc_cof _)
  have hsq : p.map i ≫ w = p.map b := by
    apply psq.hom_ext
    · calc
        p.map (F.frame.left a.n) ≫ (p.map i ≫ w) =
            p.map (F.frame.diagram.source a.n) ≫ p.map (F.diskIso (a.n+1)).hom ≫ w := by
          simp [i, GlobularFrame.diagram, Category.assoc]
        _ = p.map (F.diskIso a.n).hom ≫ (p.map (R.functor.map (Shape.source a.n)) ≫ w) := by
          rw [← Category.assoc, ← p.map_comp, F.source, p.map_comp, Category.assoc]
        _ = p.map ((F.diskIso a.n).hom ≫ a.source) := by rw [himages.1, p.map_comp]
        _ = p.map (F.frame.left a.n) ≫ p.map b := by rw [← hb₀, p.map_comp]
    · calc
        p.map (F.frame.right a.n) ≫ (p.map i ≫ w) =
            p.map (F.frame.diagram.target a.n) ≫ p.map (F.diskIso (a.n+1)).hom ≫ w := by
          simp [i, GlobularFrame.diagram, Category.assoc]
        _ = p.map (F.diskIso a.n).hom ≫ (p.map (R.functor.map (Shape.target a.n)) ≫ w) := by
          rw [← Category.assoc, ← p.map_comp, F.target, p.map_comp, Category.assoc]
        _ = p.map ((F.diskIso a.n).hom ≫ a.target) := by rw [himages.2, p.map_comp]
        _ = p.map (F.frame.right a.n) ≫ p.map b := by rw [← hb₁, p.map_comp]
  obtain ⟨z', hz', hpz'⟩ := hExt i hi a.arity b w hsq
  refine ⟨z', ⟨?_, ?_⟩, ?_⟩
  · change R.functor.map (Shape.source a.n) ≫ z' = a.source
    apply (cancel_epi (F.diskIso a.n).hom).1
    calc
      (F.diskIso a.n).hom ≫ (R.functor.map (Shape.source a.n) ≫ z') =
          F.frame.left a.n ≫ (i ≫ z') := by
        rw [← Category.assoc, ← F.source]
        simp [i, GlobularFrame.diagram, Category.assoc]
      _ = F.frame.left a.n ≫ b := by rw [hz']
      _ = (F.diskIso a.n).hom ≫ a.source := hb₀
  · change R.functor.map (Shape.target a.n) ≫ z' = a.target
    apply (cancel_epi (F.diskIso a.n).hom).1
    calc
      (F.diskIso a.n).hom ≫ (R.functor.map (Shape.target a.n) ≫ z') =
          F.frame.right a.n ≫ (i ≫ z') := by
        rw [← Category.assoc, ← F.target]
        simp [i, GlobularFrame.diagram, Category.assoc]
      _ = F.frame.right a.n ≫ b := by rw [hz']
      _ = (F.diskIso a.n).hom ≫ a.target := hb₁
  · change (α.app (Shape.globe (a.n+1))).inv ≫ p.map z' ≫ (α.app a.arity).hom = z
    rw [hpz']
    simp [w, Category.assoc]

/-- Acyclic pre-fibrations lift fillers for every framed shape interpretation. -/
theorem liftsFillers_acyclic {R : ShapeInterpretation X} (F : FramedShapeInterpretation R)
    (S : ShapeInterpretation Y) {p : X ⥤ Y} (hp : IsPreFibration p)
    (hm : IsCylinderMorphism p) (ha : IsAcyclic p) (α : R.functor ⋙ p ≅ S.functor) :
    GlobularTheory.LiftsFillers (R.map S p α) :=
  F.liftsFillers S p hm α
    (fun {A B} i hi _ a w hs => lift_acyclic_extension hp hm ha i hi a w hs)

/-- Pre-fibrations lift fillers when the interpreted arities and their images are h-terminal. -/
theorem liftsFillers_hterminal {R : ShapeInterpretation X} (F : FramedShapeInterpretation R)
    (S : ShapeInterpretation Y) {p : X ⥤ Y} (hp : IsPreFibration p)
    (hm : IsCylinderMorphism p) (α : R.functor ⋙ p ≅ S.functor)
    (hR : ∀ T : Shape, IsHTerminal (R.functor.obj T) ∧ IsHTerminal (p.obj (R.functor.obj T))) :
    GlobularTheory.LiftsFillers (R.map S p α) :=
  F.liftsFillers S p hm α (fun {A B} i hi T a w hs =>
    lift_hterminal_extension hp hm (hR T).1 (hR T).2 i hi a w hs)

end FramedShapeInterpretation

#print axioms FramedShapeInterpretation.boundary_exists
#print axioms FramedShapeInterpretation.liftsFillers_acyclic
#print axioms FramedShapeInterpretation.liftsFillers_hterminal

end HomotopyHypothesis.FiniteCategory.Lifting
