import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.FiniteCategory.Lifting.EndomorphismTheory
import HomotopyHypothesis.FiniteCategory.Lifting.FillerLift
import HomotopyHypothesis.FiniteCategory.Lifting.FrameCofibrations
import HomotopyHypothesis.FiniteCategory.Lifting.FrameShapes
import HomotopyHypothesis.FiniteCategory.Lifting.PartialPushout
/-!
# Realizing finite globular sums by cofibration pushouts

The partial left adjoint of a globular frame nerve is defined on each finite globular sum.
The inclusion of its last disk is a trivial cofibration, as follows by induction over its table.
-/

noncomputable section

universe u v

open CategoryTheory Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck HomotopyHypothesis.Henry

namespace HomotopyHypothesis.FiniteCategory.Lifting

variable {X : Type u} [Category.{v} X] [CategoryWithCofibrations X]
  [CategoryWithWeakEquivalences X] [IsCylinderCategory X]

set_option backward.isDefEq.respectTransparency false in
/-- A finite table is corepresentable, and its last-disk map is a trivial cofibration. -/
theorem frameTable_realizable (B : GlobularFrame X)
    (hB : ∀ n,
      (cofibrations X (B.diagram.source n) ∧ weakEquivalences X (B.diagram.source n)) ∧
        (cofibrations X (B.diagram.target n) ∧ weakEquivalences X (B.diagram.target n)))
    {n : ℕ} (T : Table n) :
    ∃ hT : (frameNerve B).leftAdjointObjIsDefined (GlobularPresheaf.liftSmall.{v}.obj T.realize),
      let f := (frameNerve B).partialLeftAdjoint.map
        (ObjectProperty.homMk (GlobularPresheaf.liftSmall.map T.lastInclusion) :
          (frameSmallGlobes B).obj (Globe.mk n) ⟶
            ⟨GlobularPresheaf.liftSmall.obj T.realize, hT⟩)
      cofibrations X f ∧ weakEquivalences X f := by
  let N := frameNerve B
  let L := GlobularPresheaf.liftSmall.{v}
  induction T with
  | globe n =>
    let hT := frameSmallGlobe_leftAdjointObjIsDefined B n
    let f : (frameSmallGlobes B).obj (Globe.mk n) ⟶
        (⟨L.obj (Table.globe n).realize, hT⟩ : N.PartialLeftAdjointSource) :=
      ObjectProperty.homMk (L.map (Table.globe n).lastInclusion)
    haveI : IsIso (L.map (Table.globe n).lastInclusion) := by
      change IsIso (L.map (𝟙 (GlobularPresheaf.disk.{0} n)))
      infer_instance
    haveI : IsIso ((ObjectProperty.ι N.leftAdjointObjIsDefined).map f) := by
      change IsIso (L.map (Table.globe n).lastInclusion)
      infer_instance
    haveI : IsIso f := isIso_of_fully_faithful (ObjectProperty.ι N.leftAdjointObjIsDefined) f
    refine ⟨hT, ?_, ?_⟩
    · exact IsCofibrationCategory.isomorphisms_le (N.partialLeftAdjoint.map f) inferInstance
    · exact IsCylinderCategory.isomorphisms_le_weakEquivalences (N.partialLeftAdjoint.map f)
        inferInstance
  | @attach n T b h hl hr ih =>
    obtain ⟨hT, hcofT, hwT⟩ := ih
    let A' : N.PartialLeftAdjointSource := (frameSmallGlobes B).obj (Globe.mk b)
    let B' : N.PartialLeftAdjointSource := ⟨L.obj T.realize, hT⟩
    let D' : N.PartialLeftAdjointSource := (frameSmallGlobes B).obj (Globe.mk h)
    let last : (frameSmallGlobes B).obj (Globe.mk n) ⟶ B' :=
      ObjectProperty.homMk (L.map T.lastInclusion)
    let f₀ := GlobularPresheaf.face hl true ≫ T.lastInclusion
    let g₀ := GlobularPresheaf.face hr false
    let f := L.map f₀
    let g := L.map g₀
    let k := L.map (pushout.inl f₀ g₀)
    let j := L.map (pushout.inr f₀ g₀)
    let f' : A' ⟶ B' := ObjectProperty.homMk f
    let g' : A' ⟶ D' := ObjectProperty.homMk g
    have hcomp : f' = (frameSmallGlobes B).map (Globe.face hl true) ≫ last := by
      apply ObjectProperty.hom_ext
      change L.map (GlobularPresheaf.face hl true ≫ T.lastInclusion) =
        L.map (GlobularPresheaf.face hl true) ≫ L.map T.lastInclusion
      exact L.map_comp _ _
    have hface := frameSmallFace_trivial B hB hl true
    have hf : cofibrations X (N.partialLeftAdjoint.map f') ∧
        weakEquivalences X (N.partialLeftAdjoint.map f') := by
      rw [hcomp, N.partialLeftAdjoint.map_comp]
      exact ⟨(IsCofibrationCategory.isMultiplicative (C := X)).comp_mem _ _ hface.1 hcofT,
        (IsCylinderCategory.weakEquivalences_isMultiplicative (C := X)).comp_mem _ _ hface.2 hwT⟩
    have sq : IsPushout f g k j := (IsPushout.of_hasPushout f₀ g₀).map L
    have hPush : HasPushout (N.partialLeftAdjoint.map f') (N.partialLeftAdjoint.map g') :=
      IsCofibrationCategory.hasPushout _ _ hf.1
    have hNew : N.leftAdjointObjIsDefined (L.obj (Table.attach T b h hl hr).realize) :=
      leftAdjointObjIsDefined_pushout N f g k j sq A'.property B'.property D'.property hPush
    let P' : N.PartialLeftAdjointSource := ⟨L.obj (Table.attach T b h hl hr).realize, hNew⟩
    let k' : B' ⟶ P' := ObjectProperty.homMk k
    let j' : D' ⟶ P' := ObjectProperty.homMk j
    have imageSq := partialLeftAdjoint_isPushout N f g k j sq
      A'.property B'.property D'.property P'.property
    have hcj : cofibrations X (N.partialLeftAdjoint.map j') :=
      (IsCofibrationCategory.isStableUnderCobaseChange (C := X)).of_isPushout imageSq.flip hf.1
    have hwj : weakEquivalences X (N.partialLeftAdjoint.map j') :=
      IsCylinderCategory.trivialCofibration_cobaseChange _ _ _ _ imageSq hf.1 hf.2
    exact ⟨hNew, hcj, hwj⟩

/-- Every finite shape lies in the domain of the frame's partial adjoint. -/
theorem frameShape_leftAdjointObjIsDefined (B : GlobularFrame X)
    (hB : ∀ n,
      (cofibrations X (B.diagram.source n) ∧ weakEquivalences X (B.diagram.source n)) ∧
        (cofibrations X (B.diagram.target n) ∧ weakEquivalences X (B.diagram.target n)))
    (S : Shape) : (frameNerve B).leftAdjointObjIsDefined (Shape.liftedRealization.obj S) :=
  (frameTable_realizable B hB S.2).choose

/-- Finite shapes as objects in the domain of the partial adjoint. -/
def frameShapeDomain (B : GlobularFrame X)
    (hB : ∀ n,
      (cofibrations X (B.diagram.source n) ∧ weakEquivalences X (B.diagram.source n)) ∧
        (cofibrations X (B.diagram.target n) ∧ weakEquivalences X (B.diagram.target n))) :
    Shape ⥤ (frameNerve B).PartialLeftAdjointSource :=
  ObjectProperty.lift (frameNerve B).leftAdjointObjIsDefined Shape.liftedRealization
    (frameShape_leftAdjointObjIsDefined B hB)

/-- Realize finite shapes using the partial adjoint. -/
def finiteFrameRealization (B : GlobularFrame X)
    (hB : ∀ n,
      (cofibrations X (B.diagram.source n) ∧ weakEquivalences X (B.diagram.source n)) ∧
        (cofibrations X (B.diagram.target n) ∧ weakEquivalences X (B.diagram.target n))) :
    Shape ⥤ X := frameShapeDomain B hB ⋙ (frameNerve B).partialLeftAdjoint

set_option backward.isDefEq.respectTransparency false in
/-- The finite frame realization preserves the defining globular-sum pushouts. -/
def finiteFrameInterpretation (B : GlobularFrame X)
    (hB : ∀ n,
      (cofibrations X (B.diagram.source n) ∧ weakEquivalences X (B.diagram.source n)) ∧
        (cofibrations X (B.diagram.target n) ∧ weakEquivalences X (B.diagram.target n))) :
    ShapeInterpretation X where
  functor := finiteFrameRealization B hB
  sums S b h hl hr := partialLeftAdjoint_isPushout (frameNerve B) _ _ _ _
    (Shape.liftedRealization_pushout S b h hl hr)
    (frameShape_leftAdjointObjIsDefined B hB (Shape.globe b))
    (frameShape_leftAdjointObjIsDefined B hB S)
    (frameShape_leftAdjointObjIsDefined B hB (Shape.globe h))
    (frameShape_leftAdjointObjIsDefined B hB (S.attach b h hl hr))

set_option backward.isDefEq.respectTransparency false in
/-- The finite shape interpretation has the original cofibrant globular frame. -/
def finiteFrameFramed (B : GlobularFrame X) (hc : ∀ n, cofibrations X (B.inc n))
    (hB : ∀ n,
      (cofibrations X (B.diagram.source n) ∧ weakEquivalences X (B.diagram.source n)) ∧
        (cofibrations X (B.diagram.target n) ∧ weakEquivalences X (B.diagram.target n))) :
    FramedShapeInterpretation (finiteFrameInterpretation B hB) where
  frame := B
  diskIso n := (frameSmallGlobesComparison B).app (Globe.mk n)
  source n := by
    change B.diagram.source n ≫ ((frameSmallGlobesComparison B).app (Globe.mk (n+1))).hom =
      ((frameSmallGlobesComparison B).app (Globe.mk n)).hom ≫
        (frameSmallGlobes B ⋙ (frameNerve B).partialLeftAdjoint).map (Globe.source n)
    simpa only [Iso.app_hom, CoGlobularObject.functor, Globe.source, Globe.face, CoGlobularObject.eval,
      CoGlobularObject.face_succ, CoGlobularObject.adjacent, Bool.false_eq_true, ↓reduceIte] using
      (frameSmallGlobesComparison B).hom.naturality (Globe.source n)
  target n := by
    change B.diagram.target n ≫ ((frameSmallGlobesComparison B).app (Globe.mk (n+1))).hom =
      ((frameSmallGlobesComparison B).app (Globe.mk n)).hom ≫
        (frameSmallGlobes B ⋙ (frameNerve B).partialLeftAdjoint).map (Globe.target n)
    simpa only [Iso.app_hom, CoGlobularObject.functor, Globe.target, Globe.face, CoGlobularObject.eval,
      CoGlobularObject.face_succ, CoGlobularObject.adjacent, ↓reduceIte] using
      (frameSmallGlobesComparison B).hom.naturality (Globe.target n)
  inc_cof := hc

/-- The last disk as a morphism of finite shapes. -/
def lastShapeInclusion (S : Shape) : Shape.globe S.1 ⟶ S := S.2.lastInclusion

/-- The realized last-disk inclusion is a trivial cofibration. -/
theorem finiteFrame_last_trivial (B : GlobularFrame X)
    (hB : ∀ n,
      (cofibrations X (B.diagram.source n) ∧ weakEquivalences X (B.diagram.source n)) ∧
        (cofibrations X (B.diagram.target n) ∧ weakEquivalences X (B.diagram.target n)))
    (S : Shape) :
    let f := (finiteFrameRealization B hB).map (lastShapeInclusion S)
    cofibrations X f ∧ weakEquivalences X f :=
  (frameTable_realizable B hB S.2).choose_spec

/-- A canonical proper source face from the zero disk, or its identity in dimension zero. -/
def frameFromZero (B : GlobularFrame X) : ∀ n, B.obj 0 ⟶ B.obj n
  | 0 => 𝟙 _
  | n+1 => B.diagram.face (Nat.zero_lt_succ n) false

/-- All frame maps from the zero disk are weak equivalences. -/
theorem frameFromZero_weak (B : GlobularFrame X)
    (hB : ∀ n,
      (cofibrations X (B.diagram.source n) ∧ weakEquivalences X (B.diagram.source n)) ∧
        (cofibrations X (B.diagram.target n) ∧ weakEquivalences X (B.diagram.target n)))
    (n : ℕ) : weakEquivalences X (frameFromZero B n) := by
  cases n with
  | zero =>
    change weakEquivalences X (𝟙 (B.obj 0))
    exact IsCylinderCategory.isomorphisms_le_weakEquivalences _
      (MorphismProperty.isomorphisms.infer_property _)
  | succ n => exact (frameFace_trivial B hB (Nat.zero_lt_succ n) false).2

/-- Every realized finite shape admits a weak equivalence from the marked zero disk. -/
theorem finiteFrame_shape_from_zero (B : GlobularFrame X)
    (hB : ∀ n,
      (cofibrations X (B.diagram.source n) ∧ weakEquivalences X (B.diagram.source n)) ∧
        (cofibrations X (B.diagram.target n) ∧ weakEquivalences X (B.diagram.target n)))
    (S : Shape) :
    ∃ w : B.obj 0 ⟶ (finiteFrameRealization B hB).obj S, weakEquivalences X w := by
  let w := frameFromZero B S.1 ≫ ((frameSmallGlobesComparison B).app (Globe.mk S.1)).hom ≫
    (finiteFrameRealization B hB).map (lastShapeInclusion S)
  exact ⟨w, (IsCylinderCategory.weakEquivalences_isMultiplicative (C := X)).comp_mem _ _
    (frameFromZero_weak B hB S.1)
    ((IsCylinderCategory.weakEquivalences_isMultiplicative (C := X)).comp_mem _ _
      (IsCylinderCategory.isomorphisms_le_weakEquivalences _
        ((frameSmallGlobesComparison B).app (Globe.mk S.1)).isIso_hom)
      (finiteFrame_last_trivial B hB S).2)⟩

#print axioms frameShape_leftAdjointObjIsDefined
#print axioms finiteFrameFramed
#print axioms finiteFrame_shape_from_zero

end HomotopyHypothesis.FiniteCategory.Lifting
