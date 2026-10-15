import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.FiniteCategory.Lifting.Exactness
import HomotopyHypothesis.FiniteCategory.Lifting.FillerLift
import HomotopyHypothesis.FiniteCategory.Lifting.FrameCofibrations
import HomotopyHypothesis.FiniteCategory.Lifting.PartialPushout
/-!
# Finite shape realization of a globular frame

The restricted Yoneda nerve of a globular frame has a partial left adjoint on the globular disks.
Finite globular sums can be added to its domain using their cofibration pushouts.
-/

noncomputable section

universe u v

open CategoryTheory Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck

namespace HomotopyHypothesis.FiniteCategory.Lifting

variable {X : Type u} [Category.{v} X]

/-- The globular-presheaf-valued nerve of a boundary frame. -/
def frameNerve (B : GlobularFrame X) : X ⥤ GlobularPresheaf.{v} :=
  Presheaf.restrictedULiftYoneda.{v} B.diagram.functor

set_option backward.isDefEq.respectTransparency false in
/-- A disk of the frame corepresents maps from the corresponding globular presheaf disk. -/
def frameGlobeCorepresentable (B : GlobularFrame X) (n : ℕ) :
    (frameNerve B ⋙ coyoneda.obj (op (GlobularPresheaf.disk.{v} n))).CorepresentableBy
      (B.obj n) where
  homEquiv {Y} := Equiv.ulift.symm.trans
    (uliftYonedaEquiv (F := (frameNerve B).obj Y) (X := Globe.mk n)).symm
  homEquiv_comp {Y Y'} f g := by
    change (uliftYonedaEquiv (F := (frameNerve B).obj Y')).symm (ULift.up (g ≫ f)) =
      (uliftYonedaEquiv (F := (frameNerve B).obj Y)).symm (ULift.up g) ≫ (frameNerve B).map f
    exact (uliftYonedaEquiv_symm_comp (X := op (Globe.mk n))
      (F := (frameNerve B).obj Y) (G := (frameNerve B).obj Y')
      (ULift.up g) ((frameNerve B).map f)).symm

/-- The partial left adjoint of the frame nerve is defined at every globular disk. -/
theorem frameGlobe_leftAdjointObjIsDefined (B : GlobularFrame X) (n : ℕ) :
    (frameNerve B).leftAdjointObjIsDefined (GlobularPresheaf.disk.{v} n) :=
  (frameGlobeCorepresentable B n).isCorepresentable

/-- The globular disks as objects in the domain of the partial left adjoint. -/
def frameGlobes (B : GlobularFrame X) : Globe ⥤ (frameNerve B).PartialLeftAdjointSource where
  obj n := ⟨GlobularPresheaf.disk n.dim, frameGlobe_leftAdjointObjIsDefined B n.dim⟩
  map f := ObjectProperty.homMk (uliftYoneda.map f)
  map_id n := by apply ObjectProperty.hom_ext; exact uliftYoneda.map_id n
  map_comp f g := by apply ObjectProperty.hom_ext; exact uliftYoneda.map_comp f g

/-- Identify each chosen partial-adjoint globe with its disk in the original frame. -/
def frameGlobeIso (B : GlobularFrame X) (n : ℕ) :
      B.obj n ≅ ((frameGlobes B) ⋙ (frameNerve B).partialLeftAdjoint).obj (Globe.mk n) := by
  letI := (frameGlobeCorepresentable B n).isCorepresentable
  exact (frameGlobeCorepresentable B n).isoCoreprX

set_option backward.isDefEq.respectTransparency false in
/-- The chosen disk isomorphism has the same universal element as the partial adjoint. -/
theorem frameGlobeIso_equiv (B : GlobularFrame X) (n : ℕ) :
    (frameGlobeCorepresentable B n).homEquiv (frameGlobeIso B n).hom =
      (frameNerve B).partialLeftAdjointHomEquiv
        (X := (frameGlobes B).obj (Globe.mk n)) (𝟙 _) := by
  simp [frameGlobeIso, Functor.CorepresentableBy.isoCoreprX,
    Functor.CorepresentableBy.uniqueUpToIso_hom, Coyoneda.fullyFaithful_preimage,
    Functor.partialLeftAdjointHomEquiv, frameGlobes]
  exact (frameGlobeCorepresentable B n).homEquiv.apply_symm_apply _

set_option backward.isDefEq.respectTransparency false in
/-- Disk corepresentability is natural in globular face maps. -/
theorem frameGlobeCorepresentable_left (B : GlobularFrame X) {m n : ℕ}
    (f : Globe.mk m ⟶ Globe.mk n) {Y : X} (a : B.obj n ⟶ Y) :
    (frameGlobeCorepresentable B m).homEquiv (B.diagram.eval f ≫ a) =
      uliftYoneda.map f ≫ (frameGlobeCorepresentable B n).homEquiv a := by
  change (uliftYonedaEquiv (F := (frameNerve B).obj Y)).symm
      (ULift.up (B.diagram.eval f ≫ a)) =
    uliftYoneda.map f ≫ (uliftYonedaEquiv (F := (frameNerve B).obj Y)).symm (ULift.up a)
  exact uliftYonedaEquiv_symm_map (F := (frameNerve B).obj Y) f.op (ULift.up a)

set_option backward.isDefEq.respectTransparency false in
/-- The chosen disk isomorphisms form a natural isomorphism on the globe category. -/
theorem frameGlobeIso_naturality (B : GlobularFrame X) {m n : ℕ}
    (f : Globe.mk m ⟶ Globe.mk n) :
    B.diagram.eval f ≫ (frameGlobeIso B n).hom = (frameGlobeIso B m).hom ≫
      ((frameGlobes B) ⋙ (frameNerve B).partialLeftAdjoint).map f := by
  apply (frameGlobeCorepresentable B m).homEquiv.injective
  rw [frameGlobeCorepresentable_left, frameGlobeIso_equiv,
    (frameGlobeCorepresentable B m).homEquiv_comp, frameGlobeIso_equiv]
  change uliftYoneda.map f ≫ (frameNerve B).partialLeftAdjointHomEquiv
      (X := (frameGlobes B).obj (Globe.mk n)) (𝟙 _) =
    (frameNerve B).partialLeftAdjointHomEquiv
      (X := (frameGlobes B).obj (Globe.mk m)) (𝟙 _) ≫
      (frameNerve B).map ((frameNerve B).partialLeftAdjoint.map ((frameGlobes B).map f))
  have hl := (frameNerve B).partialLeftAdjointHomEquiv_map_comp ((frameGlobes B).map f) (𝟙 _)
  have hr := (frameNerve B).partialLeftAdjointHomEquiv_comp
    (X := (frameGlobes B).obj (Globe.mk m)) (𝟙 _)
    ((frameNerve B).partialLeftAdjoint.map ((frameGlobes B).map f))
  simp only [Category.comp_id] at hl
  simp only [Category.id_comp] at hr
  exact hl.symm.trans hr

/-- The natural comparison between the frame and its partial-adjoint globes. -/
def frameGlobesIso (B : GlobularFrame X) :
    B.diagram.functor ≅ frameGlobes B ⋙ (frameNerve B).partialLeftAdjoint :=
  NatIso.ofComponents (fun n => frameGlobeIso B n.dim)
    (fun {m n} f => frameGlobeIso_naturality B (m := m.dim) (n := n.dim) f)

/-- The universe-raised small disks also lie in the domain of the frame's partial adjoint. -/
theorem frameSmallGlobe_leftAdjointObjIsDefined (B : GlobularFrame X) (n : ℕ) :
    (frameNerve B).leftAdjointObjIsDefined
      (GlobularPresheaf.liftSmall.{v}.obj (GlobularPresheaf.disk.{0} n)) :=
  leftAdjointObjIsDefined_iso (frameNerve B) (GlobularPresheaf.liftSmallDiskIso n)
    (frameGlobe_leftAdjointObjIsDefined B n)

/-- Universe-raised small disks in the domain of the partial adjoint. -/
def frameSmallGlobes (B : GlobularFrame X) : Globe ⥤ (frameNerve B).PartialLeftAdjointSource where
  obj n := ⟨GlobularPresheaf.liftSmall.obj (GlobularPresheaf.disk.{0} n.dim),
    frameSmallGlobe_leftAdjointObjIsDefined B n.dim⟩
  map f := ObjectProperty.homMk (GlobularPresheaf.liftSmall.map (uliftYoneda.{0}.map f))
  map_id n := by
    apply ObjectProperty.hom_ext
    change GlobularPresheaf.liftSmall.map (uliftYoneda.{0}.map (𝟙 n)) = 𝟙 _
    rw [uliftYoneda.map_id]
    exact GlobularPresheaf.liftSmall.map_id _
  map_comp f g := by
    apply ObjectProperty.hom_ext
    change GlobularPresheaf.liftSmall.map (uliftYoneda.{0}.map (f ≫ g)) =
      GlobularPresheaf.liftSmall.map (uliftYoneda.{0}.map f) ≫
        GlobularPresheaf.liftSmall.map (uliftYoneda.{0}.map g)
    rw [uliftYoneda.map_comp, Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Flatten the two universe lifts in the small disks. -/
def frameSmallGlobesIso (B : GlobularFrame X) : frameSmallGlobes B ≅ frameGlobes B :=
  NatIso.ofComponents (fun n => ObjectProperty.isoMk (frameNerve B).leftAdjointObjIsDefined
    (GlobularPresheaf.liftSmallDiskIso n.dim))
    (by
      intro m n f
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext T
      apply ConcreteCategory.hom_ext
      intro x
      rfl)

/-- The comparison between the original frame and the partial adjoint on small disks. -/
def frameSmallGlobesComparison (B : GlobularFrame X) :
    B.diagram.functor ≅ frameSmallGlobes B ⋙ (frameNerve B).partialLeftAdjoint :=
  frameGlobesIso B ≪≫ (Functor.isoWhiskerRight (frameSmallGlobesIso B)
    (frameNerve B).partialLeftAdjoint).symm

variable [CategoryWithCofibrations X] [CategoryWithWeakEquivalences X]
  [HomotopyHypothesis.Henry.IsCylinderCategory X]

/-- Proper small-disk face maps remain trivial cofibrations under the partial adjoint. -/
theorem frameSmallFace_trivial (B : GlobularFrame X)
    (hB : ∀ n,
      (cofibrations X (B.diagram.source n) ∧ weakEquivalences X (B.diagram.source n)) ∧
        (cofibrations X (B.diagram.target n) ∧ weakEquivalences X (B.diagram.target n)))
    {m n : ℕ} (h : m < n) (side : Bool) :
    let f := (frameSmallGlobes B ⋙ (frameNerve B).partialLeftAdjoint).map (Globe.face h side)
    cofibrations X f ∧ weakEquivalences X f := by
  have hf := frameFace_trivial B hB h side
  exact ⟨map_mem_of_natIso _ (HomotopyHypothesis.Henry.IsCofibrationCategory.isMultiplicative)
      (HomotopyHypothesis.Henry.IsCofibrationCategory.isomorphisms_le)
      (frameSmallGlobesComparison B) _ hf.1,
    map_mem_of_natIso _ (HomotopyHypothesis.Henry.IsCylinderCategory.weakEquivalences_isMultiplicative)
      (HomotopyHypothesis.Henry.IsCylinderCategory.isomorphisms_le_weakEquivalences)
      (frameSmallGlobesComparison B) _ hf.2⟩

#print axioms frameGlobe_leftAdjointObjIsDefined
#print axioms frameGlobeIso_naturality
#print axioms frameSmallFace_trivial

end HomotopyHypothesis.FiniteCategory.Lifting
