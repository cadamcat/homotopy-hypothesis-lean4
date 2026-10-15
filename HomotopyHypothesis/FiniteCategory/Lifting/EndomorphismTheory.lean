import HomotopyHypothesis.FiniteCategory.Lifting.Nerve
/-!
# Endomorphism theories of globular sums

A globular-sum preserving shape diagram determines a globular theory of its endomorphisms.
Compatible diagrams over a functor give a morphism of these theories. Filler lifting then
extends a cellular coherator interpretation, by its free presentation.
-/

noncomputable section

universe u v u₁

open CategoryTheory Limits
open OAI.Grothendieck

namespace HomotopyHypothesis.FiniteCategory.Lifting

/-- A realization of the finite globular sums in a category. -/
structure ShapeInterpretation (X : Type u) [Category.{v} X] where
  functor : Shape ⥤ X
  sums : ∀ (S : Shape) (b h : ℕ) (hl : b < S.1) (hr : b < h),
    IsPushout (functor.map (S.seam hl)) (functor.map (Shape.face hr false))
      (functor.map (S.inl b h hl hr)) (functor.map (S.inr b h hl hr))

namespace ShapeInterpretation

variable {X : Type u} [Category.{v} X] {Y : Type u₁} [Category.{v} Y]

/-- Endomorphisms between the interpreted shapes. -/
def endData (R : ShapeInterpretation X) : TheoryData.{v} where
  Hom S T := R.functor.obj S ⟶ R.functor.obj T
  id S := 𝟙 _
  comp f g := f ≫ g
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc
  base f := R.functor.map f
  base_id := R.functor.map_id
  base_comp := R.functor.map_comp

/-- The fully faithful realization of the endomorphism data. -/
def embedding (R : ShapeInterpretation X) : R.endData.Obj ⥤ X where
  obj S := R.functor.obj S.shape
  map f := f

instance (R : ShapeInterpretation X) : R.embedding.Full where
  map_surjective f := ⟨f, rfl⟩

instance (R : ShapeInterpretation X) : R.embedding.Faithful where
  map_injective h := h

/-- The endomorphism globular theory, whose sums are inherited from the interpretation. -/
def endTheory (R : ShapeInterpretation X) : GlobularTheory.{v} where
  toTheoryData := R.endData
  sums S b h hl hr := IsPushout.of_map_of_faithful R.embedding (R.sums S b h hl hr)

/-- Interpret a theory morphism in the objects of the shape diagram. -/
def interpretation {C : GlobularTheory.{v}} (R : ShapeInterpretation X)
    (a : GlobularTheory.Morphism C R.endTheory) : TheoryInterpretation C X where
  functor :=
    { obj S := R.functor.obj S.shape
      map f := a.map f
      map_id S := a.map_id S.shape
      map_comp f g := a.map_comp f g }
  sums S b h hl hr := by
    change IsPushout (a.map (C.base (S.seam hl))) (a.map (C.base (Shape.face hr false)))
      (a.map (C.base (S.inl b h hl hr))) (a.map (C.base (S.inr b h hl hr)))
    simpa only [a.map_base, endTheory, endData] using R.sums S b h hl hr

/-- A compatible diagram induces a morphism between its endomorphism theories. -/
def map (R : ShapeInterpretation X) (S : ShapeInterpretation Y) (p : X ⥤ Y)
    (α : R.functor ⋙ p ≅ S.functor) : GlobularTheory.Morphism R.endTheory S.endTheory where
  map {A B} f := (α.app A).inv ≫ p.map f ≫ (α.app B).hom
  map_id A := by
    change (α.app A).inv ≫ p.map (𝟙 _) ≫ (α.app A).hom = 𝟙 _
    simp
  map_comp {A B D} f g := by
    dsimp only [endTheory, endData] at f g
    change (α.app A).inv ≫ p.map (f ≫ g) ≫ (α.app D).hom =
      ((α.app A).inv ≫ p.map f ≫ (α.app B).hom) ≫
        ((α.app B).inv ≫ p.map g ≫ (α.app D).hom)
    simp [Category.assoc]
  map_base {A B} f := by
    change α.inv.app A ≫ (R.functor ⋙ p).map f ≫ α.hom.app B = S.functor.map f
    rw [α.hom.naturality f]
    simp

/-- Filler lifting on the endomorphism theories gives a lift of any cellular interpretation. -/
theorem lift_cellular {C : GlobularTheory.{v}} (P : C.CellularPresentation)
    (R : ShapeInterpretation X) (S : ShapeInterpretation Y) (p : X ⥤ Y)
    (α : R.functor ⋙ p ≅ S.functor)
    (hp : GlobularTheory.LiftsFillers (R.map S p α))
    (f : GlobularTheory.Morphism C S.endTheory) :
    ∃ a : GlobularTheory.Morphism C R.endTheory,
      a.comp (R.map S p α) = f ∧
        Nonempty ((R.interpretation a).functor ⋙ p ≅ (S.interpretation f).functor) := by
  obtain ⟨a, ha⟩ := P.lift (R.map S p α) hp f
  refine ⟨a, ha, ⟨NatIso.ofComponents (fun T => α.app T.shape) ?_⟩⟩
  intro A B g
  have hg := congrArg (fun z : GlobularTheory.Morphism C S.endTheory => z.map g) ha
  change (α.app A.shape).inv ≫ p.map (a.map g) ≫ (α.app B.shape).hom = f.map g at hg
  change p.map (a.map g) ≫ (α.app B.shape).hom = (α.app A.shape).hom ≫ f.map g
  rw [← cancel_epi (α.app A.shape).inv]
  simpa only [endTheory, endData, Category.assoc, Iso.inv_hom_id_assoc] using hg

end ShapeInterpretation

#print axioms ShapeInterpretation.lift_cellular

end HomotopyHypothesis.FiniteCategory.Lifting
