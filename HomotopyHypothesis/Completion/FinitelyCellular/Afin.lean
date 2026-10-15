import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Completion.FinitelyCellular.Basic
import HomotopyHypothesis.Completion.FinitelyCellular.Free
/-
# The free functor into finitely cellular models.

The Yoneda embedding of `C.Obj` lands in `Afin`, and sends globular sums
to pushouts along finite cell maps.
-/

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck
open HomotopyHypothesis.Blueprint
open HomotopyHypothesis.Henry

noncomputable section

namespace HomotopyHypothesis.Completion.FinitelyCellular

universe u

variable {C : GlobularTheory.{u}}

/-- The free functor `C.Obj ⥤ C.Model` (Yoneda). -/
def FreeFunctor : C.Obj ⥤ C.Model where
  obj X :=
    { presheaf := yoneda.obj X
      sums := fun S b h hl hr => ((C.sums S b h hl hr).op.map (yoneda.obj X)).flip }
  map f := yoneda.map f

/-- It coincides with `freeShape` on shapes. -/
theorem FreeFunctor_obj_shape (S : OAI.Grothendieck.Shape) :
    FreeFunctor (C := C).obj ⟨S⟩ = FreeShape (C := C) S := rfl

/-- The free functor lands in `Afin`. -/
def FreeAfin (hC : C.IsCoherator) : C.Obj ⥤ Afin C hC where
  obj X := ⟨FreeFunctor (C := C).obj X, freeShape_mem X.shape⟩
  map f := ObjectProperty.homMk (FreeFunctor (C := C).map f)

/-- Pushing a square forward along a fully faithful inclusion reflects pushouts:
    if the image is a pushout and the vertex lies in the subcategory, so is the source. -/
theorem isPushout_of_full {D : Type*} [Category D] {E : Type*} [Category E]
    (F : D ⥤ E) [F.Full] [F.Faithful] {A B X Q : D}
    {i : A ⟶ B} {f : A ⟶ X} {k : B ⟶ Q} {j : X ⟶ Q}
    (h : IsPushout (F.map i) (F.map f) (F.map k) (F.map j)) :
    IsPushout i f k j := by
  apply IsPushout.mk'
  · have hw : F.map (i ≫ k) = F.map (f ≫ j) := by
      rw [F.map_comp, F.map_comp]; exact h.w
    exact F.map_injective hw
  · intro T p p' hp hp'
    have hpE : F.map k ≫ F.map p = F.map k ≫ F.map p' := by
      rw [← F.map_comp, ← F.map_comp]; exact congrArg F.map hp
    have hqE : F.map j ≫ F.map p = F.map j ≫ F.map p' := by
      rw [← F.map_comp, ← F.map_comp]; exact congrArg F.map hp'
    have hEE : F.map p = F.map p' := h.hom_ext hpE hqE
    exact F.map_injective hEE
  · intro T p q hpq
    have hpE : F.map i ≫ F.map p = F.map f ≫ F.map q := by
      rw [← F.map_comp, ← F.map_comp]; exact congrArg F.map hpq
    obtain ⟨r, hr1, hr2⟩ := h.exists_desc _ _ hpE
    obtain ⟨r', rfl⟩ := F.map_surjective r
    refine ⟨r', ?_, ?_⟩
    · have hrr : F.map (k ≫ r') = F.map p := by
        rw [F.map_comp]; exact hr1
      exact F.map_injective hrr
    · have hrr : F.map (j ≫ r') = F.map q := by
        rw [F.map_comp]; exact hr2
      exact F.map_injective hrr

/-- The free functor sends the face maps to cofibrations of `Afin`. -/
theorem freeAfin_face_cofibration (hC : C.IsCoherator) {b h : ℕ} (hr : b < h) :
    cofibrations (Afin C hC)
      ((FreeAfin hC).map (C.toTheoryData.arity.map (Shape.face hr false))) := by
  show finiteCellMaps C ((Afin.ι hC).map _)
  exact face_mem_finiteCellMaps hr false

/-- The free functor sends globular sums to pushouts in `Afin`. -/
theorem freeAfin_attach_isPushout (hC : C.IsCoherator) (S : Shape)
    (b h : ℕ) (hl : b < S.1) (hr : b < h) :
    IsPushout ((FreeAfin hC).map (C.toTheoryData.arity.map (S.seam hl)))
      ((FreeAfin hC).map (C.toTheoryData.arity.map (Shape.face hr false)))
      ((FreeAfin hC).map (C.toTheoryData.arity.map (S.inl b h hl hr)))
      ((FreeAfin hC).map (C.toTheoryData.arity.map (S.inr b h hl hr))) := by
  apply isPushout_of_full (F := Afin.ι hC)
  exact freeShape_attach_isPushout S b h hl hr

end HomotopyHypothesis.Completion.FinitelyCellular
