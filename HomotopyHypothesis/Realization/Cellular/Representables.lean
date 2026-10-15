import HomotopyHypothesis.Blueprint.Defs
noncomputable section

open CategoryTheory Limits Opposite
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Blueprint

namespace HomotopyHypothesis.Realization.Cellular

universe u

variable {C : GlobularTheory.{u}} (R : OAIRealization C)
    (L : C.Model ⥤ TopCat.{u}) (adj : L ⊣ R.Pi)

/-- Adjunction and Yoneda identify the realization of a representable. -/
def realizationHomEquiv (S : Shape) (X : TopCat.{u}) :
    (L.obj (freeShape C S) ⟶ X) ≃ (R.functor.obj ⟨S⟩ ⟶ X) :=
  (adj.homEquiv (freeShape C S) X).trans
    (show (freeShape C S ⟶ R.Pi.obj X) ≃ (R.functor.obj ⟨S⟩ ⟶ X) from yonedaEquiv)

theorem realizationHomEquiv_comp (S : Shape) {X Y : TopCat.{u}}
    (a : L.obj (freeShape C S) ⟶ X) (f : X ⟶ Y) :
    realizationHomEquiv R L adj S Y (a ≫ f) = realizationHomEquiv R L adj S X a ≫ f := by
  change yonedaEquiv (adj.homEquiv _ _ (a ≫ f)) = _
  rw [adj.homEquiv_naturality_right]
  rfl

/-- The realization of a representable is its value under the original functor. -/
def realizationRepresentableIso (S : Shape) :
    L.obj (freeShape C S) ≅ R.functor.obj ⟨S⟩ :=
  (show (coyoneda.obj (op (R.functor.obj ⟨S⟩))).CorepresentableBy
      (L.obj (freeShape C S)) from
    { homEquiv := realizationHomEquiv R L adj S _
      homEquiv_comp := fun f a => realizationHomEquiv_comp R L adj S a f }).uniqueUpToIso
    (Functor.CorepresentableBy.coyoneda _)

@[simp]
theorem realizationRepresentableIso_inv (S : Shape) :
    (realizationRepresentableIso R L adj S).inv =
      realizationHomEquiv R L adj S _ (𝟙 _) := rfl

@[simp]
theorem realizationHomEquiv_iso_hom (S : Shape) :
    realizationHomEquiv R L adj S _ (realizationRepresentableIso R L adj S).hom = 𝟙 _ := by
  change realizationHomEquiv R L adj S _
    ((realizationHomEquiv R L adj S _).symm (𝟙 _)) = _
  exact Equiv.apply_symm_apply _ _

set_option backward.isDefEq.respectTransparency false in
/-- The representable comparison commutes with all theory morphisms. -/
theorem realizationRepresentableIso_naturality {S T : Shape}
    (f : (⟨S⟩ : C.Obj) ⟶ ⟨T⟩) :
    L.map (show freeShape C S ⟶ freeShape C T from yoneda.map f) ≫
        (realizationRepresentableIso R L adj T).hom =
      (realizationRepresentableIso R L adj S).hom ≫ R.functor.map f := by
  apply (realizationHomEquiv R L adj S _).injective
  rw [realizationHomEquiv_comp R L adj S _ (R.functor.map f),
    realizationHomEquiv_iso_hom, Category.id_comp]
  simp only [realizationHomEquiv, Equiv.trans_apply]
  rw [adj.homEquiv_naturality_left]
  change yonedaEquiv (yoneda.map f ≫
    (show yoneda.obj (⟨T⟩ : C.Obj) ⟶ (R.Pi.obj _).presheaf from
      adj.homEquiv _ _ (realizationRepresentableIso R L adj T).hom)) = _
  rw [← yonedaEquiv_naturality]
  change R.functor.map f ≫ realizationHomEquiv R L adj T _ _ = _
  rw [realizationHomEquiv_iso_hom, Category.comp_id]

/-- The realization of a representable globe is the standard topological disk. -/
def realizationDiskIso (n : ℕ) : L.obj (disk C n) ≅ TopCat.disk.{u} n :=
  realizationRepresentableIso R L adj (Shape.globe n) ≪≫ R.onGlobes.app (Globe.mk n)

end HomotopyHypothesis.Realization.Cellular
