import HomotopyHypothesis.Bridge.Statement.Shapes
import HomotopyHypothesis.Blueprint.Bridge.GlobeOfOAI
import HomotopyHypothesis.Blueprint.Bridge.GlobeOfOAICompGlobeToOAI
import HomotopyHypothesis.Blueprint.Bridge.GlobeToOAI
import HomotopyHypothesis.Blueprint.Bridge.TopGlobesEq
import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Challenge
import HomotopyHypothesis.Bridge.GlobularEquivalence.Transport
/-!
# Transport of globular theories, realizations and models

A globular theory on the statement's shapes is pulled back along the fully faithful shape functor
to a globular theory on OpenAI's shapes, with the same hom-types. Topological realizations and
models are transported along the resulting functor of underlying categories, and the fundamental
∞-groupoid functors correspond.
-/

noncomputable section

namespace HomotopyHypothesis.Bridge.Statement

open CategoryTheory CategoryTheory.Limits
open HomotopyHypothesis.Bridge.GlobularEquivalence

universe u v

/-- The globes of the two shape categories correspond under the shape functor. -/
theorem shapeGlobes_comp_shapeFunctor :
    OAI.Grothendieck.GlobularTheory.shapeGlobes ⋙ shapeFunctor =
      HomotopyHypothesis.Blueprint.globeOfOAI ⋙
        HomotopyHypothesis.Grothendieck.GlobularTheory.shapeGlobes := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) fun X Y f => ?_
  obtain ⟨m⟩ := X; obtain ⟨n⟩ := Y
  have hf : @CategoryTheory.Functor.map _ _ _ _ HomotopyHypothesis.Blueprint.globeToOAI
      (Grothendieck.Globe.mk m) (Grothendieck.Globe.mk n)
      (HomotopyHypothesis.Blueprint.globeOfOAI.map f) = f := by
    change OAI.Grothendieck.Globe.Face _ _ at f
    cases f <;> rfl
  have key := diskIso_map.{0} (m := m) (n := n)
    (HomotopyHypothesis.Blueprint.globeOfOAI.map f)
  rw [hf] at key
  have e : ∀ {A B : Grothendieck.Shape} (p : A = A) (q : B = B) (g : A ⟶ B),
      eqToHom p ≫ g ≫ eqToHom q = g := by intros; simp
  exact ((Iso.inv_comp_eq (diskIso.{0} m)).2 key).trans
    (e (A := Grothendieck.Shape.globe m) (B := Grothendieck.Shape.globe n) rfl rfl
      (uliftYoneda.map (HomotopyHypothesis.Blueprint.globeOfOAI.map f))).symm

/-- A theory on the statement's shapes as a theory on OpenAI's shapes. -/
abbrev theoryDataToOAI (C : HomotopyHypothesis.Grothendieck.TheoryData.{v}) :
    OAI.Grothendieck.TheoryData.{v} where
  Hom S T := C.Hom (shapeOfOAI S) (shapeOfOAI T)
  id S := C.id _
  comp f g := C.comp f g
  id_comp f := C.id_comp f
  comp_id f := C.comp_id f
  assoc f g h := C.assoc f g h
  base f := C.base (shapeFunctor.map f)
  base_id S := by rw [shapeFunctor.map_id]; exact C.base_id _
  base_comp f g := by rw [shapeFunctor.map_comp]; exact C.base_comp _ _

/-- The underlying categories: identity on hom-types. -/
def objFunctor (C : HomotopyHypothesis.Grothendieck.TheoryData.{v}) :
    (theoryDataToOAI C).Obj ⥤ C.Obj where
  obj S := ⟨shapeOfOAI S.shape⟩
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

instance (C : HomotopyHypothesis.Grothendieck.TheoryData.{v}) : (objFunctor C).Full where
  map_surjective f := ⟨f, rfl⟩

instance (C : HomotopyHypothesis.Grothendieck.TheoryData.{v}) : (objFunctor C).Faithful where
  map_injective h := h

theorem arity_comp_objFunctor (C : HomotopyHypothesis.Grothendieck.TheoryData.{v}) :
    (theoryDataToOAI C).arity ⋙ objFunctor C = shapeFunctor ⋙ C.arity := rfl

/-- A globular theory on the statement's shapes as a globular theory on OpenAI's shapes. -/
abbrev theoryToOAI (C : HomotopyHypothesis.Grothendieck.GlobularTheory.{v}) :
    OAI.Grothendieck.GlobularTheory.{v} where
  toTheoryData := theoryDataToOAI C.toTheoryData
  sums S b h hl hr := by
    have H : IsPushout
        ((objFunctor C.toTheoryData).map ((theoryDataToOAI C.toTheoryData).arity.map (S.seam hl)))
        ((objFunctor C.toTheoryData).map
          ((theoryDataToOAI C.toTheoryData).arity.map (OAI.Grothendieck.Shape.face hr false)))
        ((objFunctor C.toTheoryData).map
          ((theoryDataToOAI C.toTheoryData).arity.map (S.inl b h hl hr)))
        ((objFunctor C.toTheoryData).map
          ((theoryDataToOAI C.toTheoryData).arity.map (S.inr b h hl hr))) := by
      change IsPushout (C.arity.map (shapeFunctor.map (S.seam hl)))
        (C.arity.map (shapeFunctor.map (OAI.Grothendieck.Shape.face hr false)))
        (C.arity.map (shapeFunctor.map (S.inl b h hl hr)))
        (C.arity.map (shapeFunctor.map (S.inr b h hl hr)))
      rw [shapeFunctor_seam, shapeFunctor_face, shapeFunctor_inl, shapeFunctor_inr]
      exact C.sums (shapeOfOAI S) b h hl hr
    exact IsPushout.of_map_of_faithful (F := objFunctor C.toTheoryData) H

theorem globes_comp_objFunctor (C : HomotopyHypothesis.Grothendieck.GlobularTheory.{v}) :
    (theoryToOAI C).globes ⋙ objFunctor C.toTheoryData =
      HomotopyHypothesis.Blueprint.globeOfOAI ⋙ C.globes := by
  change (OAI.Grothendieck.GlobularTheory.shapeGlobes ⋙ shapeFunctor) ⋙ C.arity =
    (HomotopyHypothesis.Blueprint.globeOfOAI ⋙
      HomotopyHypothesis.Grothendieck.GlobularTheory.shapeGlobes) ⋙ C.arity
  rw [shapeGlobes_comp_shapeFunctor]

/-- A topological realization of a theory as a realization of the transported theory. -/
def realizationToOAI {C : HomotopyHypothesis.Grothendieck.GlobularTheory.{u}}
    (R : HomotopyHypothesis.TopRealization C) :
    HomotopyHypothesis.Blueprint.OAIRealization (theoryToOAI C) where
  functor := objFunctor C.toTheoryData ⋙ R.functor
  onGlobes :=
    eqToIso (by rw [← Functor.assoc, globes_comp_objFunctor, Functor.assoc]) ≪≫
      Functor.isoWhiskerLeft HomotopyHypothesis.Blueprint.globeOfOAI R.onGlobes ≪≫
      eqToIso (by
        rw [HomotopyHypothesis.Blueprint.topGlobes_eq, ← Functor.assoc,
          HomotopyHypothesis.Blueprint.globeOfOAI_comp_globeToOAI, Functor.id_comp])
  sums S b h hl hr := by
    change IsPushout (R.functor.map (C.arity.map (shapeFunctor.map (S.seam hl))))
      (R.functor.map (C.arity.map (shapeFunctor.map (OAI.Grothendieck.Shape.face hr false))))
      (R.functor.map (C.arity.map (shapeFunctor.map (S.inl b h hl hr))))
      (R.functor.map (C.arity.map (shapeFunctor.map (S.inr b h hl hr))))
    rw [shapeFunctor_seam, shapeFunctor_face, shapeFunctor_inl, shapeFunctor_inr]
    exact R.sums (shapeOfOAI S) b h hl hr

/-- Models of a theory as models of the transported theory (restriction along `objFunctor`). -/
def modelToOAI (C : HomotopyHypothesis.Grothendieck.GlobularTheory.{v}) :
    C.Model ⥤ (theoryToOAI C).Model where
  obj X :=
    { presheaf := (objFunctor C.toTheoryData).op ⋙ X.presheaf
      sums S b h hl hr := by
        change IsPullback (X.presheaf.map (C.arity.map (shapeFunctor.map (S.inl b h hl hr))).op)
          (X.presheaf.map (C.arity.map (shapeFunctor.map (S.inr b h hl hr))).op)
          (X.presheaf.map (C.arity.map (shapeFunctor.map (S.seam hl))).op)
          (X.presheaf.map
            (C.arity.map (shapeFunctor.map (OAI.Grothendieck.Shape.face hr false))).op)
        rw [shapeFunctor_seam, shapeFunctor_face, shapeFunctor_inl, shapeFunctor_inr]
        exact X.sums (shapeOfOAI S) b h hl hr }
  map {X Y} f := show (objFunctor C.toTheoryData).op ⋙ X.presheaf ⟶
      (objFunctor C.toTheoryData).op ⋙ Y.presheaf from
    Functor.whiskerLeft (objFunctor C.toTheoryData).op f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The fundamental ∞-groupoid functors correspond. -/
theorem pi_realizationToOAI {C : HomotopyHypothesis.Grothendieck.GlobularTheory.{u}}
    (R : HomotopyHypothesis.TopRealization C) :
    (realizationToOAI R).Pi = HomotopyHypothesis.fundamentalGroupoidFunctor R ⋙ modelToOAI C :=
  rfl

end HomotopyHypothesis.Bridge.Statement
