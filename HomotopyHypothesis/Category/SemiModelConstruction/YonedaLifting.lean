import HomotopyHypothesis.Blueprint.Henry.Completion
universe w v u

open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace HomotopyHypothesis.Category.SemiModelConstruction

open Henry

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C] [LocallySmall.{w} C]

theorem shrinkYoneda_isCompletionPresheaf (X : C) :
    IsCompletionPresheaf C (shrinkYoneda.{w}.obj X) := by
  refine ⟨fun I hI => ?_, fun A B Y Q i f k j h hi => ?_⟩
  · exact ⟨Types.isTerminalEquivUnique _
      (hI.op.isTerminalObj (shrinkYoneda.{w}.obj X) _)⟩
  · exact h.op.flip.map (shrinkYoneda.{w}.obj X)

noncomputable abbrev completionSmallYoneda : C ⥤ Completion.{w} C :=
  ObjectProperty.lift _ shrinkYoneda shrinkYoneda_isCompletionPresheaf

noncomputable def completionSmallYonedaHomEquiv (A : C) (X : Completion.{w} C) :
    (completionSmallYoneda.obj A ⟶ X) ≃ X.obj.obj (op A) :=
  (ObjectProperty.fullyFaithfulι _).homEquiv.trans shrinkYonedaEquiv

theorem completionSmallYoneda_lifting_iff {A B : C} (i : A ⟶ B)
    {X Y : Completion.{w} C} (f : X ⟶ Y) :
    HasLiftingProperty (completionSmallYoneda.map i) f ↔
      ∀ (a : X.obj.obj (op A)) (b : Y.obj.obj (op B)),
        f.hom.app (op A) a = Y.obj.map i.op b →
          ∃ l : X.obj.obj (op B), X.obj.map i.op l = a ∧ f.hom.app (op B) l = b := by
  constructor
  · intro h a b hab
    let a' : completionSmallYoneda.obj A ⟶ X :=
      ObjectProperty.homMk (shrinkYonedaEquiv.symm a)
    let b' : completionSmallYoneda.obj B ⟶ Y :=
      ObjectProperty.homMk (shrinkYonedaEquiv.symm b)
    have sq : CommSq a' (completionSmallYoneda.map i) f b' := by
      constructor
      apply ObjectProperty.hom_ext
      apply shrinkYonedaEquiv.injective
      change shrinkYonedaEquiv (shrinkYonedaEquiv.symm a ≫ f.hom) =
        shrinkYonedaEquiv (shrinkYoneda.map i ≫ shrinkYonedaEquiv.symm b)
      rw [shrinkYonedaEquiv_comp, ← shrinkYonedaEquiv_naturality]
      simpa using hab
    letI := h
    refine ⟨shrinkYonedaEquiv sq.lift.hom, ?_, ?_⟩
    · rw [shrinkYonedaEquiv_naturality]
      change shrinkYonedaEquiv ((completionSmallYoneda.map i ≫ sq.lift).hom) = a
      rw [sq.fac_left]
      exact shrinkYonedaEquiv.apply_symm_apply a
    · rw [← shrinkYonedaEquiv_comp]
      change shrinkYonedaEquiv ((sq.lift ≫ f).hom) = b
      rw [sq.fac_right]
      exact shrinkYonedaEquiv.apply_symm_apply b
  · intro h
    constructor
    intro a' b' sq
    have hab : f.hom.app (op A) (shrinkYonedaEquiv a'.hom) =
        Y.obj.map i.op (shrinkYonedaEquiv b'.hom) := by
      have hs := congrArg (fun t => shrinkYonedaEquiv t.hom) sq.w
      change shrinkYonedaEquiv (a'.hom ≫ f.hom) =
        shrinkYonedaEquiv (shrinkYoneda.map i ≫ b'.hom) at hs
      rw [shrinkYonedaEquiv_comp, ← shrinkYonedaEquiv_naturality] at hs
      exact hs
    obtain ⟨l, hl, hfl⟩ := h (shrinkYonedaEquiv a'.hom) (shrinkYonedaEquiv b'.hom) hab
    refine CommSq.HasLift.mk' {
      l := ObjectProperty.homMk (shrinkYonedaEquiv.symm l)
      fac_left := ?_
      fac_right := ?_ }
    · apply ObjectProperty.hom_ext
      apply shrinkYonedaEquiv.injective
      change shrinkYonedaEquiv (shrinkYoneda.map i ≫ shrinkYonedaEquiv.symm l) = _
      rw [← shrinkYonedaEquiv_naturality]
      simpa using hl
    · apply ObjectProperty.hom_ext
      apply shrinkYonedaEquiv.injective
      change shrinkYonedaEquiv (shrinkYonedaEquiv.symm l ≫ f.hom) = _
      rw [shrinkYonedaEquiv_comp]
      simpa using hfl

def completionElementRLP (S : MorphismProperty C) : MorphismProperty (Completion.{w} C) :=
  fun X Y f => ∀ ⦃A B : C⦄ (i : A ⟶ B), S i →
    ∀ (a : X.obj.obj (op A)) (b : Y.obj.obj (op B)),
      f.hom.app (op A) a = Y.obj.map i.op b →
        ∃ l : X.obj.obj (op B), X.obj.map i.op l = a ∧ f.hom.app (op B) l = b

#print axioms completionSmallYoneda_lifting_iff

end HomotopyHypothesis.Category.SemiModelConstruction
