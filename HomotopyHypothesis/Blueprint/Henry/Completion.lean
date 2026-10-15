import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
/-!
# The completion of a cofibration category

For a cofibration category `C`, its completion `C̃` (H:980, Def 2.4.1) is the category of presheaves
on `C` sending initial objects to singletons and pushouts along cofibrations to pullbacks. For a
cylinder category, H §2.4 equips it with a semi-model structure; here we define the classes of maps
of that structure (H:997, Def 2.4.3; H:1041, Def 2.4.5) and the restriction functors along
morphisms (H:993).

Maps between representables and elements are expressed through elements of presheaves, so that the
values of the presheaves may live in any universe `w`.
-/

universe w v u v' u'

open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace HomotopyHypothesis.Henry

variable (C : Type u) [Category.{v} C]

/-- The condition defining the completion (H:980): `P` sends initial objects to singletons and
pushout squares along a cofibration to pullback squares. -/
def IsCompletionPresheaf [CategoryWithCofibrations C] (P : Cᵒᵖ ⥤ Type w) : Prop :=
  (∀ ⦃I : C⦄, IsInitial I → Nonempty (Unique (P.obj (op I)))) ∧
  ∀ ⦃A B X Q : C⦄ (i : A ⟶ B) (f : A ⟶ X) (k : B ⟶ Q) (j : X ⟶ Q),
    IsPushout i f k j → cofibrations C i →
    IsPullback (P.map k.op) (P.map j.op) (P.map i.op) (P.map f.op)

/-- The completion `C̃` (H:980, Def 2.4.1), with values in `Type w`. -/
abbrev Completion [CategoryWithCofibrations C] : Type (max u v (w + 1)) :=
  ObjectProperty.FullSubcategory (IsCompletionPresheaf.{w} C)

variable {C}

section Classes

variable [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]

/-- Weak equivalences of presheaves (H:1041, Def 2.4.5): `f : X ⟶ Y` is a weak equivalence if
for every cofibration `i : A ↪ B` of `C`, every element `a ∈ X(A)` and `b ∈ Y(B)` with
`f(a) = b|_A`, there are `l ∈ X(B)` with `l|_A = a`, a relative cylinder `I_A B` for `i` and
`h ∈ Y(I_A B)` restricting to `f(l)` and `b` on the two ends. -/
def presheafWeakEquivalences : MorphismProperty (Cᵒᵖ ⥤ Type w) := fun X Y f =>
  ∀ ⦃A B : C⦄ (i : A ⟶ B), cofibrations C i →
    ∀ (a : X.obj (op A)) (b : Y.obj (op B)), f.app (op A) a = Y.map i.op b →
      ∃ (l : X.obj (op B)) (cyl : RelativeCylinder i) (h : Y.obj (op cyl.I)),
        X.map i.op l = a ∧ Y.map (cyl.j₀ ≫ cyl.c).op h = f.app (op B) l ∧
          Y.map (cyl.j₁ ≫ cyl.c).op h = b

/-- Trivial fibrations of presheaves (H:999, Def 2.4.3): maps with the right lifting property with
respect to the cofibrations of `C`, expressed on elements. -/
def presheafTrivialFibrations : MorphismProperty (Cᵒᵖ ⥤ Type w) := fun X Y f =>
  ∀ ⦃A B : C⦄ (i : A ⟶ B), cofibrations C i →
    ∀ (a : X.obj (op A)) (b : Y.obj (op B)), f.app (op A) a = Y.map i.op b →
      ∃ l : X.obj (op B), X.map i.op l = a ∧ f.app (op B) l = b

/-- Fibrations of presheaves (H:1043, Def 2.4.5): maps with the right lifting property with respect
to the trivial cofibrations of `C`, expressed on elements. -/
def presheafFibrations : MorphismProperty (Cᵒᵖ ⥤ Type w) := fun X Y f =>
  ∀ ⦃A B : C⦄ (i : A ⟶ B), cofibrations C i → weakEquivalences C i →
    ∀ (a : X.obj (op A)) (b : Y.obj (op B)), f.app (op A) a = Y.map i.op b →
      ∃ l : X.obj (op B), X.map i.op l = a ∧ f.app (op B) l = b

variable (C)

/-- Weak equivalences of the completion (H:1041, Def 2.4.5). -/
def Completion.weakEquivalences : MorphismProperty (Completion.{w} C) := fun _ _ f =>
  presheafWeakEquivalences f.hom

/-- Trivial fibrations of the completion (H:999, Def 2.4.3). -/
def Completion.trivialFibrations : MorphismProperty (Completion.{w} C) := fun _ _ f =>
  presheafTrivialFibrations f.hom

/-- Fibrations of the completion (H:1043, Def 2.4.5). -/
def Completion.fibrations : MorphismProperty (Completion.{w} C) := fun _ _ f =>
  presheafFibrations f.hom

/-- Cofibrations of the completion (H:1000–1011): the maps with the left lifting property with
respect to all trivial fibrations (equivalently, retracts of cellular maps). -/
def Completion.cofibrations : MorphismProperty (Completion.{w} C) :=
  (Completion.trivialFibrations C).llp

theorem presheafWeakEquivalences_respectsIso :
    (presheafWeakEquivalences : MorphismProperty (Cᵒᵖ ⥤ Type w)).RespectsIso := by
  apply MorphismProperty.RespectsIso.mk
  · intro X' X Y e f hf A B i hi a b hab
    obtain ⟨l, cyl, h, hl, h₀, h₁⟩ :=
      hf i hi (e.hom.app _ a) b (by simpa using hab)
    refine ⟨e.inv.app _ l, cyl, h, ?_, ?_, h₁⟩
    · rw [← NatTrans.naturality_apply, hl]
      simp
    · simpa using h₀
  · intro X Y Y' e f hf A B i hi a b hab
    obtain ⟨l, cyl, h, hl, h₀, h₁⟩ := hf i hi a (e.inv.app _ b) (by
      rw [← NatTrans.naturality_apply, ← hab]
      simp)
    refine ⟨l, cyl, e.hom.app _ h, hl, ?_, ?_⟩
    · rw [← NatTrans.naturality_apply, h₀]
      simp
    · rw [← NatTrans.naturality_apply, h₁]
      simp

/-- Weak equivalences of the completion are stable under composition with isomorphisms. -/
theorem Completion.weakEquivalences_respectsIso :
    (Completion.weakEquivalences.{w} C).RespectsIso := by
  have := presheafWeakEquivalences_respectsIso.{w} C
  apply MorphismProperty.RespectsIso.mk
  · intro X Y Z e f hf
    exact this.toRespectsLeft.precomp ((ObjectProperty.ι _).mapIso e).hom
      (show IsIso ((ObjectProperty.ι _).mapIso e).hom from inferInstance) f.hom hf
  · intro X Y Z e f hf
    exact this.toRespectsRight.postcomp ((ObjectProperty.ι _).mapIso e).hom
      (show IsIso ((ObjectProperty.ι _).mapIso e).hom from inferInstance) f.hom hf

end Classes

section Restriction

variable [CategoryWithCofibrations C] {D : Type u'} [Category.{v'} D]

/-- Restriction along a functor `G : C ⥤ D` sending initial objects to initial objects and pushout
squares along cofibrations to pushout squares: `Y ↦ (A ↦ Hom(G A, Y))` (H:993, and H:2790 for
`D` = spaces, where it is the fundamental `∞`-groupoid functor `π_∞`). -/
@[simps!]
def restrictionAlong (G : C ⥤ D) (hG₀ : ∀ ⦃I : C⦄, IsInitial I → Nonempty (IsInitial (G.obj I)))
    (hG₁ : ∀ ⦃A B X Q : C⦄ (i : A ⟶ B) (f : A ⟶ X) (k : B ⟶ Q) (j : X ⟶ Q),
      IsPushout i f k j → cofibrations C i → IsPushout (G.map i) (G.map f) (G.map k) (G.map j)) :
    D ⥤ Completion.{v'} C :=
  ObjectProperty.lift _ (yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj G.op) (fun Y => by
    refine ⟨fun I hI => ?_, fun A B X Q i f k j h hi => ?_⟩
    · obtain ⟨hGI⟩ := hG₀ hI
      exact ⟨⟨⟨hGI.to Y⟩, fun g => hGI.hom_ext _ _⟩⟩
    · exact ((hG₁ i f k j h hi).op.map (yoneda.obj Y)).flip)

variable (C) in
/-- The Yoneda embedding `C ⥤ C̃` (H:988). -/
abbrev Completion.yoneda : C ⥤ Completion.{v} C :=
  restrictionAlong (𝟭 C) (fun _ hI => ⟨hI⟩) (fun _ _ _ _ _ _ _ _ h _ => h)

end Restriction

end HomotopyHypothesis.Henry
