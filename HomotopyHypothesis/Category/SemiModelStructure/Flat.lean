import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Category.SemiModelStructure.Filtered
import HomotopyHypothesis.Category.SemiModelConstruction.YonedaLifting
/-!
# Flat objects of the completion

An object of the completion is flat if it is a filtered colimit of representable objects. Flat
objects are closed under filtered colimits and under retracts.
-/

universe w v u

open CategoryTheory Limits HomotopicalAlgebra Opposite

attribute [local instance] Cardinal.fact_isRegular_aleph0

namespace HomotopyHypothesis.Category.SemiModelStructure

open Henry Category.SemiModelConstruction

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]

section

variable [LocallySmall.{w} C]

/-- Objects of the completion isomorphic to a representable object. -/
def IsRepresentableCompletion : ObjectProperty (Completion.{w} C) :=
  fun X => ∃ E : C, Nonempty (X ≅ completionSmallYoneda.{w}.obj E)

/-- Flat objects: filtered colimits of representable objects. -/
def IsFlat : ObjectProperty (Completion.{w} C) :=
  ObjectProperty.ind.{w} IsRepresentableCompletion

theorem isRepresentableCompletion_le_isFinitelyPresentable :
    IsRepresentableCompletion.{w} (C := C) ≤
      ObjectProperty.isFinitelyPresentable.{w} (Completion.{w} C) := by
  rintro X ⟨E, ⟨e⟩⟩
  have := completionSmallYoneda_isFinitelyPresentable.{w} (C := C) E
  exact isCardinalPresentable_of_iso e.symm _

theorem isFlat_of_isRepresentable {X : Completion.{w} C}
    (hX : IsRepresentableCompletion X) : IsFlat X :=
  ObjectProperty.le_ind _ _ hX

theorem isFlat_yoneda (E : C) : IsFlat (completionSmallYoneda.{w}.obj E) :=
  isFlat_of_isRepresentable ⟨E, ⟨Iso.refl _⟩⟩

end

section

variable [EssentiallySmall.{w} C]

theorem isFlat_ind_eq :
    ObjectProperty.ind.{w} (IsFlat.{w} (C := C)) = IsFlat.{w} (C := C) := by
  have := completion_locallySmall.{w} (C := C)
  exact ObjectProperty.ind_ind isRepresentableCompletion_le_isFinitelyPresentable

/-- A filtered colimit of flat objects is flat. -/
theorem isFlat_of_isColimit {J : Type w} [SmallCategory J] [IsFiltered J]
    {F : J ⥤ Completion.{w} C} {c : Cocone F} (hc : IsColimit c)
    (h : ∀ j, IsFlat (F.obj j)) : IsFlat c.pt := by
  rw [← isFlat_ind_eq]
  exact ⟨J, inferInstance, inferInstance, ⟨F, c.ι, hc⟩, h⟩

/-- A colimit over an essentially small filtered category of flat objects is flat. -/
theorem isFlat_of_isColimit' {J : Type*} [Category* J] [EssentiallySmall.{w} J] [IsFiltered J]
    {F : J ⥤ Completion.{w} C} {c : Cocone F} (hc : IsColimit c)
    (h : ∀ j, IsFlat (F.obj j)) : IsFlat c.pt := by
  rw [← isFlat_ind_eq]
  exact ObjectProperty.of_essentiallySmall_index ⟨F, c.ι, hc⟩ h

/-- The telescope of an idempotent: a retract `X` of `Y` is the colimit of the sequence
`Y ⟶ Y ⟶ ⋯` whose maps are the idempotent `r ≫ s`. -/
def telescopeCocone {D : Type*} [Category* D] {X Y : D} (s : X ⟶ Y) (r : Y ⟶ X) (h : s ≫ r = 𝟙 X) :
    Cocone (Functor.ofSequence (X := fun _ : ℕ => Y) (fun _ => r ≫ s)) where
  pt := X
  ι := NatTrans.ofSequence (fun _ => r) (fun n => by
    rw [Functor.ofSequence_map_homOfLE_succ]
    change (r ≫ s) ≫ r = r ≫ 𝟙 X
    rw [Category.assoc, h])

theorem retract_comp {D : Type*} [Category* D] {X Y Z : D} (s : X ⟶ Y) (r : Y ⟶ X)
    (h : s ≫ r = 𝟙 X) (g : X ⟶ Z) : s ≫ r ≫ g = g := by
  rw [← Category.assoc, h, Category.id_comp]

theorem telescope_step {D : Type*} [Category* D] {X Y : D} (s : X ⟶ Y) (r : Y ⟶ X)
    (c : Cocone (Functor.ofSequence (X := fun _ : ℕ => Y) (fun _ => r ≫ s))) (m : ℕ) :
    c.ι.app m = r ≫ s ≫ c.ι.app (m + 1) := by
  have := c.w (homOfLE (Nat.le_add_right m 1))
  rw [Functor.ofSequence_map_homOfLE_succ] at this
  rw [← this]
  exact Category.assoc _ _ _

theorem telescope_idem {D : Type*} [Category* D] {X Y : D} (s : X ⟶ Y) (r : Y ⟶ X)
    (h : s ≫ r = 𝟙 X)
    (c : Cocone (Functor.ofSequence (X := fun _ : ℕ => Y) (fun _ => r ≫ s))) (m : ℕ) :
    r ≫ s ≫ c.ι.app m = c.ι.app m := by
  have h' : ∀ (g : X ⟶ c.pt), s ≫ r ≫ g = g := fun g => by
    rw [← Category.assoc, h, Category.id_comp]
  have e1 := telescope_step s r c m
  rw [e1, h']

theorem telescope_leg_eq {D : Type*} [Category* D] {X Y : D} (s : X ⟶ Y) (r : Y ⟶ X)
    (h : s ≫ r = 𝟙 X)
    (c : Cocone (Functor.ofSequence (X := fun _ : ℕ => Y) (fun _ => r ≫ s))) (n : ℕ) :
    c.ι.app n = c.ι.app 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← ih, telescope_step s r c n, telescope_idem s r h c (n + 1)]

def telescopeIsColimit {D : Type*} [Category* D] {X Y : D} (s : X ⟶ Y) (r : Y ⟶ X)
    (h : s ≫ r = 𝟙 X) : IsColimit (telescopeCocone s r h) where
  desc c := s ≫ c.ι.app 0
  fac c n := by
    simp only [telescopeCocone, NatTrans.ofSequence_app]
    rw [telescope_leg_eq s r h c n]
    exact telescope_idem s r h c 0
  uniq c m hm := by
    have h0 := hm 0
    rw [← h0]
    exact (retract_comp s r h m).symm

/-- A retract of a flat object is flat. -/
theorem isFlat_of_retract {X Y : Completion.{w} C} (s : X ⟶ Y) (r : Y ⟶ X) (h : s ≫ r = 𝟙 X)
    (hY : IsFlat Y) : IsFlat X :=
  isFlat_of_isColimit' (telescopeIsColimit s r h) (fun _ => hY)

theorem isFlat_of_iso {X Y : Completion.{w} C} (e : X ≅ Y) (hX : IsFlat X) : IsFlat Y :=
  isFlat_of_retract e.inv e.hom e.inv_hom_id hX

end

end HomotopyHypothesis.Category.SemiModelStructure
