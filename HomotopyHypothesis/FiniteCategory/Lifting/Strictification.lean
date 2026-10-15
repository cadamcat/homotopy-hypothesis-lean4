import HomotopyHypothesis.Blueprint.Henry.Coherator
/-!+# Strictification along isofibrations

An isofibration turns a functor lifting up to natural isomorphism into a strict lifting.
The construction also preserves a specified object when the original isomorphism is compatible
with a chosen isomorphism at that object.
-/

universe v u v₁ u₁ v₂ u₂

open CategoryTheory Limits HomotopicalAlgebra
open HomotopyHypothesis.Henry

namespace HomotopyHypothesis.FiniteCategory.Lifting

section Conjugation

variable {C : Type u} [Category.{v} C] {X : Type u₁} [Category.{v₁} X]

/-- Conjugate the action of a functor by a family of object isomorphisms. -/
def conjugate (L : C ⥤ X) (Z : C → X) (e : ∀ c, L.obj c ≅ Z c) : C ⥤ X where
  obj := Z
  map {a b} f := (e a).inv ≫ L.map f ≫ (e b).hom
  map_id _ := by simp
  map_comp f g := by simp [Category.assoc]

/-- The conjugated functor is naturally isomorphic to the original. -/
def conjugateIso (L : C ⥤ X) (Z : C → X) (e : ∀ c, L.obj c ≅ Z c) :
    L ≅ conjugate L Z e :=
  NatIso.ofComponents e (by intro a b f; simp [conjugate])

end Conjugation

section Strictification

variable {C : Type u} [Category.{v} C]
  {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y]

/-- Strictify a lifting while retaining the marked object exactly. -/
theorem strictify_pointed {p : X ⥤ Y} (hp : IsIsofibration p)
    (L : C ⥤ X) (h : C ⥤ Y) (α : L ⋙ p ≅ h) (o : C) (x : X)
    (hx : h.obj o = p.obj x) (a : L.obj o ≅ x)
    (ha : p.map a.hom = (α.app o).hom ≫ eqToHom hx) :
    ∃ (l : C ⥤ X) (β : L ≅ l), l ⋙ p = h ∧ l.obj o = x := by
  classical
  have choices : ∀ c : C, ∃ (z : X) (e : L.obj c ≅ z) (q : p.obj z = h.obj c),
      p.map e.hom = (α.app c).hom ≫ eqToHom q.symm ∧ (c = o → z = x) := by
    intro c
    by_cases hc : c = o
    · subst c
      exact ⟨x, a, hx.symm, ha, fun _ => rfl⟩
    · obtain ⟨z, e, q, he⟩ := hp (L.obj c) (h.obj c) (α.app c)
      exact ⟨z, e, q, he, fun hc' => (hc hc').elim⟩
  choose Z e q he hz using choices
  let l := conjugate L Z e
  let β : L ≅ l := conjugateIso L Z e
  refine ⟨l, β, ?_, hz o rfl⟩
  let γ : l ⋙ p ≅ h := (Functor.isoWhiskerRight β p).symm ≪≫ α
  refine Functor.ext_of_iso γ q ?_
  intro c
  change p.map (e c).inv ≫ (α.app c).hom = eqToHom (q c)
  rw [← cancel_epi (p.map (e c).hom)]
  simp only [← Category.assoc, ← p.map_comp, Iso.hom_inv_id, p.map_id, Category.id_comp]
  rw [he c]
  simp

end Strictification

#print axioms strictify_pointed

end HomotopyHypothesis.FiniteCategory.Lifting
