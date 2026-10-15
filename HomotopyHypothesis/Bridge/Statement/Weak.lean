import HomotopyHypothesis.Bridge.Statement.Shapes
import HomotopyHypothesis.Bridge.Statement.Theory
import HomotopyHypothesis.Challenge
/-!
# Weak equivalences of transported models

Restriction of models along the underlying functor of a transported theory preserves the
underlying globular sets (same cells, same source and target maps), the chosen units, and hence
the components and homotopy groups. It therefore preserves and reflects weak equivalences.
-/

noncomputable section

namespace HomotopyHypothesis.Bridge.Statement

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

theorem choose_congr_of_iff {α : Sort*} {p q : α → Prop} (hpq : ∀ x, p x ↔ q x)
    (h₁ : ∃ x, p x) (h₂ : ∃ x, q x) : Classical.choose h₁ = Classical.choose h₂ := by
  have : p = q := funext fun x => propext (hpq x)
  subst this
  rfl

variable {C : Grothendieck.GlobularTheory.{v}} (hC : C.IsCoherator)
  (hC' : (theoryToOAI C).IsCoherator)

include hC hC' in
theorem unit_theoryToOAI (n : ℕ) : (theoryToOAI C).unit hC' n = C.unit hC n := by
  unfold OAI.Grothendieck.GlobularTheory.unit Grothendieck.GlobularTheory.unit
  refine choose_congr_of_iff (fun z => ?_) _ _
  change C.comp (C.base (shapeFunctor.map
        (OAI.Grothendieck.Shape.face (Nat.lt_succ_self n) false))) z = C.id _ ∧
      C.comp (C.base (shapeFunctor.map
        (OAI.Grothendieck.Shape.face (Nat.lt_succ_self n) true))) z = C.id _ ↔
    C.comp (C.base (Grothendieck.Shape.face (Nat.lt_succ_self n) false)) z = C.id _ ∧
      C.comp (C.base (Grothendieck.Shape.face (Nat.lt_succ_self n) true)) z = C.id _
  rw [shapeFunctor_face, shapeFunctor_face]
  exact Iff.rfl

theorem source_modelToOAI (X : C.Model) (n : ℕ) :
    ((modelToOAI C).obj X).underlying.source n = X.underlying.source n := by
  have e1 : ((modelToOAI C).obj X).underlying.source n = X.presheaf.map (C.arity.map
      (shapeFunctor.map (OAI.Grothendieck.Shape.face (Nat.lt_succ_self n) false))).op := rfl
  have e2 : X.underlying.source n =
      X.presheaf.map (C.arity.map (Grothendieck.Shape.face (Nat.lt_succ_self n) false)).op := rfl
  rw [e1, e2, shapeFunctor_face]
  rfl

theorem target_modelToOAI (X : C.Model) (n : ℕ) :
    ((modelToOAI C).obj X).underlying.target n = X.underlying.target n := by
  have e1 : ((modelToOAI C).obj X).underlying.target n = X.presheaf.map (C.arity.map
      (shapeFunctor.map (OAI.Grothendieck.Shape.face (Nat.lt_succ_self n) true))).op := rfl
  have e2 : X.underlying.target n =
      X.presheaf.map (C.arity.map (Grothendieck.Shape.face (Nat.lt_succ_self n) true)).op := rfl
  rw [e1, e2, shapeFunctor_face]
  rfl

theorem joined_modelToOAI (X : C.Model) (n : ℕ) (a b : X.underlying.Cell n) :
    ((modelToOAI C).obj X).underlying.Joined n a b ↔ X.underlying.Joined n a b := by
  unfold OAI.Grothendieck.GlobularSet.Joined Grothendieck.GlobularSet.Joined
  rw [source_modelToOAI, target_modelToOAI]
  exact Iff.rfl

/-- Components of a transported model. -/
def componentsEquiv (X : C.Model) :
    ((modelToOAI C).obj X).Components ≃ X.Components :=
  Quot.congr (Equiv.refl _) fun a b => joined_modelToOAI X 0 a b

theorem componentsMap_modelToOAI {X Y : C.Model} (f : X ⟶ Y) :
    OAI.Grothendieck.GlobularTheory.Model.componentsMap ((modelToOAI C).map f) =
      (componentsEquiv Y).symm ∘ Grothendieck.GlobularTheory.Model.componentsMap f ∘
        componentsEquiv X := by
  funext q
  induction q using Quot.ind
  rfl

include hC hC' in
theorem unitCell_modelToOAI (X : C.Model) (k : ℕ) (y : X.underlying.Cell k) :
    ((modelToOAI C).obj X).unitCell hC' k y = X.unitCell hC k y :=
  congrArg (fun w => X.presheaf.map
      (show (⟨Grothendieck.Shape.globe (k + 1)⟩ : C.Obj) ⟶ ⟨Grothendieck.Shape.globe k⟩
        from w).op y)
    (unit_theoryToOAI hC hC' k)

include hC hC' in
theorem baseCell_modelToOAI (X : C.Model) (x : X.underlying.Cell 0) (k : ℕ) :
    ((modelToOAI C).obj X).baseCell hC' x k = X.baseCell hC x k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact (unitCell_modelToOAI hC hC' X k _).trans (congrArg (X.unitCell hC k) ih)

/-- Loops of a transported model. -/
def loopsEquiv (X : C.Model) (x : X.underlying.Cell 0) (n : ℕ) :
    ((modelToOAI C).obj X).Loops hC' x n ≃ X.Loops hC x n where
  toFun z := ⟨z.1,
    ⟨(congrFun (source_modelToOAI X n) z.1).symm.trans
        (z.2.1.trans (baseCell_modelToOAI hC hC' X x n)),
      (congrFun (target_modelToOAI X n) z.1).symm.trans
        (z.2.2.trans (baseCell_modelToOAI hC hC' X x n))⟩⟩
  invFun z := ⟨z.1,
    ⟨(congrFun (source_modelToOAI X n) z.1).trans
        (z.2.1.trans (baseCell_modelToOAI hC hC' X x n).symm),
      (congrFun (target_modelToOAI X n) z.1).trans
        (z.2.2.trans (baseCell_modelToOAI hC hC' X x n).symm)⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Homotopy groups of a transported model. -/
def homotopyGroupEquiv (X : C.Model) (x : X.underlying.Cell 0) (n : ℕ) :
    ((modelToOAI C).obj X).HomotopyGroup hC' x n ≃ X.HomotopyGroup hC x n :=
  Quot.congr (loopsEquiv hC hC' X x n) fun a b => joined_modelToOAI X (n + 1) a.1 b.1

theorem homotopyMap_modelToOAI {X Y : C.Model} (f : X ⟶ Y) (x : X.underlying.Cell 0) (n : ℕ) :
    OAI.Grothendieck.GlobularTheory.Model.homotopyMap ((modelToOAI C).map f) hC' x n =
      (homotopyGroupEquiv hC hC' Y _ n).symm ∘
        Grothendieck.GlobularTheory.Model.homotopyMap f hC x n ∘
          homotopyGroupEquiv hC hC' X x n := by
  funext q
  induction q using Quot.ind
  rfl

include hC hC' in
/-- Restriction of models preserves and reflects weak equivalences. -/
theorem weakEquivalence_modelToOAI_iff {X Y : C.Model} (f : X ⟶ Y) :
    OAI.Grothendieck.GlobularTheory.Model.WeakEquivalence hC' ((modelToOAI C).map f) ↔
      Grothendieck.GlobularTheory.Model.WeakEquivalence hC f := by
  unfold OAI.Grothendieck.GlobularTheory.Model.WeakEquivalence
    Grothendieck.GlobularTheory.Model.WeakEquivalence
  rw [componentsMap_modelToOAI, Equiv.comp_bijective, Equiv.bijective_comp]
  refine and_congr_right fun _ => forall_congr' fun x => forall_congr' fun n => ?_
  exact (congrArg Function.Bijective (homotopyMap_modelToOAI hC hC' f x n)).to_iff.trans
    ((Equiv.comp_bijective _ _).trans (Equiv.bijective_comp _ _))

end HomotopyHypothesis.Bridge.Statement
