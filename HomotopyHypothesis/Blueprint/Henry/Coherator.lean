import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
/-!
# Pre-fibrations and cylinder coherators

Pre-fibrations of pre-cylinder categories (H:2021, Def 4.1.1) and the lifting properties against
them that define (trivial) cofibrations (H:2048, Def 4.1.3), and cylinder coherators
(H:2754, Def 5.1.1).

A morphism `F_* ⟶ X` out of the free pre-cylinder category on one object is the same as an object
of `X` (H:1565, Prop 3.1.7). We therefore state the lifting properties of `F_* ⟶ C` (classifying an
object `o : C`) directly in terms of objects: a square from `F_* ⟶ C` to `p : X ⥤ Y` is an object
`x : X` and a morphism `h : C ⥤ Y` with `h o = p x`, and a lift is a morphism `l : C ⥤ X` with
`l ⋙ p = h` and `l o = x`.

The lifting properties quantify over cylinder categories in fixed universes `(u₂, v₂)`, given as
explicit universe parameters.
-/

universe u₂ v₂ v u v' u'

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopyHypothesis.Henry

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
  {D : Type u'} [Category.{v'} D] [CategoryWithCofibrations D] [CategoryWithWeakEquivalences D]

/-- A pre-fibration (H:2021, Def 4.1.1): retractions of trivial cofibrations, and factorizations as
a cofibration followed by a weak equivalence, lift strictly along `p`. -/
structure IsPreFibration (p : C ⥤ D) : Prop where
  lift_retraction : ∀ ⦃A B : C⦄ (s : A ⟶ B), cofibrations C s → weakEquivalences C s →
    ∀ r : p.obj B ⟶ p.obj A, p.map s ≫ r = 𝟙 _ →
      ∃ r' : B ⟶ A, s ≫ r' = 𝟙 A ∧ p.map r' = r
  lift_factorization : ∀ ⦃A B : C⦄ (f : A ⟶ B) ⦃Q : D⦄ (i : p.obj A ⟶ Q) (w : Q ⟶ p.obj B),
    cofibrations D i → weakEquivalences D w → i ≫ w = p.map f →
      ∃ (P : C) (i' : A ⟶ P) (w' : P ⟶ B) (e : p.obj P = Q),
        cofibrations C i' ∧ weakEquivalences C w' ∧ i' ≫ w' = f ∧
          p.map i' = i ≫ eqToHom e.symm ∧ p.map w' = eqToHom e ≫ w

/-- `p` lifts isomorphisms: every isomorphism `p x ≅ y` is the image of an isomorphism `x ≅ x'`
with `p x' = y`. Henry works with categories up to equivalence (H:1565–1575, H:1647–1668); with
this condition a lift up to natural isomorphism can be replaced by a strict lift, which the
strict lifting properties below require for full replete categories of models. -/
def IsIsofibration (p : C ⥤ D) : Prop :=
  ∀ (x : C) (y : D) (e : p.obj x ≅ y), ∃ (x' : C) (e' : x ≅ x') (h : p.obj x' = y),
    p.map e'.hom = e.hom ≫ eqToHom h.symm

/-- The class of morphisms used as right-hand side of the lifting properties below: morphisms of
cylinder categories `p : X ⥤ Y` between cylinder categories in the universes `(u₂, v₂)` that are
pre-fibrations and isofibrations, and also acyclic when `acyclic` is `true` (H:2048, Def 4.1.3:
fibrations between fibrant objects, resp. acyclic ones). -/
def IsLiftingTarget (acyclic : Bool) (X : Type u₂) [Category.{v₂} X] [CategoryWithCofibrations X]
    [CategoryWithWeakEquivalences X] (Y : Type u₂) [Category.{v₂} Y] [CategoryWithCofibrations Y]
    [CategoryWithWeakEquivalences Y] (p : X ⥤ Y) : Prop :=
  IsCylinderCategory X ∧ IsCylinderCategory Y ∧ IsCylinderMorphism p ∧ IsPreFibration p ∧
    IsIsofibration p ∧ (acyclic = true → IsAcyclic p)

/-- Lifting property of the morphism `F_* ⟶ C` classifying `o : C` against the lifting targets of
`IsLiftingTarget acyclic` in universes `(u₂, v₂)`, restricted to squares whose top object satisfies
`good`. -/
def PointLifting (acyclic : Bool) (C : Type u) [Category.{v} C] [CategoryWithCofibrations C]
    [CategoryWithWeakEquivalences C] (o : C)
    (good : ∀ (X : Type u₂) [Category.{v₂} X] [CategoryWithCofibrations X]
      [CategoryWithWeakEquivalences X] (Y : Type u₂) [Category.{v₂} Y] [CategoryWithCofibrations Y]
      [CategoryWithWeakEquivalences Y], (X ⥤ Y) → X → Prop) : Prop :=
  ∀ (X : Type u₂) [Category.{v₂} X] [CategoryWithCofibrations X] [CategoryWithWeakEquivalences X]
    (Y : Type u₂) [Category.{v₂} Y] [CategoryWithCofibrations Y] [CategoryWithWeakEquivalences Y]
    (p : X ⥤ Y), IsLiftingTarget acyclic X Y p →
    ∀ (x : X), good X Y p x → ∀ (h : C ⥤ Y), IsCylinderMorphism h → h.obj o = p.obj x →
      ∃ l : C ⥤ X, IsCylinderMorphism l ∧ l ⋙ p = h ∧ l.obj o = x

/-- A cylinder coherator (H:2754, Def 5.1.1): a cylinder category `C` with a marked object `o`
such that the morphism `F_* ⟶ C` classifying `o` is a trivial cofibration, i.e. has the left lifting
property against pre-fibrations between cylinder categories (H:2048). Universes of the test
categories: `(u₂, v₂)`. -/
def IsCylinderCoherator (C : Type u) [Category.{v} C] [CategoryWithCofibrations C]
    [CategoryWithWeakEquivalences C] (o : C) : Prop :=
  IsCylinderCategory C ∧ PointLifting.{u₂, v₂} false C o (fun _ _ _ _ _ _ _ _ _ _ => True)

/-- The morphism `F_* ⟶ C` classifying `o` is a cofibration (H:2050, Def 4.1.3): it has the left
lifting property against acyclic pre-fibrations between cylinder categories. -/
def IsCofibrantAt (C : Type u) [Category.{v} C] [CategoryWithCofibrations C]
    [CategoryWithWeakEquivalences C] (o : C) : Prop :=
  PointLifting.{u₂, v₂} true C o (fun _ _ _ _ _ _ _ _ _ _ => True)

/-- The conclusion of H Lemma 5.3.9 (H:3114) for `(C, o)`: morphisms out of `C` lift along
pre-fibrations between cylinder categories as soon as the chosen lift `x` of the image of `o` is
h-terminal and so is its image. -/
def LiftsAtHTerminal (C : Type u) [Category.{v} C] [CategoryWithCofibrations C]
    [CategoryWithWeakEquivalences C] (o : C) : Prop :=
  PointLifting.{u₂, v₂} false C o
    (fun _X _ _ _ _Y _ _ _ p x => IsHTerminal x ∧ IsHTerminal (p.obj x))

end HomotopyHypothesis.Henry
