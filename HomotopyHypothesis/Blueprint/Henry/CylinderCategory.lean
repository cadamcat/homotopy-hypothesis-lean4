import Mathlib
/-!
# Cylinder categories

Cofibration categories, pre-cylinder categories and cylinder categories, following
S. Henry, *Algebraic models of homotopy types and the homotopy hypothesis*,
arXiv:1609.04622 (cited as `H:<line>` of its TeX source), §2.1 and §3.1.

The classes of cofibrations and weak equivalences are Mathlib's
`HomotopicalAlgebra.CategoryWithCofibrations` and
`HomotopicalAlgebra.CategoryWithWeakEquivalences`; the axioms are `Prop`-valued classes on top of
them, so that a proof that a concrete category satisfies the axioms is a theorem and never part of a
definition.

All notions are stated without chosen colimits: pushouts are `IsPushout` squares and coproducts
`X ⊔ X` are pushouts over an initial object. Henry's framework is strict (1-categorical), so
liftings and equalities of functors below are strict.
-/

universe v u v' u'

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopyHypothesis.Henry

section Definitions

variable (C : Type u) [Category.{v} C]

/-- The 2-out-of-6 property (H:377): if `f ≫ g` and `g ≫ h` are in `W`, then so are `f`, `g`, `h`
and `f ≫ g ≫ h`. -/
def TwoOutOfSix (W : MorphismProperty C) : Prop :=
  ∀ ⦃X Y Z T : C⦄ (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T), W (f ≫ g) → W (g ≫ h) →
    W f ∧ W g ∧ W h ∧ W (f ≫ g ≫ h)

/-- A cofibration category (H:443, Def 2.1.3): cofibrations contain the isomorphisms and are
closed under composition; there is an initial object, and every object is cofibrant; pushouts along
cofibrations exist and cofibrations are stable under pushout. -/
class IsCofibrationCategory [CategoryWithCofibrations C] : Prop where
  isomorphisms_le : MorphismProperty.isomorphisms C ≤ cofibrations C
  isMultiplicative : (cofibrations C).IsMultiplicative
  exists_initial : ∃ I : C, Nonempty (IsInitial I)
  initial_cofibration : ∀ {I : C} (hI : IsInitial I) (X : C), cofibrations C (hI.to X)
  hasPushout : ∀ {A B X : C} (i : A ⟶ B) (f : A ⟶ X), cofibrations C i → HasPushout i f
  isStableUnderCobaseChange : (cofibrations C).IsStableUnderCobaseChange

/-- A pre-cylinder category (H:1500, Def 3.1.1): a cofibration category with a class of weak
equivalences satisfying 2-out-of-6 and the cube (gluing) lemma (H:722, Prop 2.2.12).

The weak equivalences are also required to contain the isomorphisms and to be closed under
composition; Henry's definition leaves this implicit, but it is needed for the smallest such class
to make sense. The gluing condition reads: given two pushout
squares `B ← A → X` (with `i : A ⟶ B` a cofibration, pushout `P`) and `B' ← A' → X'` (with `i'` a
cofibration, pushout `P'`), weak equivalences `vA`, `vB`, `vX` between them forming commutative
squares, any map `φ : P ⟶ P'` compatible with the pushout inclusions is a weak equivalence. -/
class IsPreCylinderCategory [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] : Prop
    extends IsCofibrationCategory C where
  isomorphisms_le_weakEquivalences : MorphismProperty.isomorphisms C ≤ weakEquivalences C
  weakEquivalences_isMultiplicative : (weakEquivalences C).IsMultiplicative
  twoOutOfSix : TwoOutOfSix C (weakEquivalences C)
  gluing : ∀ {A B X P A' B' X' P' : C} (i : A ⟶ B) (f : A ⟶ X) (k : B ⟶ P) (j : X ⟶ P)
    (i' : A' ⟶ B') (f' : A' ⟶ X') (k' : B' ⟶ P') (j' : X' ⟶ P')
    (vA : A ⟶ A') (vB : B ⟶ B') (vX : X ⟶ X') (φ : P ⟶ P'),
    IsPushout i f k j → IsPushout i' f' k' j' →
    cofibrations C i → cofibrations C i' →
    weakEquivalences C vA → weakEquivalences C vB → weakEquivalences C vX →
    i ≫ vB = vA ≫ i' → f ≫ vX = vA ≫ f' → k ≫ φ = vB ≫ k' → j ≫ φ = vX ≫ j' →
    weakEquivalences C φ

/-- The axioms on a class of weak equivalences `W` of a pre-cylinder category with cofibrations
`cof` (H:1500, Def 3.1.1): `W` contains the isomorphisms, is closed under composition, satisfies
2-out-of-6 and the gluing condition of `IsPreCylinderCategory`. Used to define weak equivalences of
freely generated pre-cylinder categories as the smallest such class containing given maps. -/
def IsWeakEquivalenceClass (cof W : MorphismProperty C) : Prop :=
  MorphismProperty.isomorphisms C ≤ W ∧ W.IsMultiplicative ∧ TwoOutOfSix C W ∧
  ∀ {A B X P A' B' X' P' : C} (i : A ⟶ B) (f : A ⟶ X) (k : B ⟶ P) (j : X ⟶ P)
    (i' : A' ⟶ B') (f' : A' ⟶ X') (k' : B' ⟶ P') (j' : X' ⟶ P')
    (vA : A ⟶ A') (vB : B ⟶ B') (vX : X ⟶ X') (φ : P ⟶ P'),
    IsPushout i f k j → IsPushout i' f' k' j' → cof i → cof i' → W vA → W vB → W vX →
    i ≫ vB = vA ≫ i' → f ≫ vX = vA ≫ f' → k ≫ φ = vB ≫ k' → j ≫ φ = vX ≫ j' → W φ

variable {C}

/-- A relative cylinder object for a map `i : A ⟶ B` (H:530, Def after Cor 2.2.3): a pushout
`P = B ⊔_A B` with inclusions `j₀ j₁`, and a factorization `P ⟶ I ⟶ B` of the codiagonal as a
cofibration `c` followed by a weak equivalence `p`. For `A` initial this is a cylinder object
`X ⊔ X ↪ IX ⥲ X` (H:398). -/
structure RelativeCylinder [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
    {A B : C} (i : A ⟶ B) where
  /-- the pushout `B ⊔_A B` -/
  P : C
  /-- first inclusion into `B ⊔_A B` -/
  j₀ : B ⟶ P
  /-- second inclusion into `B ⊔_A B` -/
  j₁ : B ⟶ P
  isPushout : IsPushout i i j₀ j₁
  /-- the cylinder object `I_A B` -/
  I : C
  /-- the cofibration `B ⊔_A B ↪ I_A B` -/
  c : P ⟶ I
  /-- the weak equivalence `I_A B ⥲ B` -/
  p : I ⟶ B
  c_mem : cofibrations C c
  p_mem : weakEquivalences C p
  j₀_c_p : j₀ ≫ c ≫ p = 𝟙 B
  j₁_c_p : j₁ ≫ c ≫ p = 𝟙 B

/-- A cylinder category (H:370, Def 2.1.1): (1) weak equivalences and cofibrations contain the
isomorphisms and are closed under composition; (2) weak equivalences satisfy 2-out-of-6; (3) there is
an initial object and every object is cofibrant; (4) pushouts of cofibrations exist and are
cofibrations; (5) pushouts of trivial cofibrations are trivial cofibrations; (6) every object has a
cylinder object; (7) every trivial cofibration has a retraction. -/
class IsCylinderCategory (C : Type u) [Category.{v} C] [CategoryWithCofibrations C]
    [CategoryWithWeakEquivalences C] : Prop extends IsCofibrationCategory C where
  isomorphisms_le_weakEquivalences : MorphismProperty.isomorphisms C ≤ weakEquivalences C
  weakEquivalences_isMultiplicative : (weakEquivalences C).IsMultiplicative
  twoOutOfSix : TwoOutOfSix C (weakEquivalences C)
  trivialCofibration_cobaseChange : ∀ {A B X P : C} (i : A ⟶ B) (f : A ⟶ X) (k : B ⟶ P)
    (j : X ⟶ P), IsPushout i f k j → cofibrations C i → weakEquivalences C i →
    weakEquivalences C j
  exists_cylinder : ∀ {I : C} (hI : IsInitial I) (X : C), Nonempty (RelativeCylinder (hI.to X))
  exists_retraction : ∀ {A B : C} (i : A ⟶ B), cofibrations C i → weakEquivalences C i →
    ∃ r : B ⟶ A, i ≫ r = 𝟙 A

/-- Two maps `f g : B ⟶ X` are homotopic relative to `i : A ⟶ B` (H:560–600) if they are the two
restrictions of a map out of some relative cylinder object for `i`. By H Prop 2.2.8(1) the choice
of the cylinder does not matter in a cylinder category. -/
def RelHomotopic [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
    {A B X : C} (i : A ⟶ B) (f g : B ⟶ X) : Prop :=
  ∃ (cyl : RelativeCylinder i) (H : cyl.I ⟶ X), cyl.j₀ ≫ cyl.c ≫ H = f ∧ cyl.j₁ ≫ cyl.c ≫ H = g

/-- Two maps are homotopic if they are homotopic relative to the initial object (H:560). -/
def Homotopic [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
    {X Y : C} (f g : X ⟶ Y) : Prop :=
  ∃ (I : C) (hI : IsInitial I), RelHomotopic (hI.to X) f g

/-- An object `X` is h-terminal (H:2667, Def 4.4.3) if every map `A ⟶ X` extends along every
cofibration `A ↪ B`. -/
def IsHTerminal [CategoryWithCofibrations C] (X : C) : Prop :=
  ∀ ⦃A B : C⦄ (i : A ⟶ B), cofibrations C i → ∀ a : A ⟶ X, ∃ b : B ⟶ X, i ≫ b = a

end Definitions

section Morphisms

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- A morphism of cofibration categories (H:443): a functor sending cofibrations to cofibrations,
initial objects to initial objects, and pushout squares along a cofibration to pushout squares. -/
structure IsCofibrationMorphism [CategoryWithCofibrations C] [CategoryWithCofibrations D]
    (F : C ⥤ D) : Prop where
  map_cofibration : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), cofibrations C f → cofibrations D (F.map f)
  map_initial : ∀ ⦃I : C⦄, IsInitial I → Nonempty (IsInitial (F.obj I))
  map_isPushout : ∀ ⦃A B X P : C⦄ (i : A ⟶ B) (f : A ⟶ X) (k : B ⟶ P) (j : X ⟶ P),
    IsPushout i f k j → cofibrations C i → IsPushout (F.map i) (F.map f) (F.map k) (F.map j)

/-- A morphism of (pre-)cylinder categories (H:427, H:1500): a morphism of cofibration categories
that also sends weak equivalences to weak equivalences ("exact functor"). -/
structure IsCylinderMorphism [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
    [CategoryWithCofibrations D] [CategoryWithWeakEquivalences D] (F : C ⥤ D) : Prop
    extends IsCofibrationMorphism F where
  map_weakEquivalence : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), weakEquivalences C f →
    weakEquivalences D (F.map f)

end Morphisms

end HomotopyHypothesis.Henry
