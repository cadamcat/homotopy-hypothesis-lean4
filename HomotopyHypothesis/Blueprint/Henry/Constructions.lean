import HomotopyHypothesis.Blueprint.Henry.Coherator
/-!
# Constructions on cylinder categories

* the terminal cylinder category (H:430);
* products of cylinder categories, with componentwise cofibrations and weak equivalences (H:1532);
* the path category `C^eq` of cofibrant cospans of weak equivalences (H:2498, 4.2.8), with its
  projection to `C × C`;
* the homotopy slice `C^X` (H:2627, Prop 4.4.1) with its forgetful morphism to `C`.

Coproducts and relative latching objects are expressed as pushout squares: `IsCofibrantGluing`
says that the map from a pushout to a given object is a cofibration.
-/

universe v u

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopyHypothesis.Henry

section Gluing

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]

/-- Given a span `B ← A → X` (maps `f`, `g`) and a cocone `u : B ⟶ T`, `w : X ⟶ T` on it, the
induced map `B ⊔_A X ⟶ T` is a cofibration (for some, hence every, pushout). -/
def IsCofibrantGluing {A B X T : C} (f : A ⟶ B) (g : A ⟶ X) (u : B ⟶ T) (w : X ⟶ T) : Prop :=
  ∃ (P : C) (k : B ⟶ P) (j : X ⟶ P) (_ : IsPushout f g k j) (m : P ⟶ T),
    k ≫ m = u ∧ j ≫ m = w ∧ cofibrations C m

/-- The map `B ⊔ X ⟶ T` induced by `u : B ⟶ T` and `w : X ⟶ T` is a cofibration. -/
def IsCofibrantPair {B X T : C} (u : B ⟶ T) (w : X ⟶ T) : Prop :=
  ∃ (I : C) (hI : IsInitial I), IsCofibrantGluing (hI.to B) (hI.to X) u w

end Gluing

/-! ### The terminal cylinder category -/

/-- The terminal cylinder category (H:430): one object, one morphism, which is a trivial
cofibration. It lives in `Type (u + 1)` with morphisms in `Type u`. -/
def TerminalCat : Type (u + 1) := PUnit

instance : Category.{u} TerminalCat.{u} where
  Hom _ _ := PUnit
  id _ := PUnit.unit
  comp _ _ := PUnit.unit

instance : CategoryWithCofibrations TerminalCat.{u} := ⟨⊤⟩
instance : CategoryWithWeakEquivalences TerminalCat.{u} := ⟨⊤⟩

/-- The unique functor to the terminal cylinder category. -/
def toTerminalCat (C : Type*) [Category C] : C ⥤ TerminalCat.{u} where
  obj _ := PUnit.unit
  map _ := PUnit.unit

/-! ### Products -/

section Prod

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]

instance [CategoryWithCofibrations C] [CategoryWithCofibrations D] :
    CategoryWithCofibrations (C × D) :=
  ⟨fun _ _ f => cofibrations C f.1 ∧ cofibrations D f.2⟩

instance [CategoryWithWeakEquivalences C] [CategoryWithWeakEquivalences D] :
    CategoryWithWeakEquivalences (C × D) :=
  ⟨fun _ _ f => weakEquivalences C f.1 ∧ weakEquivalences D f.2⟩

end Prod

/-! ### The path category `C^eq` -/

section Path

variable (C : Type u) [Category.{v} C] [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]

/-- Objects of the path category `C^eq = [R_eq, C]` (H:2498): cospans `X_l ⟶ X_c ⟵ X_r` whose two
legs are weak equivalences and whose induced map `X_l ⊔ X_r ⟶ X_c` is a cofibration. -/
structure PathObj where
  /-- left end -/
  l : C
  /-- right end -/
  r : C
  /-- middle object -/
  c : C
  /-- left leg -/
  il : l ⟶ c
  /-- right leg -/
  ir : r ⟶ c
  cofibrant : IsCofibrantPair il ir
  il_mem : weakEquivalences C il
  ir_mem : weakEquivalences C ir

variable {C}

/-- Morphisms of `C^eq`: natural transformations of cospans. -/
@[ext]
structure PathObj.Hom (X Y : PathObj C) where
  /-- component at the left end -/
  l : X.l ⟶ Y.l
  /-- component at the right end -/
  r : X.r ⟶ Y.r
  /-- component at the middle -/
  c : X.c ⟶ Y.c
  il_c : X.il ≫ c = l ≫ Y.il
  ir_c : X.ir ≫ c = r ≫ Y.ir

attribute [reassoc] PathObj.Hom.il_c PathObj.Hom.ir_c

instance : Category.{v} (PathObj C) where
  Hom := PathObj.Hom
  id X := ⟨𝟙 _, 𝟙 _, 𝟙 _, by simp, by simp⟩
  comp f g := ⟨f.l ≫ g.l, f.r ≫ g.r, f.c ≫ g.c, by simp [f.il_c_assoc, g.il_c],
    by simp [f.ir_c_assoc, g.ir_c]⟩

/-- Reedy cofibrations of `C^eq` (H:2391, Prop 4.2.7): both ends are cofibrations, and the relative
latching map `(X_c ⊔_{X_l} Y_l) ⊔_{X_r} Y_r ⟶ Y_c` is a cofibration. -/
instance : CategoryWithCofibrations (PathObj C) :=
  ⟨fun X Y f => cofibrations C f.l ∧ cofibrations C f.r ∧
    ∃ (P : C) (k : X.c ⟶ P) (j : Y.l ⟶ P) (_ : IsPushout X.il f.l k j) (m : P ⟶ Y.c),
      k ≫ m = f.c ∧ j ≫ m = Y.il ∧ IsCofibrantGluing (X.ir ≫ k) f.r m Y.ir⟩

/-- Weak equivalences of `C^eq`: levelwise weak equivalences. -/
instance : CategoryWithWeakEquivalences (PathObj C) :=
  ⟨fun _ _ f => weakEquivalences C f.l ∧ weakEquivalences C f.r ∧ weakEquivalences C f.c⟩

variable (C) in
/-- The projection `C^eq ⥤ C × C` to the two ends (H:2519). -/
@[simps]
def PathObj.proj : PathObj C ⥤ C × C where
  obj X := (X.l, X.r)
  map f := (f.l, f.r)

variable (C) in
/-- The left end `C^eq ⥤ C`. -/
@[simps!]
def PathObj.left : PathObj C ⥤ C := PathObj.proj C ⋙ CategoryTheory.Prod.fst C C

variable (C) in
/-- The right end `C^eq ⥤ C`. -/
@[simps!]
def PathObj.right : PathObj C ⥤ C := PathObj.proj C ⋙ CategoryTheory.Prod.snd C C

end Path

/-! ### The homotopy slice `C^X` -/

section Slice

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]

variable (X : C) in
/-- Objects of the homotopy slice `C^X` (H:2627, Prop 4.4.1): triples `(A₀, A_f, A₀ ⊔ X ↪ A_f)`
whose restriction `X ⟶ A_f` is a trivial cofibration. -/
structure SliceObj where
  /-- the underlying object -/
  A₀ : C
  /-- the replacement of the map to `X` -/
  Af : C
  /-- the structure map from `A₀` -/
  a : A₀ ⟶ Af
  /-- the structure map from `X` -/
  x : X ⟶ Af
  cofibrant : IsCofibrantPair a x
  x_cofibration : cofibrations C x
  x_weakEquivalence : weakEquivalences C x

variable {X : C}

/-- Morphisms of `C^X`: pairs `(v₀, v_f)` compatible with the structure maps (and the identity of
`X`). -/
@[ext]
structure SliceObj.Hom (A B : SliceObj X) where
  /-- component on the underlying objects -/
  v₀ : A.A₀ ⟶ B.A₀
  /-- component on the replacements -/
  vf : A.Af ⟶ B.Af
  a_vf : A.a ≫ vf = v₀ ≫ B.a
  x_vf : A.x ≫ vf = B.x

attribute [reassoc] SliceObj.Hom.a_vf

instance : Category.{v} (SliceObj X) where
  Hom := SliceObj.Hom
  id A := ⟨𝟙 _, 𝟙 _, by simp, by simp⟩
  comp f g := ⟨f.v₀ ≫ g.v₀, f.vf ≫ g.vf, by simp [f.a_vf_assoc, g.a_vf],
    by rw [← Category.assoc, f.x_vf, g.x_vf]⟩

/-- Reedy cofibrations of `C^X` (H:2639): `v₀` is a cofibration and so is `B₀ ⊔_{A₀} A_f ⟶ B_f`. -/
instance : CategoryWithCofibrations (SliceObj X) :=
  ⟨fun A B f => cofibrations C f.v₀ ∧ IsCofibrantGluing A.a f.v₀ f.vf B.a⟩

/-- Weak equivalences of `C^X` (H:2637): `v₀` is a weak equivalence. -/
instance : CategoryWithWeakEquivalences (SliceObj X) :=
  ⟨fun _ _ f => weakEquivalences C f.v₀⟩

variable (X) in
/-- The forgetful morphism `C^X ⥤ C`, `A ↦ A₀` (H:2645). -/
@[simps]
def SliceObj.forget : SliceObj X ⥤ C where
  obj A := A.A₀
  map f := f.v₀

end Slice

end HomotopyHypothesis.Henry
