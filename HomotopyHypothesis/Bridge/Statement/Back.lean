import HomotopyHypothesis.Bridge.Statement.Equivalence
import HomotopyHypothesis.Bridge.Statement.Shapes
import HomotopyHypothesis.Bridge.Statement.Theory
import HomotopyHypothesis.Challenge
/-!
# Coherators transport

Theories on OpenAI's shapes pull back to theories on the statement's shapes along a quasi-inverse
of the shape functor. Morphisms out of a transported theory correspond to morphisms into the
pulled-back theory, naturally; hence free extensions and colimits of towers, and therefore
cellular presentations and coherators, transport.
-/

noncomputable section

namespace HomotopyHypothesis.Bridge.Statement

open CategoryTheory CategoryTheory.Limits

universe v

/-! ### A quasi-inverse of the shape functor -/

theorem shapeToOAI_shapeOfOAI (S : OAI.Grothendieck.Shape) : shapeToOAI (shapeOfOAI S) = S := by
  obtain ⟨n, T⟩ := S
  change (⟨n, tableToOAI (tableOfOAI T)⟩ : OAI.Grothendieck.Shape) = ⟨n, T⟩
  rw [tableToOAI_tableOfOAI]

theorem height_tableToOAI {n : ℕ} (T : Grothendieck.Table n) :
    (tableToOAI T).height = T.height := by
  induction T with
  | globe => rfl
  | attach T b h hl hr ih =>
    change max (tableToOAI T).height h = max T.height h
    rw [ih]

theorem eqToHom_self {A : Type*} [Category A] {X : A} (p : X = X) : eqToHom p = 𝟙 X := rfl

theorem eS (S : Grothendieck.Shape) : shapeFunctor.obj (shapeToOAI S) = S :=
  shapeOfOAI_shapeToOAI S

/-- The statement's shapes to OpenAI's: the preimage of the conjugated map. -/
def shapeBack : Grothendieck.Shape ⥤ OAI.Grothendieck.Shape where
  obj := shapeToOAI
  map {S T} f := shapeFunctorFullyFaithful.preimage
    (eqToHom (eS S) ≫ f ≫ eqToHom (eS T).symm)
  map_id S := shapeFunctorFullyFaithful.map_injective (by
    rw [Functor.FullyFaithful.map_preimage, CategoryTheory.Functor.map_id, Category.id_comp,
      eqToHom_trans, eqToHom_refl])
  map_comp {R S T} f g := shapeFunctorFullyFaithful.map_injective (by
    rw [CategoryTheory.Functor.map_comp, Functor.FullyFaithful.map_preimage,
      Functor.FullyFaithful.map_preimage, Functor.FullyFaithful.map_preimage]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp])

theorem fS (S : OAI.Grothendieck.Shape) : shapeBack.obj (shapeFunctor.obj S) = S :=
  shapeToOAI_shapeOfOAI S

theorem shapeFunctor_map_shapeBack {S T : Grothendieck.Shape} (f : S ⟶ T) :
    shapeFunctor.map (shapeBack.map f) = eqToHom (eS S) ≫ f ≫ eqToHom (eS T).symm :=
  shapeFunctorFullyFaithful.map_preimage _

theorem shapeBack_map_shapeFunctor {S T : OAI.Grothendieck.Shape} (g : S ⟶ T) :
    shapeBack.map (shapeFunctor.map g) = eqToHom (fS S) ≫ g ≫ eqToHom (fS T).symm := by
  apply shapeFunctorFullyFaithful.map_injective
  simp only [shapeFunctor_map_shapeBack, CategoryTheory.Functor.map_comp, eqToHom_map]
  try rfl

theorem shapeBack_face {m n : ℕ} (h : m < n) (b : Bool) :
    shapeBack.map (Grothendieck.Shape.face h b) = OAI.Grothendieck.Shape.face h b := by
  apply shapeFunctorFullyFaithful.map_injective
  exact (shapeFunctor_map_shapeBack _).trans
    (((Category.id_comp _).trans (Category.comp_id _)).trans (shapeFunctor_face h b).symm)

/-! ### Pulling theories back -/

/-- A theory on OpenAI's shapes as a theory on the statement's shapes. -/
abbrev theoryDataOfOAI (D : OAI.Grothendieck.TheoryData.{v}) :
    Grothendieck.TheoryData.{v} where
  Hom S T := D.Hom (shapeToOAI S) (shapeToOAI T)
  id S := D.id _
  comp f g := D.comp f g
  id_comp f := D.id_comp f
  comp_id f := D.comp_id f
  assoc f g h := D.assoc f g h
  base f := D.base (shapeBack.map f)
  base_id S := by rw [shapeBack.map_id]; exact D.base_id _
  base_comp f g := by rw [shapeBack.map_comp]; exact D.base_comp _ _

/-- The underlying categories: identity on hom-types. -/
def objFunctorBack (D : OAI.Grothendieck.TheoryData.{v}) :
    (theoryDataOfOAI D).Obj ⥤ D.Obj where
  obj S := ⟨shapeToOAI S.shape⟩
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

instance (D : OAI.Grothendieck.TheoryData.{v}) : (objFunctorBack D).Full where
  map_surjective f := ⟨f, rfl⟩

instance (D : OAI.Grothendieck.TheoryData.{v}) : (objFunctorBack D).Faithful where
  map_injective h := h

/-- A globular theory on OpenAI's shapes as a globular theory on the statement's shapes. -/
abbrev theoryOfOAI (D : OAI.Grothendieck.GlobularTheory.{v}) :
    Grothendieck.GlobularTheory.{v} where
  toTheoryData := theoryDataOfOAI D.toTheoryData
  sums S b h hl hr := by
    obtain ⟨S', rfl⟩ : ∃ S', shapeOfOAI S' = S := ⟨shapeToOAI S, shapeOfOAI_shapeToOAI S⟩
    let e : ∀ X : OAI.Grothendieck.Shape,
        D.arity.obj X ≅ D.arity.obj (shapeBack.obj (shapeFunctor.obj X)) :=
      fun X => D.arity.mapIso (eqToIso (fS X).symm)
    have key : ∀ {X Y : OAI.Grothendieck.Shape} (g : X ⟶ Y),
        D.arity.map g ≫ (e Y).hom = (e X).hom ≫ D.arity.map (shapeBack.map (shapeFunctor.map g)) := by
      intro X Y g
      simp only [e, Functor.mapIso_hom, eqToIso.hom, shapeBack_map_shapeFunctor,
        ← CategoryTheory.Functor.map_comp, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    have H := (D.sums S' b h hl hr).of_iso (e _) (e _) (e _) (e _)
      (key _) (key _) (key _) (key _)
      (f' := D.arity.map (shapeBack.map (shapeFunctor.map (S'.seam hl))))
      (g' := D.arity.map (shapeBack.map (shapeFunctor.map (OAI.Grothendieck.Shape.face hr false))))
      (inl' := D.arity.map (shapeBack.map (shapeFunctor.map (S'.inl b h hl hr))))
      (inr' := D.arity.map (shapeBack.map (shapeFunctor.map (S'.inr b h hl hr))))
    rw [shapeFunctor_inl S' b h hl hr, shapeFunctor_inr S' b h hl hr, shapeFunctor_seam S' hl,
      shapeFunctor_face hr false] at H
    exact IsPushout.of_map_of_faithful (F := objFunctorBack D.toTheoryData) H

/-! ### Morphisms -/

/-- Morphisms of theories transport. -/
def morphToOAI {A B : Grothendieck.GlobularTheory.{v}} (f : Grothendieck.GlobularTheory.Morphism A B) :
    OAI.Grothendieck.GlobularTheory.Morphism (theoryToOAI A) (theoryToOAI B) where
  map x := f.map x
  map_id _ := f.map_id _
  map_comp x y := f.map_comp x y
  map_base _ := f.map_base _

theorem morphToOAI_comp {A B E : Grothendieck.GlobularTheory.{v}}
    (f : Grothendieck.GlobularTheory.Morphism A B) (g : Grothendieck.GlobularTheory.Morphism B E) :
    morphToOAI (f.comp g) = (morphToOAI f).comp (morphToOAI g) := rfl

/-- Conjugation by equalities of shapes, inside a theory. -/
def conj (A : Grothendieck.TheoryData.{v}) {S S' T T' : Grothendieck.Shape} (p : S' = S)
    (q : T' = T) (x : A.Hom S T) : A.Hom S' T' :=
  A.comp (A.base (eqToHom p)) (A.comp x (A.base (eqToHom q.symm)))

/-- Conjugation by equalities of shapes, inside an OpenAI theory. -/
def conj' (A : OAI.Grothendieck.TheoryData.{v}) {S S' T T' : OAI.Grothendieck.Shape} (p : S' = S)
    (q : T' = T) (x : A.Hom S T) : A.Hom S' T' :=
  A.comp (A.base (eqToHom p)) (A.comp x (A.base (eqToHom q.symm)))

section ConjAlgebra

variable (A : Grothendieck.TheoryData.{v})

theorem base_eqToHom_trans {X Y Z : Grothendieck.Shape} (p : X = Y) (q : Y = Z) :
    A.comp (A.base (eqToHom p)) (A.base (eqToHom q)) = A.base (eqToHom (p.trans q)) := by
  rw [← A.base_comp, eqToHom_trans]

theorem base_eqToHom_self {X : Grothendieck.Shape} (p : X = X) :
    A.base (eqToHom p) = A.id X := by
  rw [eqToHom_self, A.base_id]

theorem base_eqToHom_cancel {X Y Z : Grothendieck.Shape} (p : X = Y) (w : A.Hom Y Z) :
    A.comp (A.base (eqToHom p.symm)) (A.comp (A.base (eqToHom p)) w) = w := by
  rw [← A.assoc, base_eqToHom_trans, base_eqToHom_self, A.id_comp]

theorem conj_comp {S S' T T' U U' : Grothendieck.Shape} (p : S' = S) (q : T' = T) (r : U' = U)
    (x : A.Hom S T) (y : A.Hom T U) :
    conj A p r (A.comp x y) = A.comp (conj A p q x) (conj A q r y) := by
  simp only [conj, A.assoc, base_eqToHom_cancel]

theorem conj_id {S S' : Grothendieck.Shape} (p : S' = S) : conj A p p (A.id S) = A.id S' := by
  simp only [conj, A.id_comp, base_eqToHom_trans, base_eqToHom_self]

theorem conj_base {S S' T T' : Grothendieck.Shape} (p : S' = S) (q : T' = T) (f : S ⟶ T) :
    conj A p q (A.base f) = A.base (eqToHom p ≫ f ≫ eqToHom q.symm) := by
  simp only [conj, A.base_comp]

end ConjAlgebra

section ConjAlgebra'

variable (A : OAI.Grothendieck.TheoryData.{v})

theorem base_eqToHom_trans' {X Y Z : OAI.Grothendieck.Shape} (p : X = Y) (q : Y = Z) :
    A.comp (A.base (eqToHom p)) (A.base (eqToHom q)) = A.base (eqToHom (p.trans q)) := by
  rw [← A.base_comp, eqToHom_trans]

theorem base_eqToHom_self' {X : OAI.Grothendieck.Shape} (p : X = X) :
    A.base (eqToHom p) = A.id X := by
  rw [eqToHom_self, A.base_id]

theorem base_eqToHom_cancel' {X Y Z : OAI.Grothendieck.Shape} (p : X = Y) (w : A.Hom Y Z) :
    A.comp (A.base (eqToHom p.symm)) (A.comp (A.base (eqToHom p)) w) = w := by
  rw [← A.assoc, base_eqToHom_trans', base_eqToHom_self', A.id_comp]

theorem conj'_comp {S S' T T' U U' : OAI.Grothendieck.Shape} (p : S' = S) (q : T' = T)
    (r : U' = U) (x : A.Hom S T) (y : A.Hom T U) :
    conj' A p r (A.comp x y) = A.comp (conj' A p q x) (conj' A q r y) := by
  simp only [conj', A.assoc, base_eqToHom_cancel']

theorem conj'_id {S S' : OAI.Grothendieck.Shape} (p : S' = S) :
    conj' A p p (A.id S) = A.id S' := by
  simp only [conj', A.id_comp, base_eqToHom_trans', base_eqToHom_self']

theorem conj'_base {S S' T T' : OAI.Grothendieck.Shape} (p : S' = S) (q : T' = T) (f : S ⟶ T) :
    conj' A p q (A.base f) = A.base (eqToHom p ≫ f ≫ eqToHom q.symm) := by
  simp only [conj', A.base_comp]

theorem conj'_cancel_gen {X₀ X₁ Y₀ Y₁ : OAI.Grothendieck.Shape} (a : X₀ = X₁) (b : X₁ = X₀)
    (c : Y₀ = Y₁) (d : Y₁ = Y₀) (w : A.Hom X₀ Y₀) :
    A.comp (A.base (eqToHom a)) (A.comp (A.comp (A.base (eqToHom b))
      (A.comp w (A.base (eqToHom c)))) (A.base (eqToHom d))) = w := by
  subst a
  subst c
  simp only [eqToHom_refl, A.base_id, A.id_comp, A.comp_id]

end ConjAlgebra'

theorem map_conj {A B : Grothendieck.GlobularTheory.{v}}
    (f : Grothendieck.GlobularTheory.Morphism A B) {S S' T T' : Grothendieck.Shape}
    (p : S' = S) (q : T' = T) (x : A.Hom S T) :
    f.map (conj A.toTheoryData p q x) = conj B.toTheoryData p q (f.map x) := by
  simp only [conj, f.map_comp, f.map_base]

/-! ### Morphisms out of a transported theory -/

section HomEquiv

variable {A : Grothendieck.GlobularTheory.{v}} {E : OAI.Grothendieck.GlobularTheory.{v}}

/-- A morphism out of a transported theory as a morphism into a pulled-back theory. -/
def homTo (m : OAI.Grothendieck.GlobularTheory.Morphism (theoryToOAI A) E) :
    Grothendieck.GlobularTheory.Morphism A (theoryOfOAI E) where
  map {S T} x := m.map (@conj A.toTheoryData S (shapeFunctor.obj (shapeToOAI S)) T
    (shapeFunctor.obj (shapeToOAI T)) (eS S) (eS T) x)
  map_id S := (congrArg m.map (conj_id A.toTheoryData (eS S))).trans (m.map_id _)
  map_comp {R S T} x y :=
    (congrArg m.map (conj_comp A.toTheoryData (eS R) (eS S) (eS T) x y)).trans
      (m.map_comp _ _)
  map_base {S T} f :=
    (congrArg m.map ((conj_base A.toTheoryData (eS S) (eS T) f).trans
      (congrArg A.base (shapeFunctor_map_shapeBack f).symm))).trans (m.map_base _)

/-- A morphism into a pulled-back theory as a morphism out of a transported theory. -/
def homFrom (n : Grothendieck.GlobularTheory.Morphism A (theoryOfOAI E)) :
    OAI.Grothendieck.GlobularTheory.Morphism (theoryToOAI A) E where
  map {S T} y := @conj' E.toTheoryData (shapeBack.obj (shapeFunctor.obj S)) S
    (shapeBack.obj (shapeFunctor.obj T)) T (fS S).symm (fS T).symm (n.map y)
  map_id S :=
    (congrArg (@conj' E.toTheoryData (shapeBack.obj (shapeFunctor.obj S)) S
      (shapeBack.obj (shapeFunctor.obj S)) S (fS S).symm (fS S).symm) (n.map_id _)).trans
      (conj'_id _ _)
  map_comp {R S T} x y :=
    (congrArg (@conj' E.toTheoryData (shapeBack.obj (shapeFunctor.obj R)) R
      (shapeBack.obj (shapeFunctor.obj T)) T (fS R).symm (fS T).symm) (n.map_comp x y)).trans
      (conj'_comp E.toTheoryData (fS R).symm (fS S).symm (fS T).symm _ _)
  map_base {S T} g :=
    (congrArg (@conj' E.toTheoryData (shapeBack.obj (shapeFunctor.obj S)) S
      (shapeBack.obj (shapeFunctor.obj T)) T (fS S).symm (fS T).symm)
      ((n.map_base (shapeFunctor.map g)).trans
        (congrArg E.base (shapeBack_map_shapeFunctor g)))).trans
      ((conj'_base _ _ _ _).trans (congrArg E.base (by simp)))

theorem homFrom_homTo (m : OAI.Grothendieck.GlobularTheory.Morphism (theoryToOAI A) E) :
    homFrom (homTo m) = m := by
  ext S T y
  have h : conj A.toTheoryData (eS (shapeFunctor.obj S)) (eS (shapeFunctor.obj T)) y =
      (theoryToOAI A).comp ((theoryToOAI A).base (eqToHom (fS S)))
        ((theoryToOAI A).comp y ((theoryToOAI A).base (eqToHom (fS T).symm))) := by
    unfold conj
    simp only [eqToHom_map]
    rfl
  have h2 : m.map (conj A.toTheoryData (eS (shapeFunctor.obj S)) (eS (shapeFunctor.obj T)) y) =
      E.comp (E.base (eqToHom (fS S))) (E.comp (m.map y) (E.base (eqToHom (fS T).symm))) :=
    (congrArg m.map h).trans ((m.map_comp _ _).trans (congrArg₂ E.comp (m.map_base _)
      ((m.map_comp _ _).trans (congrArg (E.comp (m.map y)) (m.map_base _)))))
  exact (congrArg (conj' E.toTheoryData (fS S).symm (fS T).symm) h2).trans
    (conj'_cancel_gen E.toTheoryData _ _ _ _ _)

theorem homTo_homFrom (n : Grothendieck.GlobularTheory.Morphism A (theoryOfOAI E)) :
    homTo (homFrom n) = n := by
  ext S T x
  dsimp only [homFrom, homTo]
  rw [conj, n.map_comp, n.map_comp, n.map_base, n.map_base]
  simp only [eqToHom_map]
  exact conj'_cancel_gen E.toTheoryData _ _ _ _ _

/-- The natural bijection of morphisms. -/
def homEquiv : OAI.Grothendieck.GlobularTheory.Morphism (theoryToOAI A) E ≃
    Grothendieck.GlobularTheory.Morphism A (theoryOfOAI E) where
  toFun := homTo
  invFun := homFrom
  left_inv := homFrom_homTo
  right_inv := homTo_homFrom

end HomEquiv

theorem homEquiv_comp {A B : Grothendieck.GlobularTheory.{v}} {E : OAI.Grothendieck.GlobularTheory.{v}}
    (f : Grothendieck.GlobularTheory.Morphism A B)
    (m : OAI.Grothendieck.GlobularTheory.Morphism (theoryToOAI B) E) :
    homEquiv ((morphToOAI f).comp m) = f.comp (homEquiv m) := by
  ext S T x
  exact congrArg m.map (map_conj f (eS S) (eS T) x)

end HomotopyHypothesis.Bridge.Statement
