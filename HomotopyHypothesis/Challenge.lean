import Mathlib

/-!
# The Grothendieck homotopy hypothesis for coherators

Grothendieck's conjecture, in the precise form of Maltsiniotis and Ara
(D. Ara, "On the homotopy theory of Grothendieck ∞-groupoids", arXiv:1206.2941, final
conjecture): for every coherator `C`, the fundamental ∞-groupoid functor
`Π_∞ : Top → ∞-Gpd_C` sends weak homotopy equivalences to weak equivalences, and the induced
functor `Hot = Top[W⁻¹] → Ho(∞-Gpd_C)` is an equivalence of categories.

## Vocabulary

The first part of this file (globular sets, the globe category, globular sums, globular
theories, coherators, models and their weak equivalences) is copied verbatim from OpenAI's
Comparator challenge `ComparatorChallenges/GrothendieckElementaryExpansion.lean` in the
`openai/math` repository, licensed under the Apache License, Version 2.0. Changes: the
enclosing namespace `OAI` is renamed `HomotopyHypothesis`, and the challenge theorem
`elementary_expansion` (with its `open` line) is omitted.

In that vocabulary a coherator is Ara's: a globular theory obtained from `Θ₀` by an
`ℕ`-indexed tower of free extensions adding fillers of admissible pairs `Dₙ ⇉ S` with
`dim S ≤ n + 1`, in which every admissible pair has a filler. A model (`C.Model`) is a
presheaf on `C` sending globular sums to limits, i.e. an ∞-groupoid of type `C`, and
`Model.WeakEquivalence` is Ara's weak equivalence: a bijection on `π₀` and on every `πₙ` at
every base point.

## New definitions

* `topGlobes`: Ara's globular extension of `Top`: the `n`-globe is the closed unit ball of `ℝⁿ`
  (Mathlib's `TopCat.disk`), the source and target of `Bⁿ⁺¹` are the upper and lower
  hemispheres `x ↦ (x, ±√(1 - ‖x‖²))`, and an iterated face lands on the equator.
* `TopRealization C`: a globular functor `C → Top` in Ara's sense: a functor whose restriction
  to the globes is (isomorphic to) `topGlobes` and which sends the globular sums of `C` to
  pushouts of spaces.
* `fundamentalGroupoidFunctor R : TopCat ⥤ C.Model`: Ara's `Π_{C,F}`,
  `X ↦ (S ↦ Hom(F S, X))`.
* `weakHomotopyEquivalences`: continuous maps inducing a bijection on path components and on
  every homotopy group `πₙ₊₁(X, x) → πₙ₊₁(Y, f x)` at every base point.
* `Statement`: for every coherator, a realization exists, and every realization's `Π_∞` sends
  weak homotopy equivalences to weak equivalences and exhibits `Ho(∞-Gpd_C)` as the
  localization of `Top` at the weak homotopy equivalences.
-/

namespace HomotopyHypothesis

universe u v w

namespace Grothendieck

structure GlobularSet where
  Cell : ℕ → Type u
  source : ∀ n, Cell (n + 1) → Cell n
  target : ∀ n, Cell (n + 1) → Cell n
  source_source : ∀ n x, source n (source (n + 1) x) = source n (target (n + 1) x)
  target_source : ∀ n x, target n (source (n + 1) x) = target n (target (n + 1) x)

namespace GlobularSet

@[ext]
structure Hom (X Y : GlobularSet.{u}) where
  app : ∀ n, X.Cell n → Y.Cell n
  source_app : ∀ n x, app n (X.source n x) = Y.source n (app (n + 1) x)
  target_app : ∀ n x, app n (X.target n x) = Y.target n (app (n + 1) x)

def Parallel (X : GlobularSet.{u}) : ∀ n, X.Cell n → X.Cell n → Prop
  | 0, _, _ => True
  | n + 1, x, y => X.source n x = X.source n y ∧ X.target n x = X.target n y

def Joined (X : GlobularSet.{u}) (n : ℕ) (x y : X.Cell n) : Prop :=
  ∃ h : X.Cell (n + 1), X.source n h = x ∧ X.target n h = y

def Boundary (X : GlobularSet.{u}) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => { p : X.Cell n × X.Cell n // X.Parallel n p.1 p.2 }

def boundary (X : GlobularSet.{u}) : ∀ n, X.Cell n → X.Boundary n
  | 0, _ => PUnit.unit
  | n + 1, x => ⟨(X.source n x, X.target n x), by
      cases n with
      | zero => trivial
      | succ n => exact ⟨X.source_source n x, X.target_source n x⟩⟩

def Hom.boundaryMap {X Y : GlobularSet.{u}} (f : Hom X Y) : ∀ n, X.Boundary n → Y.Boundary n
  | 0, _ => PUnit.unit
  | n + 1, b => ⟨(f.app n b.1.1, f.app n b.1.2), by
      cases n with
      | zero => trivial
      | succ n =>
        exact ⟨by rw [← f.source_app, ← f.source_app, b.2.1],
          by rw [← f.target_app, ← f.target_app, b.2.2]⟩⟩

end GlobularSet

open CategoryTheory CategoryTheory.Limits Opposite

@[ext]
structure Globe where
  dim : ℕ

namespace Globe

inductive Face : ℕ → ℕ → Type
  | id (n : ℕ) : Face n n
  | face {m n : ℕ} (lt : m < n) (side : Bool) : Face m n

namespace Face

def comp {m n k : ℕ} : Face m n → Face n k → Face m k
  | .id _, g => g
  | .face h b, .id _ => .face h b
  | .face h b, .face h' _ => .face (h.trans h') b

end Face

instance : Category Globe where
  Hom m n := Face m.dim n.dim
  id m := .id m.dim
  comp := Face.comp
  id_comp _ := rfl
  comp_id {X Y} f := by cases X; cases Y; cases f <;> rfl
  assoc {W X Y Z} f g h := by
    cases W; cases X; cases Y; cases Z
    cases f <;> cases g <;> cases h <;> rfl

def face {m n : ℕ} (h : m < n) (side : Bool) : Globe.mk m ⟶ Globe.mk n :=
  Face.face h side

def source (n : ℕ) : Globe.mk n ⟶ Globe.mk (n + 1) := face (Nat.lt_succ_self n) false

def target (n : ℕ) : Globe.mk n ⟶ Globe.mk (n + 1) := face (Nat.lt_succ_self n) true

end Globe

abbrev GlobularPresheaf := Globeᵒᵖ ⥤ Type u

namespace GlobularPresheaf

def underlying (X : GlobularPresheaf.{u}) : GlobularSet.{u} where
  Cell n := X.obj (op (Globe.mk n))
  source n := X.map (Globe.source n).op
  target n := X.map (Globe.target n).op
  source_source n x := by
    have h := congrArg (fun f => X.map f) (congrArg Quiver.Hom.op (show Globe.source n ≫ Globe.source (n + 1) = Globe.source n ≫ Globe.target (n + 1) from rfl))
    simpa only [op_comp, X.map_comp, types_comp_apply] using ConcreteCategory.congr_hom h x
  target_source n x := by
    have h := congrArg (fun f => X.map f) (congrArg Quiver.Hom.op (show Globe.target n ≫ Globe.source (n + 1) = Globe.target n ≫ Globe.target (n + 1) from rfl))
    simpa only [op_comp, X.map_comp, types_comp_apply] using ConcreteCategory.congr_hom h x

def underlyingMap {X Y : GlobularPresheaf.{u}} (f : X ⟶ Y) : X.underlying.Hom Y.underlying where
  app n := f.app (op (Globe.mk n))
  source_app n x := by
    exact ConcreteCategory.congr_hom (f.naturality (Globe.source n).op) x
  target_app n x := by
    exact ConcreteCategory.congr_hom (f.naturality (Globe.target n).op) x

def disk (n : ℕ) : GlobularPresheaf.{u} := uliftYoneda.{u}.obj (Globe.mk n)

def face {m n : ℕ} (h : m < n) (side : Bool) : disk.{u} m ⟶ disk.{u} n :=
  uliftYoneda.{u}.map (Globe.face h side)

end GlobularPresheaf

inductive Table : ℕ → Type
  | globe (n : ℕ) : Table n
  | attach {last : ℕ} (T : Table last) (b h : ℕ) (left : b < last) (right : b < h) : Table h

namespace Table

def height : {n : ℕ} → Table n → ℕ
  | _, .globe n => n
  | _, .attach T _ h _ _ => max T.height h

noncomputable def realizeWithLast : {n : ℕ} → Table n →
    (Σ X : GlobularPresheaf.{0}, GlobularPresheaf.disk n ⟶ X)
  | _, .globe n => ⟨GlobularPresheaf.disk n, 𝟙 _⟩
  | _, .attach T _ h hl hr =>
    let prev := T.realizeWithLast
    let f := GlobularPresheaf.face hl true ≫ prev.2
    let g := GlobularPresheaf.face hr false
    ⟨pushout f g, pushout.inr f g⟩

noncomputable def realize {n} (T : Table n) : GlobularPresheaf.{0} := T.realizeWithLast.1

noncomputable def lastInclusion {n} (T : Table n) : GlobularPresheaf.disk n ⟶ T.realize :=
  T.realizeWithLast.2

end Table

abbrev Shape := Σ n, Table n

namespace Shape

noncomputable def realize (S : Shape) : GlobularPresheaf.{0} := S.2.realize

def height (S : Shape) : ℕ := S.2.height

def globe (n : ℕ) : Shape := ⟨n, Table.globe n⟩

noncomputable instance : Category Shape where
  Hom S T := S.realize ⟶ T.realize
  id S := 𝟙 S.realize
  comp f g := f ≫ g
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

noncomputable def face {m n : ℕ} (h : m < n) (side : Bool) : globe m ⟶ globe n :=
  GlobularPresheaf.face h side

noncomputable def source (n : ℕ) : globe n ⟶ globe (n + 1) := face (Nat.lt_succ_self n) false

noncomputable def target (n : ℕ) : globe n ⟶ globe (n + 1) := face (Nat.lt_succ_self n) true

def attach (S : Shape) (b h : ℕ) (hl : b < S.1) (hr : b < h) : Shape :=
  ⟨h, Table.attach S.2 b h hl hr⟩

noncomputable def seam (S : Shape) {b : ℕ} (hl : b < S.1) : globe b ⟶ S :=
  show GlobularPresheaf.disk b ⟶ S.realize from
    GlobularPresheaf.face hl true ≫ S.2.lastInclusion

noncomputable def inl (S : Shape) (b h : ℕ) (hl : b < S.1) (hr : b < h) :
    S ⟶ S.attach b h hl hr :=
  pushout.inl (GlobularPresheaf.face hl true ≫ S.2.lastInclusion)
    (GlobularPresheaf.face hr false)

noncomputable def inr (S : Shape) (b h : ℕ) (hl : b < S.1) (hr : b < h) :
    globe h ⟶ S.attach b h hl hr :=
  pushout.inr (GlobularPresheaf.face hl true ≫ S.2.lastInclusion)
    (GlobularPresheaf.face hr false)

end Shape

structure TheoryData where
  Hom : Shape → Shape → Type v
  id : ∀ S, Hom S S
  comp : ∀ {S T U}, Hom S T → Hom T U → Hom S U
  id_comp : ∀ {S T} (f : Hom S T), comp (id S) f = f
  comp_id : ∀ {S T} (f : Hom S T), comp f (id T) = f
  assoc : ∀ {R S T U} (f : Hom R S) (g : Hom S T) (h : Hom T U),
    comp (comp f g) h = comp f (comp g h)
  base : ∀ {S T}, (S ⟶ T) → Hom S T
  base_id : ∀ S, base (𝟙 S) = id S
  base_comp : ∀ {R S T} (f : R ⟶ S) (g : S ⟶ T), base (f ≫ g) = comp (base f) (base g)

namespace TheoryData

structure Obj (C : TheoryData.{v}) where
  shape : Shape

instance (C : TheoryData.{v}) : Category C.Obj where
  Hom S T := C.Hom S.shape T.shape
  id S := C.id S.shape
  comp f g := C.comp f g
  id_comp := C.id_comp
  comp_id := C.comp_id
  assoc := C.assoc

noncomputable def arity (C : TheoryData.{v}) : Shape ⥤ C.Obj where
  obj S := ⟨S⟩
  map f := C.base f
  map_id := C.base_id
  map_comp := C.base_comp

def PreservesGlobularSums (C : TheoryData.{v}) : Prop :=
  ∀ (S : Shape) (b h : ℕ) (hl : b < S.1) (hr : b < h),
    IsPushout (C.arity.map (S.seam hl)) (C.arity.map (Shape.face hr false))
      (C.arity.map (S.inl b h hl hr)) (C.arity.map (S.inr b h hl hr))

end TheoryData

structure GlobularTheory extends TheoryData.{v} where
  sums : toTheoryData.PreservesGlobularSums

namespace GlobularTheory

abbrev Obj (C : GlobularTheory.{v}) := C.toTheoryData.Obj

@[ext]
structure Morphism (C D : GlobularTheory.{v}) where
  map : ∀ {S T}, C.Hom S T → D.Hom S T
  map_id : ∀ S, map (C.id S) = D.id S
  map_comp : ∀ {R S T} (f : C.Hom R S) (g : C.Hom S T),
    map (C.comp f g) = D.comp (map f) (map g)
  map_base : ∀ {S T} (f : S ⟶ T), map (C.base f) = D.base f

namespace Morphism

def id (C : GlobularTheory.{v}) : Morphism C C where
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl
  map_base _ := rfl

def comp {C D E : GlobularTheory.{v}} (f : Morphism C D) (g : Morphism D E) : Morphism C E where
  map a := g.map (f.map a)
  map_id S := by rw [f.map_id, g.map_id]
  map_comp a b := by rw [f.map_comp, g.map_comp]
  map_base a := by rw [f.map_base, g.map_base]

end Morphism

def Parallel (C : GlobularTheory.{v}) {S : Shape} :
    ∀ n, C.Hom (Shape.globe n) S → C.Hom (Shape.globe n) S → Prop
  | 0, _, _ => True
  | n + 1, f, g =>
    C.comp (C.base (Shape.source n)) f = C.comp (C.base (Shape.source n)) g ∧
    C.comp (C.base (Shape.target n)) f = C.comp (C.base (Shape.target n)) g

structure AdmissiblePair (C : GlobularTheory.{v}) where
  n : ℕ
  arity : Shape
  height : arity.height ≤ n + 1
  source : C.Hom (Shape.globe n) arity
  target : C.Hom (Shape.globe n) arity
  parallel : C.Parallel n source target

def Fills {C D : GlobularTheory.{v}} (f : Morphism C D) (p : C.AdmissiblePair)
    (z : D.Hom (Shape.globe (p.n + 1)) p.arity) : Prop :=
  D.comp (D.base (Shape.source p.n)) z = f.map p.source ∧
  D.comp (D.base (Shape.target p.n)) z = f.map p.target

def IsFreeExtension {C D : GlobularTheory.{v}} (f : Morphism C D)
    (G : Type v) (pair : G → C.AdmissiblePair)
    (filler : ∀ g, D.Hom (Shape.globe ((pair g).n + 1)) (pair g).arity) : Prop :=
  (∀ g, Fills f (pair g) (filler g)) ∧
  ∀ (E : GlobularTheory.{v}) (a : Morphism C E)
    (chosen : ∀ g, E.Hom (Shape.globe ((pair g).n + 1)) (pair g).arity),
    (∀ g, Fills a (pair g) (chosen g)) →
    ∃! b : Morphism D E, f.comp b = a ∧ ∀ g, b.map (filler g) = chosen g

structure CellularPresentation (C : GlobularTheory.{v}) where
  stage : ℕ → GlobularTheory.{v}
  initial : ∀ D : GlobularTheory.{v}, Nonempty (Unique (Morphism (stage 0) D))
  step : ∀ r, Morphism (stage r) (stage (r + 1))
  generators : ℕ → Type v
  pair : ∀ r, generators r → (stage r).AdmissiblePair
  filler : ∀ r g, (stage (r + 1)).Hom (Shape.globe ((pair r g).n + 1)) (pair r g).arity
  free : ∀ r, IsFreeExtension (step r) (generators r) (pair r) (filler r)
  inclusion : ∀ r, Morphism (stage r) C
  compatible : ∀ r, (step r).comp (inclusion (r + 1)) = inclusion r
  colimit : ∀ (D : GlobularTheory.{v}) (a : ∀ r, Morphism (stage r) D),
    (∀ r, (step r).comp (a (r + 1)) = a r) →
    ∃! b : Morphism C D, ∀ r, (inclusion r).comp b = a r

def IsCoherator (C : GlobularTheory.{v}) : Prop :=
  Nonempty C.CellularPresentation ∧
  ∀ p : C.AdmissiblePair, ∃ z, Fills (Morphism.id C) p z

noncomputable def shapeGlobes : Globe ⥤ Shape where
  obj n := Shape.globe n.dim
  map f := uliftYoneda.map f
  map_id n := by exact uliftYoneda.map_id n
  map_comp f g := by exact uliftYoneda.map_comp f g

noncomputable def globes (C : GlobularTheory.{v}) : Globe ⥤ C.Obj :=
  shapeGlobes ⋙ C.toTheoryData.arity

structure Model (C : GlobularTheory.{v}) where
  presheaf : C.Objᵒᵖ ⥤ Type v
  sums : ∀ (S : Shape) (b h : ℕ) (hl : b < S.1) (hr : b < h),
    IsPullback
      (presheaf.map (C.toTheoryData.arity.map (S.inl b h hl hr)).op)
      (presheaf.map (C.toTheoryData.arity.map (S.inr b h hl hr)).op)
      (presheaf.map (C.toTheoryData.arity.map (S.seam hl)).op)
      (presheaf.map (C.toTheoryData.arity.map (Shape.face hr false)).op)

namespace Model

instance (C : GlobularTheory.{v}) : Category C.Model where
  Hom X Y := X.presheaf ⟶ Y.presheaf
  id X := 𝟙 X.presheaf
  comp f g := f ≫ g
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

noncomputable def underlying {C : GlobularTheory.{v}} (X : C.Model) : GlobularSet.{v} :=
  GlobularPresheaf.underlying (C.globes.op ⋙ X.presheaf)

noncomputable def underlyingMap {C : GlobularTheory.{v}} {X Y : C.Model} (f : X ⟶ Y) :
    X.underlying.Hom Y.underlying :=
  GlobularPresheaf.underlyingMap (Functor.whiskerLeft C.globes.op f)

noncomputable def freeShape (C : GlobularTheory.{v}) (S : Shape) : C.Model where
  presheaf := yoneda.obj ⟨S⟩
  sums T b h hl hr := ((C.sums T b h hl hr).op.map (yoneda.obj ⟨S⟩)).flip

noncomputable def disk (C : GlobularTheory.{v}) (n : ℕ) : C.Model :=
  freeShape C (Shape.globe n)

noncomputable def J (C : GlobularTheory.{v}) (n : ℕ) : disk C n ⟶ disk C (n + 1) :=
  show (disk C n).presheaf ⟶ (disk C (n + 1)).presheaf from
    yoneda.map (C.toTheoryData.arity.map (Shape.source n))

structure BoundaryAttachment {C : GlobularTheory.{v}} {X Y : C.Model} (f : X ⟶ Y) where
  index : Type v
  dimension : index → ℕ
  boundary : ∀ k, X.underlying.Boundary (dimension k)
  cell : ∀ k, Y.underlying.Cell (dimension k)
  cell_boundary : ∀ k, Y.underlying.boundary _ (cell k) =
    (underlyingMap f).boundaryMap _ (boundary k)
  universal : ∀ (Z : C.Model) (g : X ⟶ Z)
    (z : ∀ k, Z.underlying.Cell (dimension k)),
    (∀ k, Z.underlying.boundary _ (z k) = (underlyingMap g).boundaryMap _ (boundary k)) →
    ∃! h : Y ⟶ Z, f ≫ h = g ∧ ∀ k, (underlyingMap h).app _ (cell k) = z k

structure CellularPresentation {C : GlobularTheory.{v}} (X : C.Model) where
  order : Type v
  linearOrder : LinearOrder order
  orderBot : OrderBot order
  succOrder : SuccOrder order
  wellFoundedLT : WellFoundedLT order
  initial : C.Model
  isInitial : IsInitial initial
  start : initial ⟶ X
  chain : @TransfiniteCompositionOfShape _ _ order linearOrder orderBot
    _ _ start succOrder wellFoundedLT
  attachment : ∀ j, ¬ IsMax j → BoundaryAttachment
    (chain.F.map (homOfLE (Order.le_succ j)))

def IsCellular {C : GlobularTheory.{v}} (X : C.Model) : Prop := Nonempty X.CellularPresentation

end Model

def unitPair (C : GlobularTheory.{v}) (n : ℕ) : C.AdmissiblePair where
  n := n
  arity := Shape.globe n
  height := Nat.le_succ n
  source := C.id (Shape.globe n)
  target := C.id (Shape.globe n)
  parallel := by cases n <;> simp [Parallel]

noncomputable def unit (C : GlobularTheory.{v}) (hC : C.IsCoherator) (n : ℕ) :
    C.Hom (Shape.globe (n + 1)) (Shape.globe n) := Classical.choose (hC.2 (C.unitPair n))

def Model.eval {C : GlobularTheory.{v}} (X : C.Model) {S T : Shape} (f : C.Hom S T) :
    X.presheaf.obj (op (⟨T⟩ : C.Obj)) → X.presheaf.obj (op (⟨S⟩ : C.Obj)) :=
  X.presheaf.map (show (⟨S⟩ : C.Obj) ⟶ ⟨T⟩ from f).op

noncomputable def Model.unitCell {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    (n : ℕ) (x : X.underlying.Cell n) : X.underlying.Cell (n + 1) :=
  X.eval (C.unit hC n) x

noncomputable def Model.baseCell {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    (x : X.underlying.Cell 0) : ∀ n, X.underlying.Cell n
  | 0 => x
  | n + 1 => X.unitCell hC n (X.baseCell hC x n)

def Model.Loops {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    (x : X.underlying.Cell 0) (n : ℕ) : Type v :=
  { z : X.underlying.Cell (n + 1) // X.underlying.source n z = X.baseCell hC x n ∧
      X.underlying.target n z = X.baseCell hC x n }

def Model.Components {C : GlobularTheory.{v}} (X : C.Model) : Type v :=
  Quot (X.underlying.Joined 0)

def Model.HomotopyGroup {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    (x : X.underlying.Cell 0) (n : ℕ) : Type v :=
  Quot (fun a b : X.Loops hC x n => X.underlying.Joined (n + 1) a.1 b.1)

noncomputable def Model.loopsMap {C : GlobularTheory.{v}} {X Y : C.Model} (f : X ⟶ Y)
    (hC : C.IsCoherator) (x : X.underlying.Cell 0) (n : ℕ) :
    X.Loops hC x n → Y.Loops hC ((underlyingMap f).app 0 x) n := by
  have hb : ∀ k, (underlyingMap f).app k (X.baseCell hC x k) =
      Y.baseCell hC ((underlyingMap f).app 0 x) k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      have h := ConcreteCategory.congr_hom (f.naturality
        (show (op (⟨Shape.globe k⟩ : C.Obj)) ⟶ op ⟨Shape.globe (k+1)⟩ from
          Quiver.Hom.op (C.unit hC k))) (X.baseCell hC x k)
      change (underlyingMap f).app (k+1) (X.unitCell hC k (X.baseCell hC x k)) =
        Y.unitCell hC k ((underlyingMap f).app k (X.baseCell hC x k)) at h
      simpa only [baseCell, ih] using h
  exact fun z => ⟨(underlyingMap f).app (n + 1) z.1,
    by rw [← (underlyingMap f).source_app, z.2.1, hb],
    by rw [← (underlyingMap f).target_app, z.2.2, hb]⟩

noncomputable def Model.componentsMap {C : GlobularTheory.{v}} {X Y : C.Model} (f : X ⟶ Y) :
    X.Components → Y.Components :=
  Quot.map ((underlyingMap f).app 0) (by
    rintro _ _ ⟨h, hs, ht⟩
    exact ⟨(underlyingMap f).app _ h,
      by rw [← (underlyingMap f).source_app, hs],
      by rw [← (underlyingMap f).target_app, ht]⟩)

noncomputable def Model.homotopyMap {C : GlobularTheory.{v}} {X Y : C.Model} (f : X ⟶ Y)
    (hC : C.IsCoherator) (x : X.underlying.Cell 0) (n : ℕ) :
    X.HomotopyGroup hC x n → Y.HomotopyGroup hC ((underlyingMap f).app 0 x) n :=
  Quot.map (loopsMap f hC x n) (by
    rintro _ _ ⟨h, hs, ht⟩
    exact ⟨(underlyingMap f).app _ h,
      by rw [← (underlyingMap f).source_app, hs]; rfl,
      by rw [← (underlyingMap f).target_app, ht]; rfl⟩)

def Model.WeakEquivalence {C : GlobularTheory.{v}} (hC : C.IsCoherator) {X Y : C.Model}
    (f : X ⟶ Y) : Prop :=
  Function.Bijective (componentsMap f) ∧
    ∀ (x : X.underlying.Cell 0) (n : ℕ), Function.Bijective (homotopyMap f hC x n)

end GlobularTheory

end Grothendieck

end HomotopyHypothesis

/-! ## Topological globes, realizations and the statement -/

noncomputable section

namespace HomotopyHypothesis

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open Grothendieck

/-! ### Ara's topological globes -/

/-- The closed unit ball of `ℝⁿ`, the underlying set of the topological `n`-globe. -/
abbrev Ball (n : ℕ) : Type := Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1

/-- The face `ℝᵐ → ℝⁿ` (for `m < n`) on vectors: `x ↦ (x, ±√(1 - ‖x‖²), 0, …, 0)`, with the
sign `+` for the source (`side = false`) and `-` for the target (`side = true`), as in Ara's
example of the globular extension `Top`. -/
def faceVec (m n : ℕ) (side : Bool) (x : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i =>
    if hi : (i : ℕ) < m then x ⟨i, hi⟩
    else if (i : ℕ) = m then (if side then -1 else 1) * Real.sqrt (1 - ‖x‖ ^ 2)
    else 0

theorem norm_sq_faceVec {m n : ℕ} (h : m < n) (side : Bool) (x : EuclideanSpace ℝ (Fin m))
    (hx : ‖x‖ ≤ 1) : ‖faceVec m n side x‖ ^ 2 = 1 := by
  have hx2 : 0 ≤ 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
  let g : ℕ → ℝ := fun k =>
    if hk : k < m then (x ⟨k, hk⟩) ^ 2 else if k = m then 1 - ‖x‖ ^ 2 else 0
  have key : ∀ i : Fin n, (faceVec m n side x i) ^ 2 = g i := by
    intro i
    simp only [faceVec, g]
    split_ifs with h1 h2 h3
    · rfl
    · rw [mul_pow, Real.sq_sqrt hx2]
      simp
    · rw [mul_pow, Real.sq_sqrt hx2]
      simp
    · simp
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_congr _ _ key,
    Fin.sum_univ_eq_sum_range g n, ← Finset.sum_range_add_sum_Ico _ h.le]
  have h1 : ∑ k ∈ Finset.range m, g k = ‖x‖ ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range g m, EuclideanSpace.real_norm_sq_eq]
    refine Fintype.sum_congr _ _ fun i => ?_
    simp [g, i.isLt]
  have h2 : ∑ k ∈ Finset.Ico m n, g k = 1 - ‖x‖ ^ 2 := by
    rw [Finset.sum_eq_single_of_mem m (Finset.left_mem_Ico.2 h)]
    · simp [g]
    · intro k hk hne
      have : ¬ k < m := by simp at hk; omega
      simp [g, this, hne]
  rw [h1, h2]
  ring

theorem faceVec_mem {m n : ℕ} (h : m < n) (side : Bool) (x : Ball m) :
    faceVec m n side x.1 ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  have hx : ‖x.1‖ ≤ 1 := mem_closedBall_zero_iff.1 x.2
  have := norm_sq_faceVec h side x.1 hx
  rw [mem_closedBall_zero_iff]
  nlinarith [norm_nonneg (faceVec m n side x.1)]

theorem continuous_faceVec (m n : ℕ) (side : Bool) : Continuous (faceVec m n side) := by
  unfold faceVec
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  split_ifs
  · exact PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) _
  all_goals first
    | exact continuous_const
    | exact continuous_const.mul ((continuous_const.sub (continuous_norm.pow 2)).sqrt)

/-- Iterated faces land on the equator: a face followed by any face is the composite face with
the first side. -/
theorem faceVec_faceVec {m n k : ℕ} (h : m < n) (side side' : Bool)
    (x : EuclideanSpace ℝ (Fin m)) (hx : ‖x‖ ≤ 1) :
    faceVec n k side' (faceVec m n side x) = faceVec m k side x := by
  have hy : 1 - ‖faceVec m n side x‖ ^ 2 = 0 := by
    rw [norm_sq_faceVec h side x hx]; ring
  rw [show faceVec n k side' (faceVec m n side x) = WithLp.toLp 2 fun i : Fin k =>
      if hi : (i : ℕ) < n then faceVec m n side x ⟨i, hi⟩
      else if (i : ℕ) = n then
        (if side' then -1 else 1) * Real.sqrt (1 - ‖faceVec m n side x‖ ^ 2)
      else 0 from rfl, hy, Real.sqrt_zero, mul_zero]
  ext i
  simp only [faceVec, PiLp.toLp_apply]
  split_ifs <;> first | rfl | omega

/-- The face `Bᵐ → Bⁿ` (for `m < n`) of the topological globes. -/
def ballFace {m n : ℕ} (h : m < n) (side : Bool) : C(Ball m, Ball n) where
  toFun x := ⟨faceVec m n side x.1, faceVec_mem h side x⟩
  continuous_toFun :=
    ((continuous_faceVec m n side).comp continuous_subtype_val).subtype_mk _

/-- The topological globes on morphisms of the globe category. -/
def globeMap : ∀ {m n : ℕ}, Globe.Face m n → C(Ball m, Ball n)
  | _, _, .id _ => ContinuousMap.id _
  | _, _, .face h b => ballFace h b

theorem globeMap_comp {m n k : ℕ} (f : Globe.Face m n) (g : Globe.Face n k) :
    globeMap (f.comp g) = (globeMap g).comp (globeMap f) := by
  cases f with
  | id => rfl
  | face h b =>
    cases g with
    | id => rfl
    | face h' b' =>
      refine ContinuousMap.ext fun x => Subtype.ext ?_
      exact (faceVec_faceVec h b b' x.1 (mem_closedBall_zero_iff.1 x.2)).symm

/-- Ara's globular extension `Top` on globes: the `n`-globe is the closed unit ball `𝔻 n` of
`ℝⁿ`, with the hemisphere inclusions as source and target. -/
def topGlobes : Globe ⥤ TopCat.{u} where
  obj n := TopCat.disk.{u} n.dim
  map f := TopCat.ofHom
    ⟨fun x => ULift.up (globeMap f x.down),
      continuous_uliftUp.comp ((globeMap f).continuous.comp continuous_uliftDown)⟩
  map_id _ := rfl
  map_comp f g :=
    TopCat.ext fun x => congrArg ULift.up (DFunLike.congr_fun (globeMap_comp f g) x.down)

/-! ### Realizations and the fundamental ∞-groupoid -/

/-- A topological realization of the globular theory `C` (Ara's globular functor `C → Top`):
a functor `C → Top` that restricts on the globes to the standard topological globes (up to a
specified natural isomorphism) and sends the globular sums of `C` to pushouts of spaces. -/
structure TopRealization (C : GlobularTheory.{u}) where
  /-- The underlying functor. -/
  functor : C.Obj ⥤ TopCat.{u}
  /-- On globes, the functor is the standard topological globes. -/
  onGlobes : C.globes ⋙ functor ≅ topGlobes.{u}
  /-- The functor sends globular sums to pushouts. -/
  sums : ∀ (S : Shape) (b h : ℕ) (hl : b < S.1) (hr : b < h),
    IsPushout (functor.map (C.toTheoryData.arity.map (S.seam hl)))
      (functor.map (C.toTheoryData.arity.map (Shape.face hr false)))
      (functor.map (C.toTheoryData.arity.map (S.inl b h hl hr)))
      (functor.map (C.toTheoryData.arity.map (S.inr b h hl hr)))

/-- The fundamental ∞-groupoid `Π_∞ X` of a space `X` for a realization `R`: its cells of shape
`S` are the continuous maps `R S → X`. -/
def fundamentalGroupoid {C : GlobularTheory.{u}} (R : TopRealization C) (X : TopCat.{u}) :
    C.Model where
  presheaf := R.functor.op ⋙ yoneda.obj X
  sums T b h hl hr := ((R.sums T b h hl hr).op.map (yoneda.obj X)).flip

/-- The fundamental ∞-groupoid functor `Π_∞ : Top → ∞-Gpd_C` of a realization. -/
def fundamentalGroupoidFunctor {C : GlobularTheory.{u}} (R : TopRealization C) :
    TopCat.{u} ⥤ C.Model where
  obj := fundamentalGroupoid R
  map f := show (R.functor.op ⋙ yoneda.obj _) ⟶ (R.functor.op ⋙ yoneda.obj _) from
    Functor.whiskerLeft R.functor.op (yoneda.map f)
  map_id _ := by apply NatTrans.ext; funext; rfl
  map_comp _ _ := by apply NatTrans.ext; funext; rfl

/-! ### Weak homotopy equivalences of spaces -/

/-- The map induced on path components. -/
def zerothHomotopyMap {X Y : TopCat.{u}} (f : X ⟶ Y) : ZerothHomotopy X → ZerothHomotopy Y :=
  Quotient.map f.hom (fun _ _ h => h.map f.hom.continuous)

/-- The map induced on the homotopy group `π_N(X, x)` (Mathlib's cube model). -/
def homotopyGroupMap (N : Type) {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) :
    HomotopyGroup N X x → HomotopyGroup N Y (f x) :=
  Quotient.map (fun p => ⟨f.hom.comp p.1, fun y hy => by simp [p.2 y hy]⟩)
    (fun _ _ ⟨H⟩ => ⟨H.compContinuousMap f.hom⟩)

/-- Weak homotopy equivalences: continuous maps inducing a bijection on path components and on
every homotopy group `πₙ₊₁`, `n ≥ 0`, at every base point. -/
def weakHomotopyEquivalences : MorphismProperty TopCat.{u} := fun X _ f =>
  Function.Bijective (zerothHomotopyMap f) ∧
    ∀ (n : ℕ) (x : X), Function.Bijective (homotopyGroupMap (Fin (n + 1)) f x)

/-- The weak equivalences of ∞-groupoids of type `C`. -/
def modelWeakEquivalences {C : GlobularTheory.{u}} (hC : C.IsCoherator) :
    MorphismProperty C.Model := fun _ _ f => GlobularTheory.Model.WeakEquivalence hC f

/-! ### The statement -/

/-- **The Grothendieck homotopy hypothesis for coherators.** For every coherator `C`:
1. a topological realization of `C` exists;
2. for every topological realization `R`, the fundamental ∞-groupoid functor `Π_∞` sends weak
   homotopy equivalences to weak equivalences of ∞-groupoids of type `C`, and the composite
   `Top → ∞-Gpd_C → Ho(∞-Gpd_C)` is a localization of `Top` at the weak homotopy equivalences;
   that is, the induced functor `Hot = Top[W⁻¹] → Ho(∞-Gpd_C)` is an equivalence of
   categories. -/
def Statement : Prop :=
  ∀ (C : GlobularTheory.{u}) (hC : C.IsCoherator),
    Nonempty (TopRealization C) ∧
    ∀ R : TopRealization C,
      weakHomotopyEquivalences ≤
          (modelWeakEquivalences hC).inverseImage (fundamentalGroupoidFunctor R) ∧
        (fundamentalGroupoidFunctor R ⋙ (modelWeakEquivalences hC).Q).IsLocalization
          weakHomotopyEquivalences

end HomotopyHypothesis

end
