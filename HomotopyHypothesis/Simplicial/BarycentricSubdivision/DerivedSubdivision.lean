import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
universe u v

open CategoryTheory Limits Opposite Convexity

namespace HomotopyHypothesis.Simplicial.BarycentricSubdivision

open HomotopyHypothesis.Henry

lemma semiSimplex_inclusion_length (s : HomotopyHypothesis.Henry.SemiSimplexCategory) :
    (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.obj s).len = s.obj.len := rfl

/-- The category of face incidences of a semi-simplicial set, oriented from a face to a simplex. -/
abbrev FaceCategory (W : SemiSSet.{u}) := (Functor.Elements W)ᵒᵖ

def faceDimension {W : SemiSSet.{u}} (x : FaceCategory W) : ℕ :=
  x.unop.obj.unop.obj.len

def faceCategoryArrowUnderlying {W : SemiSSet.{u}} {x y : FaceCategory W}
    (f : x ⟶ y) : x.unop.obj.unop ⟶ y.unop.obj.unop :=
  f.unop.hom.unop

noncomputable def faceObjectSimplexMap {W : SemiSSet.{u}} (x : FaceCategory W) :
    SemiSSet.stdSimplex.{u}.obj x.unop.obj.unop ⟶ W :=
  CategoryTheory.uliftYonedaEquiv.{u}.symm x.unop.val

lemma faceObjectSimplexMap_naturality {W : SemiSSet.{u}} {x y : FaceCategory W}
    (f : x ⟶ y) :
    (SemiSSet.stdSimplex.{u}.map (faceCategoryArrowUnderlying f)) ≫
      faceObjectSimplexMap y = faceObjectSimplexMap x := by
  apply (CategoryTheory.uliftYonedaEquiv.{u}).injective
  rw [CategoryTheory.uliftYonedaEquiv_comp]
  have hmap :
      CategoryTheory.uliftYonedaEquiv.{u}
        (SemiSSet.stdSimplex.{u}.map (faceCategoryArrowUnderlying f)) =
        ULift.up (faceCategoryArrowUnderlying f) := by
    change CategoryTheory.uliftYonedaEquiv.{u}
        (CategoryTheory.uliftYoneda.{u}.map (faceCategoryArrowUnderlying f)) = _
    exact CategoryTheory.uliftYonedaEquiv_uliftYoneda_map _
  rw [hmap]
  simp only [faceObjectSimplexMap,
    CategoryTheory.uliftYonedaEquiv_symm_apply_app, Equiv.apply_symm_apply]
  change W.map (Opposite.op (faceCategoryArrowUnderlying f)) y.unop.val = x.unop.val
  exact f.unop.map_val

noncomputable def faceObjectSimplexChar {W : SemiSSet.{u}} (x : FaceCategory W) :
    SemiSSet.toTop.{u}.obj x.unop.obj.unop ⟶ SemiSSet.realization.{u}.obj W :=
  (SemiSSet.stdSimplex.{u}.leftKanExtensionUnit SemiSSet.toTop.{u}).app
      x.unop.obj.unop ≫
    SemiSSet.realization.{u}.map (faceObjectSimplexMap x)

lemma faceObjectSimplexChar_naturality {W : SemiSSet.{u}} {x y : FaceCategory W}
    (f : x ⟶ y) :
    SemiSSet.toTop.{u}.map (faceCategoryArrowUnderlying f) ≫
        faceObjectSimplexChar y = faceObjectSimplexChar x := by
  let α := faceCategoryArrowUnderlying f
  have hmap :
      SemiSSet.realization.{u}.map (SemiSSet.stdSimplex.{u}.map α) ≫
        SemiSSet.realization.{u}.map (faceObjectSimplexMap y) =
          SemiSSet.realization.{u}.map (faceObjectSimplexMap x) := by
    rw [← Functor.map_comp, faceObjectSimplexMap_naturality f]
  ext z
  change (SemiSSet.realization.{u}.map (faceObjectSimplexMap y))
      ((SemiSSet.stdSimplex.{u}.leftKanExtensionUnit SemiSSet.toTop.{u}).app
        y.unop.obj.unop ((SemiSSet.toTop.{u}.map α) z)) =
    (SemiSSet.realization.{u}.map (faceObjectSimplexMap x))
      ((SemiSSet.stdSimplex.{u}.leftKanExtensionUnit SemiSSet.toTop.{u}).app
        x.unop.obj.unop z)
  rw [(SemiSSet.stdSimplex.{u}.leftKanExtensionUnit
    SemiSSet.toTop.{u}).naturality_apply α z]
  change (SemiSSet.realization.{u}.map (faceObjectSimplexMap y))
      ((SemiSSet.realization.{u}.map (SemiSSet.stdSimplex.{u}.map α))
        ((SemiSSet.stdSimplex.{u}.leftKanExtensionUnit SemiSSet.toTop.{u}).app
          x.unop.obj.unop z)) = _
  exact congrArg (fun g => g
    ((SemiSSet.stdSimplex.{u}.leftKanExtensionUnit SemiSSet.toTop.{u}).app
      x.unop.obj.unop z)) hmap

/-- A simplex represented at the standard object of its dimension. -/
def faceObjectOf {W : SemiSSet.{u}} (n : ℕ)
    (w : W.obj (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))) : FaceCategory W :=
  Opposite.op (Functor.Elements.mk w)

/-- Reindex a simplex to the standard representative of its dimension. -/
def standardizeFaceObject {W : SemiSSet.{u}} (x : FaceCategory W) :
    Σ n : ℕ, W.obj (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) := by
  let s := x.unop.obj.unop
  let h : HomotopyHypothesis.Henry.SemiSimplexCategory.mk s.obj.len = s := by
    apply WideSubcategory.ext
    exact SimplexCategory.mk_len s.obj
  let h' : Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk s.obj.len) =
      Opposite.op s := congrArg Opposite.op h
  exact ⟨s.obj.len, W.map (eqToHom h'.symm) x.unop.val⟩

lemma faceObjectOf_standardizeFaceObject {W : SemiSSet.{u}} (x : FaceCategory W) :
    faceObjectOf (standardizeFaceObject x).1 (standardizeFaceObject x).2 = x := by
  let s := x.unop.obj.unop
  let h : HomotopyHypothesis.Henry.SemiSimplexCategory.mk s.obj.len = s := by
    apply WideSubcategory.ext
    exact SimplexCategory.mk_len s.obj
  let h' : Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk s.obj.len) =
      Opposite.op s := congrArg Opposite.op h
  let y := faceObjectOf s.obj.len (W.map (eqToHom h'.symm) x.unop.val)
  change y = x
  apply Opposite.unop_injective
  have hobj : y.unop.obj = x.unop.obj := h'
  have hval : W.map (eqToHom hobj) y.unop.val = x.unop.val := by
    change (W.map (eqToHom h'.symm) ≫ W.map (eqToHom h')) x.unop.val = x.unop.val
    rw [← Functor.map_comp]
    simp
  exact Functor.Elements.ext y.unop x.unop hobj hval

lemma finite_semiSimplex_morphism (a b : HomotopyHypothesis.Henry.SemiSimplexCategory) :
    Finite (a ⟶ b) := by
  haveI : Finite (a.obj ⟶ b.obj) := by infer_instance
  apply Finite.of_injective (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map)
  intro f g h
  exact HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map_injective h

lemma finite_faceCategory_hom {W : SemiSSet.{u}} (x y : FaceCategory W) :
    Finite (x ⟶ y) := by
  haveI : Finite (x.unop.obj.unop ⟶ y.unop.obj.unop) :=
    finite_semiSimplex_morphism _ _
  haveI : Finite (y.unop.obj ⟶ x.unop.obj) :=
    Finite.of_injective (fun f => f.unop) (fun _ _ h => Quiver.Hom.unop_inj h)
  exact Finite.of_injective (fun f : x ⟶ y => f.unop.hom) (by
    intro f g h
    apply Opposite.unop_injective
    exact Functor.Elements.hom_ext h)

lemma finite_faceCategory_of_isFinite {W : SemiSSet.{u}} (hW : W.IsFinite) :
    Finite (FaceCategory W) := by
  classical
  obtain ⟨N, hN⟩ := hW.2
  letI : ∀ n : Fin (N + 1), Finite
      (W.obj (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n.val))) :=
    fun n => hW.1 n.val
  letI : Finite (Σ n : Fin (N + 1),
      W.obj (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n.val))) :=
    inferInstance
  refine Finite.of_surjective
    (fun p : Σ n : Fin (N + 1),
        W.obj (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n.val)) =>
      faceObjectOf p.1.val p.2) ?_
  intro x
  let p := standardizeFaceObject x
  have hp : p.1 ≤ N := by
    by_contra h
    exact (hN p.1 (Nat.lt_of_not_ge h)).false p.2
  let n : Fin (N + 1) := ⟨p.1, Nat.lt_succ_of_le hp⟩
  refine ⟨⟨n, p.2⟩, ?_⟩
  simpa [p, n] using faceObjectOf_standardizeFaceObject x

lemma faceDimension_le_of_bound {W : SemiSSet.{u}} (N : ℕ)
    (hN : ∀ n : ℕ, N < n → IsEmpty (W.obj
      (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))))
    (x : FaceCategory W) : faceDimension x ≤ N := by
  by_contra h
  let p := standardizeFaceObject x
  have hempty := hN (faceDimension x) (Nat.lt_of_not_ge h)
  have hp : W.obj (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk
      (faceDimension x))) := by
    simpa [p, standardizeFaceObject, faceDimension] using p.2
  exact hempty.false hp

abbrev ChainData (C : Type u) [Category.{v} C] (n : ℕ) :=
  (Fin (n + 1) → C) ×
    (Fin (n + 1) → Fin (n + 1) → Option (Σ a : C, Σ b : C, a ⟶ b))

def chainDataOf {C : Type u} [Category.{v} C] {n : ℕ}
    (F : ComposableArrows C n) : ChainData C n :=
  (F.obj, fun i j => if h : i ≤ j then
    some ⟨F.obj i, F.obj j, F.map (CategoryTheory.homOfLE h)⟩ else none)

lemma sigmaSigmaHom_heq {C : Type u} [Category.{v} C] {a a' b b' : C}
    {f : a ⟶ b} {g : a' ⟶ b'}
    (h : (⟨a, ⟨b, f⟩⟩ : Σ x : C, Σ y : C, x ⟶ y) = ⟨a', ⟨b', g⟩⟩) : HEq f g := by
  cases h
  rfl

lemma chainDataOf_injective {C : Type u} [Category.{v} C] (n : ℕ) :
    Function.Injective (chainDataOf (C := C) (n := n)) := by
  intro F G h
  have ho : F.obj = G.obj := congrArg Prod.fst h
  refine CategoryTheory.Functor.ext (fun i => congrFun ho i) ?_
  intro i j f
  let hij : i ≤ j := CategoryTheory.leOfHom f
  have hdata := congrArg Prod.snd h
  have hopt := congrFun (congrFun hdata i) j
  simp only [chainDataOf, dif_pos hij] at hopt
  have htriple := Option.some.inj hopt
  have heq := sigmaSigmaHom_heq htriple
  have hf : f = CategoryTheory.homOfLE hij := Subsingleton.elim _ _
  rw [hf]
  exact (CategoryTheory.conj_eqToHom_iff_heq (F.map (CategoryTheory.homOfLE hij))
    (G.map (CategoryTheory.homOfLE hij)) (congrFun ho i) (congrFun ho j)).2 heq

lemma finite_composableArrows {C : Type u} [Category.{v} C] [Finite C]
    [∀ a b : C, Finite (a ⟶ b)] (n : ℕ) : Finite (ComposableArrows C n) := by
  classical
  letI : Fintype C := Fintype.ofFinite C
  letI (a b : C) : Fintype (a ⟶ b) := Fintype.ofFinite (a ⟶ b)
  haveI : Fintype (ChainData C n) := by
    dsimp [ChainData]
    infer_instance
  exact Finite.of_injective (chainDataOf (C := C) (n := n)) (chainDataOf_injective n)

/-- Chains of faces with strictly increasing dimensions in the face-incidence category. -/
def strictNerveSubfunctor (C : Type u) [Category.{v} C] (rank : C → ℕ) :
    Subfunctor ((SemiSSet.ofSSet.{max u v}).obj (CategoryTheory.nerve C)) where
  obj a x := StrictMono (fun i : Fin (a.unop.obj.len + 1) => rank (x.obj i))
  map {a b} f x hx := by
    let g : b.unop.obj ⟶ a.unop.obj := SemiSimplexCategory.incl.map f.unop
    change StrictMono (fun i : Fin (a.unop.obj.len + 1) => rank (x.obj i)) at hx
    change StrictMono (fun i : Fin (b.unop.obj.len + 1) =>
      rank ((x.whiskerLeft (SimplexCategory.toCat.map g).toFunctor).obj i))
    have hmono : Mono g := by
      change Mono (f.unop.1)
      exact f.unop.property
    have hinj : Function.Injective (SimplexCategory.Hom.toOrderHom g) := by
      rw [← SimplexCategory.mono_iff_injective]
      exact hmono
    have hs : StrictMono (SimplexCategory.Hom.toOrderHom g) :=
      (SimplexCategory.Hom.toOrderHom g).monotone.strictMono_of_injective hinj
    have hobj (i : Fin (b.unop.obj.len + 1)) :
        (SimplexCategory.toCat.map g).toFunctor.obj i =
          SimplexCategory.Hom.toOrderHom g i := by
      simp [SimplexCategory.toCat]
      rfl
    intro i j hij
    change rank (x.obj ((SimplexCategory.toCat.map g).toFunctor.obj i)) <
      rank (x.obj ((SimplexCategory.toCat.map g).toFunctor.obj j))
    rw [hobj i, hobj j]
    exact hx (hs hij)

/-- The composable-arrow chain represented by a simplex in a dimension-ordered nerve. -/
noncomputable def strictNerveTopSimplex {C : Type u} [Category.{v} C]
    (rank : C → ℕ) (n : ℕ)
    (σ : SemiSSet.stdSimplex.{max u v}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) ⟶
      (strictNerveSubfunctor C rank).toFunctor) : ComposableArrows C n :=
  (σ.app (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))
    (ULift.up (𝟙 (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)))).1

lemma strictNerveTopSimplex_strictMono {C : Type u} [Category.{v} C]
    (rank : C → ℕ) (n : ℕ)
    (σ : SemiSSet.stdSimplex.{max u v}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) ⟶
      (strictNerveSubfunctor C rank).toFunctor) :
    StrictMono (fun i : Fin (n + 1) =>
      rank ((strictNerveTopSimplex rank n σ).obj i)) :=
  (σ.app (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))
    (ULift.up (𝟙 (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)))).2

lemma strictNerveTopSimplex_map {C : Type u} [Category.{v} C]
    (rank : C → ℕ) {n m : ℕ}
    (f : HomotopyHypothesis.Henry.SemiSimplexCategory.mk n ⟶
      HomotopyHypothesis.Henry.SemiSimplexCategory.mk m)
    (σ : SemiSSet.stdSimplex.{max u v}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m) ⟶
      (strictNerveSubfunctor C rank).toFunctor) :
    strictNerveTopSimplex rank n ((SemiSSet.stdSimplex.{max u v}.map f) ≫ σ) =
      (strictNerveTopSimplex rank m σ).whiskerLeft
        (SimplexCategory.toCat.map
          (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map f)).toFunctor := by
  let topPoint :
      (SemiSSet.stdSimplex.{max u v}.obj
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m)).obj
        (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m)) :=
    ULift.up (𝟙 (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m))
  have hnat := σ.naturality_apply (Opposite.op f) topPoint
  have hstd :
      ((SemiSSet.stdSimplex.{max u v}.obj
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m)).map (Opposite.op f))
        topPoint = ULift.up f := by
    apply ULift.ext
    change f ≫ 𝟙 (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m) = f
    simp
  have hpoint :
      (SemiSSet.stdSimplex.{max u v}.map f).app
        (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))
        (ULift.up (𝟙 (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))) =
      ULift.up f := by
    apply ULift.ext
    change 𝟙 (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) ≫ f = f
    simp
  have htopMap := hpoint.trans hstd.symm
  have hval := congrArg Subtype.val hnat
  have hpointσ := congrArg Subtype.val
    (congrArg (fun z => σ.app
      (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) z) htopMap)
  let pulled := (SemiSSet.stdSimplex.{max u v}.map f).app
    (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))
    (ULift.up (𝟙 (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)))
  have h1 :
      strictNerveTopSimplex rank n ((SemiSSet.stdSimplex.{max u v}.map f) ≫ σ) =
        (σ.app (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) pulled).1 := rfl
  have h2 :
      (σ.app (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) pulled).1 =
        (σ.app (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))
          ((SemiSSet.stdSimplex.{max u v}.obj
            (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m)).map (Opposite.op f)
              topPoint)).1 := by
    dsimp [pulled]
    exact hpointσ
  have h3 :
      (σ.app (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))
        ((SemiSSet.stdSimplex.{max u v}.obj
          (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m)).map (Opposite.op f)
            topPoint)).1 =
        ((strictNerveSubfunctor C rank).toFunctor.map (Opposite.op f)
          (σ.app (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m)) topPoint)).1 := hval
  have h4 :
      ((strictNerveSubfunctor C rank).toFunctor.map (Opposite.op f)
        (σ.app (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m)) topPoint)).1 =
      (strictNerveTopSimplex rank m σ).whiskerLeft
        (SimplexCategory.toCat.map
          (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map f)).toFunctor := rfl
  exact h1.trans (h2.trans (h3.trans h4))

lemma strictNerveTopSimplex_restrict_obj {C : Type u} [Category.{v} C]
    (rank : C → ℕ) {n m : ℕ}
    (f : HomotopyHypothesis.Henry.SemiSimplexCategory.mk n ⟶
      HomotopyHypothesis.Henry.SemiSimplexCategory.mk m)
    (σ : SemiSSet.stdSimplex.{max u v}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m) ⟶
      (strictNerveSubfunctor C rank).toFunctor)
    (i : Fin (n + 1)) :
    (strictNerveTopSimplex rank n ((SemiSSet.stdSimplex.{max u v}.map f) ≫ σ)).obj i =
      (strictNerveTopSimplex rank m σ).obj
        (SimplexCategory.Hom.toOrderHom
          (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map f) i) := by
  rw [strictNerveTopSimplex_map]
  rfl

lemma strictNerveTopSimplex_restrict_map {C : Type u} [Category.{v} C]
    (rank : C → ℕ) {n m : ℕ}
    (f : HomotopyHypothesis.Henry.SemiSimplexCategory.mk n ⟶
      HomotopyHypothesis.Henry.SemiSimplexCategory.mk m)
    (σ : SemiSSet.stdSimplex.{max u v}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m) ⟶
      (strictNerveSubfunctor C rank).toFunctor)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    HEq
      ((strictNerveTopSimplex rank n ((SemiSSet.stdSimplex.{max u v}.map f) ≫ σ)).map
        (CategoryTheory.homOfLE hij))
      (((strictNerveTopSimplex rank m σ).whiskerLeft
        (SimplexCategory.toCat.map
          (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map f)).toFunctor).map
            (CategoryTheory.homOfLE hij)) := by
  have hchain := strictNerveTopSimplex_map rank f σ
  apply sigmaSigmaHom_heq
  exact congrArg
    (fun z : ComposableArrows C n =>
      (⟨z.obj i, ⟨z.obj j, z.map (CategoryTheory.homOfLE hij)⟩⟩ :
        Σ a : C, Σ b : C, a ⟶ b)) hchain

/-- A rank-preserving functor induces a map of dimension-ordered nerves. -/
noncomputable def strictNerveMap {C D : Type u} [Category.{v} C] [Category.{v} D]
    (rankC : C → ℕ) (rankD : D → ℕ) (F : C ⥤ D)
    (hRank : ∀ c, rankD (F.obj c) = rankC c) :
    (strictNerveSubfunctor C rankC).toFunctor ⟶
      (strictNerveSubfunctor D rankD).toFunctor := by
  let η := (SemiSSet.ofSSet.{max u v}).map (CategoryTheory.nerveMap F)
  refine { app := fun a => TypeCat.ofHom (fun x => ⟨η.app a x.1, ?_⟩), naturality := ?_ }
  · change StrictMono (fun i => rankD (F.obj (x.1.obj i)))
    intro i j hij
    simpa only [hRank] using x.2 hij
  · intro a b f
    apply TypeCat.homEquiv.injective
    funext x
    apply Subtype.ext
    change η.app b (((SemiSSet.ofSSet.{max u v}).obj (CategoryTheory.nerve C)).map f x.1) =
      (((SemiSSet.ofSSet.{max u v}).obj (CategoryTheory.nerve D)).map f) (η.app a x.1)
    exact η.naturality_apply f x.1

lemma strictNerveSubfunctor_isFinite {C : Type u} [Category.{v} C] [Finite C]
    (rank : C → ℕ) (hHom : ∀ a b : C, Finite (a ⟶ b)) (M : ℕ)
    (hRank : ∀ c, rank c ≤ M) :
    SemiSSet.IsFinite (strictNerveSubfunctor C rank).toFunctor := by
  letI : ∀ a b : C, Finite (a ⟶ b) := hHom
  constructor
  · intro n
    letI : Finite (ComposableArrows C n) := finite_composableArrows n
    change Finite {x : ComposableArrows C n // StrictMono (fun i => rank (x.obj i))}
    infer_instance
  · refine ⟨M, fun n hn => ?_⟩
    change IsEmpty {x : ComposableArrows C n // StrictMono (fun i => rank (x.obj i))}
    refine ⟨fun x => ?_⟩
    let f : Fin (n + 1) → Fin (M + 1) := fun i => ⟨rank (x.1.obj i),
      Nat.lt_succ_of_le (hRank (x.1.obj i))⟩
    have hf : StrictMono f := by
      intro i j hij
      exact Fin.mk_lt_mk.mpr (x.2 hij)
    have hcard := Fintype.card_le_of_injective f hf.injective
    simp only [Fintype.card_fin] at hcard
    omega

lemma mapComposableArrows_obj_injective {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) [F.Faithful] (hObj : Function.Injective F.obj) (n : ℕ) :
    Function.Injective ((F.mapComposableArrows n).obj) := by
  intro α β h
  have hObjAt (i : Fin (n + 1)) : F.obj (α.obj i) = F.obj (β.obj i) := by
    have hi := congrArg (fun X : ComposableArrows D n => X.obj i) h
    simpa [CategoryTheory.Functor.mapComposableArrows] using hi
  have hSourceAt (i : Fin (n + 1)) : α.obj i = β.obj i := hObj (hObjAt i)
  refine CategoryTheory.Functor.ext (fun i => hObj (hObjAt i)) ?_
  intro i j f
  have hmapHEq : HEq (F.map (α.map f)) (F.map (β.map f)) := by
    simpa [CategoryTheory.Functor.mapComposableArrows] using
      (CategoryTheory.Functor.hcongr_hom h f)
  have hconj := (CategoryTheory.conj_eqToHom_iff_heq _ _
    (hObjAt i) (hObjAt j)).2 hmapHEq
  have hmap : F.map (α.map f) = F.map
      (eqToHom (hSourceAt i) ≫ β.map f ≫ eqToHom (hSourceAt j).symm) := by
    simpa [Functor.map_comp, Category.assoc, eqToHom_map] using hconj
  exact F.map_injective hmap

lemma strictNerveMap_app_injective {C D : Type u} [Category.{v} C] [Category.{v} D]
    (rankC : C → ℕ) (rankD : D → ℕ) (F : C ⥤ D) [F.Faithful]
    (hRank : ∀ c, rankD (F.obj c) = rankC c) (hObj : Function.Injective F.obj)
    (a : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ) :
    Function.Injective (strictNerveMap rankC rankD F hRank |>.app a) := by
  intro x y h
  apply Subtype.ext
  have hval := congrArg Subtype.val h
  change ((SemiSSet.ofSSet.{max u v}).map (CategoryTheory.nerveMap F)).app a x.1 =
    ((SemiSSet.ofSSet.{max u v}).map (CategoryTheory.nerveMap F)).app a y.1 at hval
  change (F.mapComposableArrows a.unop.obj.len).obj x.1 =
    (F.mapComposableArrows a.unop.obj.len).obj y.1 at hval
  exact mapComposableArrows_obj_injective F hObj a.unop.obj.len hval

lemma strictNerveMap_mono {C D : Type u} [Category.{v} C] [Category.{v} D]
    (rankC : C → ℕ) (rankD : D → ℕ) (F : C ⥤ D) [F.Faithful]
    (hRank : ∀ c, rankD (F.obj c) = rankC c) (hObj : Function.Injective F.obj) :
    Mono (strictNerveMap rankC rankD F hRank) := by
  have hApp : ∀ a, Mono ((strictNerveMap rankC rankD F hRank).app a) := by
    intro a
    exact (CategoryTheory.mono_iff_injective _).2
      (strictNerveMap_app_injective rankC rankD F hRank hObj a)
  exact NatTrans.mono_of_mono_app _

/-- The induced map between face-incidence categories. -/
def faceFunctor {W V : SemiSSet.{u}} (φ : W ⟶ V) : FaceCategory W ⥤ FaceCategory V :=
  (NatTrans.mapElements φ).op

lemma mono_app_injective {W V : SemiSSet.{u}} (φ : W ⟶ V) [Mono φ]
    (a : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ) : Function.Injective (φ.app a) := by
  haveI : Mono (φ.app a) := by infer_instance
  exact (CategoryTheory.mono_iff_injective _).mp inferInstance

lemma cast_eq_of_heq {α : Sort u} {β : α → Sort v} {a b : α} (h : a = b)
    {x : β a} {y : β b} (hxy : HEq x y) : cast (congrArg β h) x = y := by
  cases h
  exact eq_of_heq hxy

lemma eqToHom_apply_type {A B : Type u} (h : A = B) (x : A) :
    (eqToHom h : A ⟶ B) x = cast h x := by
  cases h
  rfl

lemma faceFunctor_obj_injective {W V : SemiSSet.{u}} (φ : W ⟶ V) [Mono φ] :
    Function.Injective (faceFunctor φ).obj := by
  intro x y h
  have hElem : (NatTrans.mapElements φ).obj x.unop = (NatTrans.mapElements φ).obj y.unop :=
    congrArg Opposite.unop h
  have htuple :
      (⟨(Functor.Elements.π V).obj ((NatTrans.mapElements φ).obj x.unop),
        ((NatTrans.mapElements φ).obj x.unop).val⟩ :
          Σ a : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ, V.obj a) =
      ⟨(Functor.Elements.π V).obj ((NatTrans.mapElements φ).obj y.unop),
        ((NatTrans.mapElements φ).obj y.unop).val⟩ :=
    congrArg (fun z : Functor.Elements V =>
      (⟨(Functor.Elements.π V).obj z, z.val⟩ :
        Σ a : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ, V.obj a)) hElem
  obtain ⟨hbase, hval⟩ := Sigma.ext_iff.mp htuple
  have hcast : V.map (eqToHom hbase) (φ.app x.unop.obj x.unop.val) =
      φ.app y.unop.obj y.unop.val := by
    rw [eqToHom_map, eqToHom_apply_type]
    exact cast_eq_of_heq hbase hval
  have hnat := NatTrans.naturality_apply φ (eqToHom hbase) x.unop.val
  have hsource : W.map (eqToHom hbase) x.unop.val = y.unop.val :=
    mono_app_injective φ y.unop.obj (hnat.trans hcast)
  apply Opposite.unop_injective
  exact Functor.Elements.ext x.unop y.unop hbase hsource

lemma faceFunctor_faithful {W V : SemiSSet.{u}} (φ : W ⟶ V) :
    (faceFunctor φ).Faithful where
  map_injective {x y} f g h := by
    have h' := Quiver.Hom.op_inj h
    have hu : f.unop = g.unop := by
      apply (Functor.Elements.π W).map_injective
      simpa [NatTrans.mapElements_comp_π] using
        congrArg (fun q => (Functor.Elements.π V).map q) h'
    exact Quiver.Hom.unop_inj hu

abbrev Vertices (X : SemiSSet.{u}) :=
  X.obj (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk 0))

/-- The set of vertices, equipped with the indiscrete topology for quotient arguments. -/
noncomputable def vertexSupport : SemiSSet.{u} ⥤ TopCat.{u} where
  obj X := by
    letI : TopologicalSpace (Set (Vertices X)) := ⊤
    exact TopCat.of (Set (Vertices X))
  map {X Y} f := by
    letI : TopologicalSpace (Set (Vertices X)) := ⊤
    letI : TopologicalSpace (Set (Vertices Y)) := ⊤
    exact TopCat.ofHom ⟨fun s => Set.image (f.app
      (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk 0))) s,
      continuous_of_indiscreteTopology⟩
  map_id X := by
    ext s x
    simp
  map_comp f g := by
    ext s x
    simp [Set.image_image]

noncomputable def vertexInclusionAt
    (s : HomotopyHypothesis.Henry.SemiSimplexCategory)
    (i : Fin ((HomotopyHypothesis.Henry.SemiSimplexCategory.incl.obj s).len + 1)) :
    HomotopyHypothesis.Henry.SemiSimplexCategory.mk 0 ⟶ s := by
  let i' : Fin (s.obj.len + 1) := ⟨i.val, by
    simpa only [semiSimplex_inclusion_length] using i.isLt⟩
  let f := SimplexCategory.const (SimplexCategory.mk 0) s.obj i'
  haveI : Mono f := by
    rw [SimplexCategory.mono_iff_injective]
    intro a b h
    apply Fin.ext
    have ha : a.val < 1 := by simpa using a.isLt
    have hb : b.val < 1 := by simpa using b.isLt
    omega
  exact ⟨f, inferInstance⟩

lemma strictNerveTopSimplex_vertex {C : Type u} [Category.{v} C]
    (rank : C → ℕ) (n : ℕ)
    (σ : SemiSSet.stdSimplex.{max u v}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) ⟶
      (strictNerveSubfunctor C rank).toFunctor)
    (i : Fin (n + 1)) :
    (σ.app (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk 0))
      (ULift.up (vertexInclusionAt
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) i))).1 =
      ComposableArrows.mk₀ ((strictNerveTopSimplex rank n σ).obj i) := by
  let topPoint :
      (SemiSSet.stdSimplex.{max u v}.obj
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)).obj
        (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) :=
    ULift.up (𝟙 (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))
  have hnat := σ.naturality_apply
    (Opposite.op (vertexInclusionAt
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) i))
    topPoint
  apply ComposableArrows.ext₀
  have hobj := congrArg
    (fun z : (strictNerveSubfunctor C rank).toFunctor.obj
        (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk 0)) =>
      z.1.obj' 0) hnat
  have hindex :
      (SimplexCategory.Hom.toOrderHom
        (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map
          (vertexInclusionAt
            (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) i))) 0 = i := by
    apply Fin.ext
    rfl
  dsimp [topPoint, strictNerveSubfunctor, Subfunctor.toFunctor,
    SemiSSet.ofSSet, CategoryTheory.nerve] at hobj
  change (σ.app (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk 0))
        (ULift.up (vertexInclusionAt
          (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) i))).1.obj' 0 =
      (strictNerveTopSimplex rank n σ).obj
        ((SimplexCategory.Hom.toOrderHom
          (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map
            (vertexInclusionAt
              (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) i))) 0) at hobj
  rw [hindex] at hobj
  exact hobj

lemma vertexInclusion_comp {s t : HomotopyHypothesis.Henry.SemiSimplexCategory}
    (f : s ⟶ t) (i : Fin ((HomotopyHypothesis.Henry.SemiSimplexCategory.incl.obj s).len + 1)) :
    vertexInclusionAt s i ≫ f = vertexInclusionAt t
      ((SimplexCategory.Hom.toOrderHom
        (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map f)) i) := by
  apply HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map_injective
  apply SimplexCategory.Hom.ext
  ext j
  fin_cases j
  rfl

lemma stdSimplex_map_vertex {s t : HomotopyHypothesis.Henry.SemiSimplexCategory}
    (f : s ⟶ t)
    (i : Fin ((HomotopyHypothesis.Henry.SemiSimplexCategory.incl.obj s).len + 1)) :
    (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.map f).app
      (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk 0))
      (ULift.up (vertexInclusionAt s i)) =
    ULift.up (vertexInclusionAt t
      ((SimplexCategory.Hom.toOrderHom
        (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map f)) i)) := by
  change ULift.up (vertexInclusionAt s i ≫ f) = _
  rw [vertexInclusion_comp]

noncomputable def simplexVertexSupport (s : HomotopyHypothesis.Henry.SemiSimplexCategory) :
    HomotopyHypothesis.Henry.SemiSSet.toTop.obj
        s ⟶
      vertexSupport.obj (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.obj
        s) := by
  letI : TopologicalSpace (Set (Vertices
      (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.obj s))) := ⊤
  exact TopCat.ofHom ⟨fun x : ULift (StdSimplex ℝ
      (Fin ((HomotopyHypothesis.Henry.SemiSimplexCategory.incl.obj s).len + 1))) =>
    Set.image (fun i => ULift.up (vertexInclusionAt s i))
      (x.down.weights.support : Set
        (Fin ((HomotopyHypothesis.Henry.SemiSimplexCategory.incl.obj s).len + 1))),
      continuous_of_indiscreteTopology⟩

lemma simplexVertexSupport_vertex (n : ℕ) (i : Fin (n + 1)) :
    simplexVertexSupport (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)
      (SemiSSet.simplexVertex i) =
    Set.singleton (ULift.up (vertexInclusionAt
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) i)) := by
  have hsupp : (StdSimplex.single (R := ℝ) i).weights.support = {i} :=
    StdSimplex.support_weights_eq_singleton.mpr rfl
  change Set.image (fun j : Fin (n + 1) => ULift.up (vertexInclusionAt
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) j))
      ((StdSimplex.single (R := ℝ) i).weights.support : Set (Fin (n + 1))) =
    Set.singleton (ULift.up (vertexInclusionAt
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) i))
  rw [hsupp, Finset.coe_singleton, Set.image_singleton]
  rfl

lemma simplexVertexSupport_natural {s t : HomotopyHypothesis.Henry.SemiSimplexCategory}
    (f : s ⟶ t)
    (x : ULift (StdSimplex ℝ
      (Fin ((HomotopyHypothesis.Henry.SemiSimplexCategory.incl.obj s).len + 1)))) :
    simplexVertexSupport t (HomotopyHypothesis.Henry.SemiSSet.toTop.map f x) =
      (vertexSupport.map (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.map f))
        (simplexVertexSupport s x) := by
  let α := SimplexCategory.Hom.toOrderHom
    (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map f)
  have hmono : Mono (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map f) := by
    change Mono f.1
    exact f.property
  have hα : Function.Injective α := by
    rw [← SimplexCategory.mono_iff_injective]
    exact hmono
  have hSupport : (StdSimplex.map (R := ℝ) (⇑α) x.down).weights.support =
      x.down.weights.support.image α := by
    simpa [StdSimplex.map] using
      (Finsupp.mapDomain_support_of_injective hα x.down.weights)
  change Set.image (fun i : Fin ((HomotopyHypothesis.Henry.SemiSimplexCategory.incl.obj t).len + 1) =>
        ULift.up (vertexInclusionAt t i))
      ((StdSimplex.map (R := ℝ) (⇑α) x.down).weights.support : Set
        (Fin ((HomotopyHypothesis.Henry.SemiSimplexCategory.incl.obj t).len + 1))) =
    Set.image (fun z => (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.map f).app
        (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk 0)) z)
      (Set.image (fun i : Fin ((HomotopyHypothesis.Henry.SemiSimplexCategory.incl.obj s).len + 1) =>
          ULift.up (vertexInclusionAt s i))
        (x.down.weights.support : Set
          (Fin ((HomotopyHypothesis.Henry.SemiSimplexCategory.incl.obj s).len + 1))))
  rw [hSupport]
  ext z
  simp only [Set.mem_image, Finset.mem_coe, Finset.mem_image]
  constructor
  · rintro ⟨k, ⟨i, hi, rfl⟩, hz⟩
    exact ⟨ULift.up (vertexInclusionAt s i), ⟨i, hi, rfl⟩,
      (stdSimplex_map_vertex f i).trans hz⟩
  · rintro ⟨v, ⟨i, hi, rfl⟩, hz⟩
    refine ⟨α i, ⟨i, hi, rfl⟩, ?_⟩
    exact (stdSimplex_map_vertex f i).symm.trans hz

noncomputable def simplexVertexSupportUnit :
    HomotopyHypothesis.Henry.SemiSSet.toTop.{u} ⟶
      HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u} ⋙ vertexSupport.{u} where
  app s := simplexVertexSupport s
  naturality {s t} f := by
    ext x
    exact simplexVertexSupport_natural f x

/-- Descend a compatible family of simplex maps to a map of realizations. -/
noncomputable def realizationMapOfSimplexFamily {A B : SemiSSet.{u}}
    (q : ∀ s : HomotopyHypothesis.Henry.SemiSimplexCategory,
      (SemiSSet.stdSimplex.{u}.obj s ⟶ A) →
        (SemiSSet.toTop.{u}.obj s ⟶ SemiSSet.realization.{u}.obj B))
    (hq : ∀ {s t : HomotopyHypothesis.Henry.SemiSimplexCategory}
      (f : s ⟶ t) (y : SemiSSet.stdSimplex.{u}.obj t ⟶ A),
      SemiSSet.toTop.{u}.map f ≫ q t y =
        q s ((SemiSSet.stdSimplex.{u}.map f) ≫ y)) :
    SemiSSet.realization.{u}.obj A ⟶ SemiSSet.realization.{u}.obj B := by
  let α := (SemiSSet.stdSimplex.{u}.leftKanExtensionUnit SemiSSet.toTop.{u})
  letI : SemiSSet.realization.{u}.IsLeftKanExtension α := by
    dsimp [SemiSSet.realization, α]
    infer_instance
  let hpw := Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
    (F' := SemiSSet.realization.{u}) α
  let D := CategoryTheory.CostructuredArrow.proj SemiSSet.stdSimplex.{u} A ⋙
    SemiSSet.toTop.{u}
  let c : Cocone D := {
    pt := SemiSSet.realization.{u}.obj B
    ι := {
      app := fun g => q g.left g.hom
      naturality := by
        intro g h f
        dsimp [D]
        rw [← CategoryTheory.CostructuredArrow.w f]
        exact hq f.left h.hom
    }
  }
  exact (hpw A).desc c

lemma realizationMapOfSimplexFamily_fac {A B : SemiSSet.{u}}
    (q : ∀ s : HomotopyHypothesis.Henry.SemiSimplexCategory,
      (SemiSSet.stdSimplex.{u}.obj s ⟶ A) →
        (SemiSSet.toTop.{u}.obj s ⟶ SemiSSet.realization.{u}.obj B))
    (hq : ∀ {s t : HomotopyHypothesis.Henry.SemiSimplexCategory}
      (f : s ⟶ t) (y : SemiSSet.stdSimplex.{u}.obj t ⟶ A),
      SemiSSet.toTop.{u}.map f ≫ q t y =
        q s ((SemiSSet.stdSimplex.{u}.map f) ≫ y))
    (s : HomotopyHypothesis.Henry.SemiSimplexCategory)
    (y : SemiSSet.stdSimplex.{u}.obj s ⟶ A) :
    ((SemiSSet.stdSimplex.{u}.leftKanExtensionUnit SemiSSet.toTop.{u}).app s ≫
      SemiSSet.realization.{u}.map y) ≫ realizationMapOfSimplexFamily q hq = q s y := by
  classical
  unfold realizationMapOfSimplexFamily
  let α := (SemiSSet.stdSimplex.{u}.leftKanExtensionUnit SemiSSet.toTop.{u})
  letI : SemiSSet.realization.{u}.IsLeftKanExtension α := by
    dsimp [SemiSSet.realization, α]
    infer_instance
  let hpw := Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
    (F' := SemiSSet.realization.{u}) α
  let D := CategoryTheory.CostructuredArrow.proj SemiSSet.stdSimplex.{u} A ⋙
    SemiSSet.toTop.{u}
  let c : Cocone D := {
    pt := SemiSSet.realization.{u}.obj B
    ι := {
      app := fun g => q g.left g.hom
      naturality := by
        intro g h f
        dsimp [D]
        rw [← CategoryTheory.CostructuredArrow.w f]
        exact hq f.left h.hom
    }
  }
  have hf := (hpw A).fac c (CategoryTheory.CostructuredArrow.mk y)
  change ((SemiSSet.stdSimplex.{u}.leftKanExtensionUnit SemiSSet.toTop.{u}).app s ≫
      SemiSSet.realization.{u}.map y) ≫ (hpw A).desc c = q s y at hf
  exact hf

noncomputable def realizationVertexSupport :
    HomotopyHypothesis.Henry.SemiSSet.realization.{u} ⟶ vertexSupport.{u} := by
  letI : HomotopyHypothesis.Henry.SemiSSet.realization.{u}.IsLeftKanExtension
      (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit
        HomotopyHypothesis.Henry.SemiSSet.toTop.{u}) := by
    dsimp [HomotopyHypothesis.Henry.SemiSSet.realization]
    infer_instance
  exact CategoryTheory.Functor.descOfIsLeftKanExtension
    (F' := HomotopyHypothesis.Henry.SemiSSet.realization.{u})
    (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit
      HomotopyHypothesis.Henry.SemiSSet.toTop.{u})
    vertexSupport.{u} simplexVertexSupportUnit

lemma realizationVertexSupport_simplexChar {W : SemiSSet.{u}} {n : ℕ}
    (y : SemiSSet.stdSimplex.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) ⟶ W)
    (x : SemiSSet.toTop.{u}.obj (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) :
    (realizationVertexSupport.app W)
        ((SemiSSet.simplexChar y) x) =
      (vertexSupport.{u}.map y)
        (simplexVertexSupport (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) x) := by
  let d : SemiSSet.{u} := HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
    (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)
  letI : HomotopyHypothesis.Henry.SemiSSet.realization.{u}.IsLeftKanExtension
      (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit
        HomotopyHypothesis.Henry.SemiSSet.toTop.{u}) := by
    dsimp [HomotopyHypothesis.Henry.SemiSSet.realization]
    infer_instance
  have hfac : (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit
      HomotopyHypothesis.Henry.SemiSSet.toTop.{u}).app
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) ≫
      realizationVertexSupport.{u}.app d = simplexVertexSupportUnit.{u}.app
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) := by
    change (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit
      HomotopyHypothesis.Henry.SemiSSet.toTop.{u}).app
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) ≫
      (Functor.descOfIsLeftKanExtension
        (F' := HomotopyHypothesis.Henry.SemiSSet.realization.{u})
        (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit
          HomotopyHypothesis.Henry.SemiSSet.toTop.{u})
        vertexSupport.{u} simplexVertexSupportUnit.{u}).app d =
      simplexVertexSupportUnit.{u}.app
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)
    exact Functor.descOfIsLeftKanExtension_fac_app
      (F' := HomotopyHypothesis.Henry.SemiSSet.realization.{u})
      (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit
        HomotopyHypothesis.Henry.SemiSSet.toTop.{u})
      vertexSupport.{u} simplexVertexSupportUnit.{u}
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)
  have hnat := realizationVertexSupport.{u}.naturality y
  let α := (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit
    HomotopyHypothesis.Henry.SemiSSet.toTop.{u}).app
    (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)
  have hnatPoint := congrArg
    (fun f : SemiSSet.realization.obj d ⟶ vertexSupport.{u}.obj W => f (α x)) hnat
  change realizationVertexSupport.{u}.app W
      ((HomotopyHypothesis.Henry.SemiSSet.realization.{u}.map y) (α x)) =
    (vertexSupport.{u}.map y) (realizationVertexSupport.{u}.app d (α x)) at hnatPoint
  have hfacPoint := congrArg
    (fun f : SemiSSet.toTop.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) ⟶ vertexSupport.{u}.obj d => f x)
    hfac
  change realizationVertexSupport.{u}.app d (α x) =
    (simplexVertexSupportUnit.{u}.app
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) x at hfacPoint
  have hfacPoint' :
      realizationVertexSupport.{u}.app d (α x) =
        simplexVertexSupport (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) x := by
    simpa [simplexVertexSupportUnit] using hfacPoint
  simp only [SemiSSet.simplexChar, CategoryTheory.comp_apply]
  calc
    realizationVertexSupport.{u}.app W
        ((HomotopyHypothesis.Henry.SemiSSet.realization.{u}.map y) (α x)) =
      (vertexSupport.{u}.map y) (realizationVertexSupport.{u}.app d (α x)) := hnatPoint
    _ = (vertexSupport.{u}.map y)
        (simplexVertexSupport (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) x) := by
      rw [hfacPoint']

lemma realizationVertexSupport_simplexChar_vertex {W : SemiSSet.{u}} {n : ℕ}
    (y : SemiSSet.stdSimplex.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) ⟶ W)
    (i : Fin (n + 1)) :
    (realizationVertexSupport.{u}.app W)
        ((SemiSSet.simplexChar y) (SemiSSet.simplexVertex i)) =
      Set.singleton ((y.app
        (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk 0)))
          (ULift.up (vertexInclusionAt
            (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) i))) := by
  let i' : Fin ((HomotopyHypothesis.Henry.SemiSimplexCategory.incl.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)).len + 1) := ⟨i.val, by
    simpa only [semiSimplex_inclusion_length] using i.isLt⟩
  have hi : vertexInclusionAt
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) i =
      vertexInclusionAt (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) i' := by
    apply HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map_injective
    apply SimplexCategory.Hom.ext
    ext j
    fin_cases j
    rfl
  rw [realizationVertexSupport_simplexChar y (SemiSSet.simplexVertex i)]
  rw [simplexVertexSupport_vertex]
  rw [hi]
  change Set.image (fun z =>
      (y.app (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk 0))) z)
      (Set.singleton (ULift.up (vertexInclusionAt
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) i'))) = _
  change (fun z =>
      (y.app (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk 0))) z) ''
      {ULift.up (vertexInclusionAt
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) i')} =
    {(y.app (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk 0))
      (ULift.up (vertexInclusionAt
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) i')))}
  exact Set.image_singleton

lemma simplexChar_vertex_eq_zeroFace {K : SemiSSet.{u}} {n : ℕ}
    (σ τ : SemiSSet.stdSimplex.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) ⟶ K)
    (i j : Fin (n + 1))
    (h : (SemiSSet.simplexChar σ).hom (SemiSSet.simplexVertex i) =
      (SemiSSet.simplexChar τ).hom (SemiSSet.simplexVertex j)) :
    σ.app (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk 0))
        (ULift.up (vertexInclusionAt
          (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) i)) =
      τ.app (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk 0))
        (ULift.up (vertexInclusionAt
          (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) j)) := by
  have hsupport := congrArg
    (fun x => (realizationVertexSupport.{u}.app K) x) h
  rw [realizationVertexSupport_simplexChar_vertex σ i,
    realizationVertexSupport_simplexChar_vertex τ j] at hsupport
  exact Set.singleton_injective hsupport

lemma faceFunctor_preserves_dimension {W V : SemiSSet.{u}} (φ : W ⟶ V)
    (x : FaceCategory W) :
    faceDimension (W := V) ((faceFunctor φ).obj x) = faceDimension x := by
  rfl

/-- The first derived subdivision, formed from strict chains in the face category. -/
noncomputable def firstSubdivision : SemiSSet.{u} ⥤ SemiSSet.{u} where
  obj W := (strictNerveSubfunctor (FaceCategory W) (faceDimension (W := W))).toFunctor
  map {W V} φ := strictNerveMap (faceDimension (W := W)) (faceDimension (W := V))
    (faceFunctor φ) (faceFunctor_preserves_dimension φ)
  map_id W := by
    ext a x
    apply Subtype.ext
    rfl
  map_comp {W V Z} φ ψ := by
    ext a x
    apply Subtype.ext
    rfl

lemma firstSubdivision_faceCategory_isThin (W : SemiSSet.{u}) :
    Quiver.IsThin (FaceCategory (firstSubdivision.obj W)) := by
  intro x y
  refine ⟨fun f g => ?_⟩
  let α : x.unop.obj.unop ⟶ y.unop.obj.unop := f.unop.hom.unop
  let β : x.unop.obj.unop ⟶ y.unop.obj.unop := g.unop.hom.unop
  have hF := congrArg Subtype.val f.unop.map_val
  have hG := congrArg Subtype.val g.unop.map_val
  change (y.unop.val.1.whiskerLeft
      (SimplexCategory.toCat.map (SemiSimplexCategory.incl.map α)).toFunctor) =
    x.unop.val.1 at hF
  change (y.unop.val.1.whiskerLeft
      (SimplexCategory.toCat.map (SemiSimplexCategory.incl.map β)).toFunctor) =
    x.unop.val.1 at hG
  apply Quiver.Hom.unop_inj
  apply Functor.Elements.hom_ext
  apply Quiver.Hom.unop_inj
  apply SemiSimplexCategory.incl.map_injective
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  have hObjF : y.unop.val.1.obj ((SimplexCategory.toCat.map
      (SemiSimplexCategory.incl.map α)).toFunctor.obj i) = x.unop.val.1.obj i :=
    congrFun (congrArg (fun z : ComposableArrows (FaceCategory W)
      x.unop.obj.unop.obj.len => z.obj) hF) i
  have hObjG : y.unop.val.1.obj ((SimplexCategory.toCat.map
      (SemiSimplexCategory.incl.map β)).toFunctor.obj i) = x.unop.val.1.obj i :=
    congrFun (congrArg (fun z : ComposableArrows (FaceCategory W)
      x.unop.obj.unop.obj.len => z.obj) hG) i
  have hRankEq : faceDimension (W := W) (y.unop.val.1.obj
      ((SimplexCategory.toCat.map (SemiSimplexCategory.incl.map α)).toFunctor.obj i)) =
    faceDimension (W := W) (y.unop.val.1.obj
      ((SimplexCategory.toCat.map (SemiSimplexCategory.incl.map β)).toFunctor.obj i)) :=
    (congrArg (faceDimension (W := W)) hObjF).trans
      (congrArg (faceDimension (W := W)) hObjG).symm
  have hiEq := y.unop.val.2.injective hRankEq
  change (SimplexCategory.toCat.map (SemiSimplexCategory.incl.map α)).toFunctor.obj i =
    (SimplexCategory.toCat.map (SemiSimplexCategory.incl.map β)).toFunctor.obj i
  exact hiEq

lemma strictChain_eq_of_range_eq {C : Type u} [Category.{v} C] [Quiver.IsThin C]
    (rank : C → ℕ) (n : ℕ) (x y : ComposableArrows C n)
    (hx : StrictMono (fun i => rank (x.obj i)))
    (hy : StrictMono (fun i => rank (y.obj i)))
    (hRange : Set.range x.obj = Set.range y.obj) : x = y := by
  have hRankRange : Set.range (fun i => rank (x.obj i)) =
      Set.range (fun i => rank (y.obj i)) := by
    calc
      _ = rank '' Set.range x.obj := Set.range_comp' _ _
      _ = rank '' Set.range y.obj := congrArg (fun s => rank '' s) hRange
      _ = _ := (Set.range_comp' _ _).symm
  have hRankFun := hx.range_inj_of_wellFoundedLT hy |>.mp hRankRange
  have hobj : ∀ i, x.obj i = y.obj i := by
    intro i
    have hmem : x.obj i ∈ Set.range y.obj := by
      rw [← hRange]
      exact Set.mem_range_self i
    rcases hmem with ⟨j, hj⟩
    have hRank : rank (y.obj j) = rank (y.obj i) := by
      calc
        rank (y.obj j) = rank (x.obj i) := congrArg rank hj
        _ = rank (y.obj i) := congrFun hRankFun i
    have hji : j = i := hy.injective hRank
    calc
      x.obj i = y.obj j := hj.symm
      _ = y.obj i := congrArg y.obj hji
  exact CategoryTheory.Functor.ext hobj (by
    intro i j f
    exact Subsingleton.elim _ _)

lemma strictNerve_simplex_eq_of_vertex_range {C : Type u} [Category.{v} C]
    [Quiver.IsThin C] (rank : C → ℕ) (n : ℕ)
    (σ τ : SemiSSet.stdSimplex.{max u v}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) ⟶
      (strictNerveSubfunctor C rank).toFunctor)
    (hRange : Set.range (fun i : Fin (n + 1) =>
        (strictNerveTopSimplex rank n σ).obj i) =
      Set.range (fun i : Fin (n + 1) =>
        (strictNerveTopSimplex rank n τ).obj i)) :
    σ = τ := by
  have hchain := strictChain_eq_of_range_eq rank n
    (strictNerveTopSimplex rank n σ) (strictNerveTopSimplex rank n τ)
    (strictNerveTopSimplex_strictMono rank n σ)
    (strictNerveTopSimplex_strictMono rank n τ) hRange
  let topPoint :
      (SemiSSet.stdSimplex.{max u v}.obj
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)).obj
        (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) :=
    ULift.up (𝟙 (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))
  have htop :
      σ.app (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) topPoint =
      τ.app (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) topPoint := by
    apply Subtype.ext
    exact hchain
  ext a x
  let f : a.unop ⟶ HomotopyHypothesis.Henry.SemiSimplexCategory.mk n := ULift.down x
  have hstd :
      ((SemiSSet.stdSimplex.{max u v}.obj
          (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)).map (Opposite.op f))
        topPoint = x := by
    simp [SemiSSet.stdSimplex, topPoint, f]
  have hσ := σ.naturality_apply (Opposite.op f) topPoint
  have hτ := τ.naturality_apply (Opposite.op f) topPoint
  change σ.app a x = τ.app a x
  rw [hstd] at hσ hτ
  rw [hσ, hτ, htop]

lemma firstSubdivision_map_mono {W V : SemiSSet.{u}} (φ : W ⟶ V) [Mono φ] :
    Mono (firstSubdivision.map φ) := by
  letI : (faceFunctor φ).Faithful := faceFunctor_faithful φ
  change Mono (strictNerveMap (faceDimension (W := W)) (faceDimension (W := V))
    (faceFunctor φ) (faceFunctor_preserves_dimension φ))
  exact strictNerveMap_mono (faceDimension (W := W)) (faceDimension (W := V))
    (faceFunctor φ) (faceFunctor_preserves_dimension φ) (faceFunctor_obj_injective φ)

lemma firstSubdivision_isFinite {W : SemiSSet.{u}} (hW : W.IsFinite) :
    SemiSSet.IsFinite (firstSubdivision.obj W) := by
  obtain ⟨N, hN⟩ := hW.2
  letI : Finite (FaceCategory W) := finite_faceCategory_of_isFinite hW
  change SemiSSet.IsFinite
    (strictNerveSubfunctor (FaceCategory W) (faceDimension (W := W))).toFunctor
  exact strictNerveSubfunctor_isFinite (faceDimension (W := W))
    (fun x y => finite_faceCategory_hom x y) N (faceDimension_le_of_bound N hN)

/-- The second derived subdivision of a semi-simplicial set. -/
noncomputable def secondSubdivision : SemiSSet.{u} ⥤ SemiSSet.{u} :=
  firstSubdivision ⋙ firstSubdivision

lemma secondSubdivision_isFinite {W : SemiSSet.{u}} (hW : W.IsFinite) :
    SemiSSet.IsFinite (secondSubdivision.obj W) :=
  firstSubdivision_isFinite (firstSubdivision_isFinite hW)

lemma secondSubdivision_map_mono {W V : SemiSSet.{u}} (φ : W ⟶ V) [Mono φ] :
    Mono (secondSubdivision.map φ) := by
  let ψ : firstSubdivision.obj W ⟶ firstSubdivision.obj V := firstSubdivision.map φ
  haveI : Mono ψ := firstSubdivision_map_mono φ
  change Mono (firstSubdivision.map ψ)
  exact firstSubdivision_map_mono ψ

lemma secondSubdivision_obj_isSimplicialComplex (W : SemiSSet.{u}) :
    (secondSubdivision.obj W).IsSimplicialComplex := by
  let V := firstSubdivision.obj W
  let C := FaceCategory V
  let rank : C → ℕ := faceDimension (W := V)
  letI : Quiver.IsThin C := by
    simpa [C, V] using firstSubdivision_faceCategory_isThin W
  change SemiSSet.IsSimplicialComplex
    ((strictNerveSubfunctor C rank).toFunctor)
  constructor
  · intro n σ i j hij
    have hzero := simplexChar_vertex_eq_zeroFace σ σ i j hij
    let x := strictNerveTopSimplex rank n σ
    have hobj : x.obj i = x.obj j := by
      have hv := congrArg Subtype.val hzero
      rw [strictNerveTopSimplex_vertex rank n σ i,
        strictNerveTopSimplex_vertex rank n σ j] at hv
      have h := congrArg (fun z : ComposableArrows C 0 => z.obj' 0) hv
      simpa [x] using h
    exact (strictNerveTopSimplex_strictMono rank n σ).injective
      (congrArg rank hobj)
  · intro n σ τ hRange
    let vσ : Fin (n + 1) → (strictNerveSubfunctor C rank).toFunctor.obj
        (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk 0)) :=
      fun i => σ.app (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk 0))
        (ULift.up (vertexInclusionAt
          (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) i))
    let vτ : Fin (n + 1) → (strictNerveSubfunctor C rank).toFunctor.obj
        (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk 0)) :=
      fun i => τ.app (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk 0))
        (ULift.up (vertexInclusionAt
          (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) i))
    let pσ : Fin (n + 1) → SemiSSet.realization.{u}.obj
        ((strictNerveSubfunctor C rank).toFunctor) := fun i =>
      (SemiSSet.simplexChar σ).hom (SemiSSet.simplexVertex i)
    let pτ : Fin (n + 1) → SemiSSet.realization.{u}.obj
        ((strictNerveSubfunctor C rank).toFunctor) := fun i =>
      (SemiSSet.simplexChar τ).hom (SemiSSet.simplexVertex i)
    let rmap := (realizationVertexSupport.{u}.app
      (strictNerveSubfunctor C rank).toFunctor).hom
    have hσsupport : ∀ i,
        rmap (pσ i) =
        Set.singleton (vσ i) := by
      intro i
      exact realizationVertexSupport_simplexChar_vertex σ i
    have hτsupport : ∀ i,
        rmap (pτ i) =
        Set.singleton (vτ i) := by
      intro i
      exact realizationVertexSupport_simplexChar_vertex τ i
    have hσfun :
        (fun i => rmap (pσ i)) =
          fun i => Set.singleton (vσ i) := funext hσsupport
    have hτfun :
        (fun i => rmap (pτ i)) =
          fun i => Set.singleton (vτ i) := funext hτsupport
    have hσimage : rmap '' Set.range pσ = Set.range (fun i => Set.singleton (vσ i)) := by
      rw [← Set.range_comp' rmap pσ]
      exact congrArg Set.range hσfun
    have hτimage : rmap '' Set.range pτ = Set.range (fun i => Set.singleton (vτ i)) := by
      rw [← Set.range_comp' rmap pτ]
      exact congrArg Set.range hτfun
    have hSingletonRange :
        Set.range (fun i => Set.singleton (vσ i)) =
          Set.range (fun i => Set.singleton (vτ i)) := by
      exact hσimage.symm.trans
        ((congrArg (fun s => rmap '' s) hRange).trans hτimage)
    have hVertexRange : Set.range vσ = Set.range vτ := by
      apply Set.ext
      intro z
      constructor
      · rintro ⟨i, rfl⟩
        have hz : Set.singleton (vσ i) ∈ Set.range (fun j => Set.singleton (vτ j)) :=
          hSingletonRange ▸ Set.mem_range.mpr ⟨i, rfl⟩
        rcases Set.mem_range.mp hz with ⟨j, hj⟩
        exact ⟨j, Set.singleton_injective hj⟩
      · rintro ⟨j, rfl⟩
        have hz : Set.singleton (vτ j) ∈ Set.range (fun i => Set.singleton (vσ i)) :=
          hSingletonRange.symm ▸ Set.mem_range.mpr ⟨j, rfl⟩
        rcases Set.mem_range.mp hz with ⟨i, hi⟩
        exact ⟨i, Set.singleton_injective hi⟩
    let vertexObject :
        (strictNerveSubfunctor C rank).toFunctor.obj
          (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk 0)) → C :=
      fun z => z.1.obj' 0
    let xσ := strictNerveTopSimplex rank n σ
    let xτ := strictNerveTopSimplex rank n τ
    have hxσ : (fun i => xσ.obj i) = fun i => vertexObject (vσ i) := by
      funext i
      have hv := strictNerveTopSimplex_vertex rank n σ i
      have h := congrArg (fun z : ComposableArrows C 0 => z.obj' 0) hv
      simpa [vertexObject, xσ, vσ] using h.symm
    have hxτ : (fun i => xτ.obj i) = fun i => vertexObject (vτ i) := by
      funext i
      have hv := strictNerveTopSimplex_vertex rank n τ i
      have h := congrArg (fun z : ComposableArrows C 0 => z.obj' 0) hv
      simpa [vertexObject, xτ, vτ] using h.symm
    have hChainRange : Set.range xσ.obj = Set.range xτ.obj := by
      calc
        _ = Set.range (fun i => vertexObject (vσ i)) := congrArg Set.range hxσ
        _ = Set.image vertexObject (Set.range vσ) := Set.range_comp' _ _
        _ = Set.image vertexObject (Set.range vτ) := congrArg _ hVertexRange
        _ = Set.range (fun i => vertexObject (vτ i)) := (Set.range_comp' _ _).symm
        _ = Set.range xτ.obj := congrArg Set.range hxτ.symm
    exact strictNerve_simplex_eq_of_vertex_range rank n σ τ hChainRange

/-- The terminal original face carried by a simplex in the second derived subdivision. -/
noncomputable def secondSubdivisionTerminalFace {W : SemiSSet.{u}} {n : ℕ}
    (σ : SemiSSet.stdSimplex.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) ⟶ secondSubdivision.obj W) :
    FaceCategory W := by
  let V := firstSubdivision.obj W
  let chain := strictNerveTopSimplex (faceDimension (W := V)) n σ
  let outer := chain.obj (Fin.last n)
  let m := outer.unop.obj.unop.obj.len
  let inner := outer.unop.val.1
  exact inner.obj (Fin.last m)

/-- The terminal face, expressed as a simplex map into the original semi-simplicial set. -/
noncomputable def secondSubdivisionTerminalSimplexMap {W : SemiSSet.{u}} {n : ℕ}
    (σ : SemiSSet.stdSimplex.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) ⟶ secondSubdivision.obj W) :
    Σ m : ℕ, SemiSSet.stdSimplex.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m) ⟶ W := by
  let p := standardizeFaceObject (secondSubdivisionTerminalFace σ)
  exact ⟨p.1, CategoryTheory.uliftYonedaEquiv.{u}.symm p.2⟩

/-- The affine extension of a vertex map between topological simplices on arbitrary objects. -/
noncomputable def vertexMapAt
    (s t : HomotopyHypothesis.Henry.SemiSimplexCategory)
    (v : Fin ((HomotopyHypothesis.Henry.SemiSimplexCategory.incl.obj s).len + 1) →
      Fin ((HomotopyHypothesis.Henry.SemiSimplexCategory.incl.obj t).len + 1)) :
    SemiSSet.toTop.{u}.obj s ⟶ SemiSSet.toTop.{u}.obj t :=
  TopCat.uliftFunctor.{u}.map
    (TopCat.ofHom ⟨StdSimplex.map (R := ℝ) v, StdSimplex.continuous_map ℝ v⟩)

lemma toTop_comp_vertexMapAt
    (r s t : HomotopyHypothesis.Henry.SemiSimplexCategory) (f : r ⟶ s)
    (v : Fin ((HomotopyHypothesis.Henry.SemiSimplexCategory.incl.obj s).len + 1) →
      Fin ((HomotopyHypothesis.Henry.SemiSimplexCategory.incl.obj t).len + 1)) :
    SemiSSet.toTop.{u}.map f ≫ vertexMapAt s t v =
      vertexMapAt r t (fun i => v
        (SimplexCategory.Hom.toOrderHom
          (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map f) i)) := by
  let α := SimplexCategory.Hom.toOrderHom
    (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map f)
  ext x
  rw [CategoryTheory.comp_apply]
  change ULift.up (StdSimplex.map (R := ℝ) v
      (StdSimplex.map (R := ℝ) α x.down)) =
    ULift.up (StdSimplex.map (R := ℝ) (fun i => v (α i)) x.down)
  exact congrArg ULift.up
    (congrFun (StdSimplex.map_comp' (R := ℝ) α v) x.down).symm

lemma vertexMapAt_comp_toTop
    (r s t : HomotopyHypothesis.Henry.SemiSimplexCategory) (f : s ⟶ t)
    (v : Fin ((HomotopyHypothesis.Henry.SemiSimplexCategory.incl.obj r).len + 1) →
      Fin ((HomotopyHypothesis.Henry.SemiSimplexCategory.incl.obj s).len + 1)) :
    vertexMapAt r s v ≫ SemiSSet.toTop.{u}.map f =
      vertexMapAt r t (fun i =>
        SimplexCategory.Hom.toOrderHom
          (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map f) (v i)) := by
  let α := SimplexCategory.Hom.toOrderHom
    (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map f)
  ext x
  rw [CategoryTheory.comp_apply]
  change ULift.up (StdSimplex.map (R := ℝ) α
      (StdSimplex.map (R := ℝ) v x.down)) =
    ULift.up (StdSimplex.map (R := ℝ) (fun i => α (v i)) x.down)
  exact congrArg ULift.up
    (congrFun (StdSimplex.map_comp' (R := ℝ) v α) x.down).symm

/-- The last-vertex affine map on a simplex in the first derived subdivision. -/
noncomputable def firstSubdivisionLastVertexFamily {W : SemiSSet.{u}} {n : ℕ}
    (σ : SemiSSet.stdSimplex.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) ⟶ firstSubdivision.obj W) :
    SemiSSet.toTop.{u}.obj (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) ⟶
      SemiSSet.realization.{u}.obj W := by
  let x := strictNerveTopSimplex (faceDimension (W := W)) n σ
  let c := x.obj (Fin.last n)
  let s := c.unop.obj.unop
  let v : Fin (n + 1) → Fin ((SemiSimplexCategory.incl.obj s).len + 1) := fun i =>
    (SimplexCategory.Hom.toOrderHom
      (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map
        (faceCategoryArrowUnderlying (x.map (CategoryTheory.homOfLE (Fin.le_last i)))))
      (Fin.last (faceDimension (x.obj i))))
  exact vertexMapAt (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) s v ≫
    faceObjectSimplexChar c

end HomotopyHypothesis.Simplicial.BarycentricSubdivision
