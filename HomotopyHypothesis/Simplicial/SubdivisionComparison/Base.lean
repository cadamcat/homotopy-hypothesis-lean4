import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Simplicial.BarycentricSubdivision.DerivedSubdivision
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.Code
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Inst42
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Rank
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.Map
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdCos
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdLan
universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Simplicial.SubdivisionComparison

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- The increasing enumeration of a nonempty face of a standard simplex. -/
def stdFaceMap {k : ℕ} (S : Finset (Fin (k + 1))) (hS : S.Nonempty) :
    HomotopyHypothesis.Henry.SemiSimplexCategory.mk (S.card - 1) ⟶ HomotopyHypothesis.Henry.SemiSimplexCategory.mk k :=
  let e := S.orderEmbOfFin (by
    have hc : 1 ≤ S.card := Finset.card_pos.mpr hS
    exact (Nat.sub_add_cancel hc).symm)
  let f : (HomotopyHypothesis.Henry.SemiSimplexCategory.mk (S.card - 1)).obj ⟶
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk k).obj :=
    SimplexCategory.Hom.mk (OrderEmbedding.toOrderHom e)
  have hf : Mono f := by
    rw [SimplexCategory.mono_iff_injective]
    exact e.injective
  ⟨f, hf⟩

/-- The object of the face category determined by a nonempty face of a standard simplex. -/
noncomputable def stdFaceObject {k : ℕ} (S : Finset (Fin (k + 1))) (hS : S.Nonempty) :
    Simplicial.BarycentricSubdivision.FaceCategory (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj (HomotopyHypothesis.Henry.SemiSimplexCategory.mk k)) :=
  Opposite.op (Functor.Elements.mk (F := HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj (HomotopyHypothesis.Henry.SemiSimplexCategory.mk k))
    (obj := Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk (S.card - 1)))
    (ULift.up (stdFaceMap S hS)))

lemma faceDimension_stdFaceObject {k : ℕ} (S : Finset (Fin (k + 1))) (hS : S.Nonempty) :
    Simplicial.BarycentricSubdivision.faceDimension (W := HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj (HomotopyHypothesis.Henry.SemiSimplexCategory.mk k))
      (stdFaceObject S hS) = S.card - 1 := rfl

/-- The order embedding induced by inclusion of finite subsets. -/
def finsetSubsetOrderEmbedding {α : Type} [PartialOrder α] {S T : Finset α}
    (hST : S ⊆ T) : S ↪o T where
  toFun x := ⟨x.1, hST x.2⟩
  inj' _ _ h := by
    apply Subtype.ext
    exact congrArg (fun z : T => (z : α)) h
  map_rel_iff' := by
    intro a b
    rfl

/-- The cardinality witness used to enumerate the vertices of a nonempty face. -/
theorem stdFaceCardEq {k : ℕ} (S : Finset (Fin (k + 1))) (hS : S.Nonempty) :
    S.card = S.card - 1 + 1 := by
  have hc : 1 ≤ S.card := Finset.card_pos.mpr hS
  exact (Nat.sub_add_cancel hc).symm

/-- The face inclusion represented between the increasing enumerations of two nested faces. -/
def stdFaceInclusionMap {k : ℕ} (S T : Finset (Fin (k + 1)))
    (hS : S.Nonempty) (hT : T.Nonempty) (hST : S ⊆ T) :
    HomotopyHypothesis.Henry.SemiSimplexCategory.mk (S.card - 1) ⟶
      HomotopyHypothesis.Henry.SemiSimplexCategory.mk (T.card - 1) := by
  let e := (S.orderIsoOfFin (stdFaceCardEq S hS)).toOrderEmbedding.trans
    ((finsetSubsetOrderEmbedding hST).trans
      ((T.orderIsoOfFin (stdFaceCardEq T hT)).symm.toOrderEmbedding))
  let f : (HomotopyHypothesis.Henry.SemiSimplexCategory.mk (S.card - 1)).obj ⟶
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk (T.card - 1)).obj :=
    SimplexCategory.Hom.mk (OrderEmbedding.toOrderHom e)
  have hf : Mono f := by
    rw [SimplexCategory.mono_iff_injective]
    exact e.injective
  exact ⟨f, hf⟩

lemma stdFaceInclusion_comp_stdFaceMap {k : ℕ} (S T : Finset (Fin (k + 1)))
    (hS : S.Nonempty) (hT : T.Nonempty) (hST : S ⊆ T) :
    stdFaceInclusionMap S T hS hT hST ≫ stdFaceMap T hT = stdFaceMap S hS := by
  apply CategoryTheory.WideSubcategory.hom_ext
  apply SimplexCategory.Hom.ext
  ext i
  dsimp [stdFaceMap, stdFaceInclusionMap]
  simp only [OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe,
    RelEmbedding.trans_apply, Finset.orderEmbOfFin,
    OrderEmbedding.subtype_apply, OrderIso.coe_toOrderEmbedding,
    OrderIso.apply_symm_apply, finsetSubsetOrderEmbedding,
    Function.comp_apply]
  rfl

/-- A nested pair of faces gives the corresponding arrow in the face category. -/
noncomputable def stdFaceArrow {k : ℕ} (S T : Finset (Fin (k + 1)))
    (hS : S.Nonempty) (hT : T.Nonempty) (hST : S ⊆ T) :
    stdFaceObject S hS ⟶ stdFaceObject T hT :=
  (Functor.Elements.homMk
    (F := HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk k))
    (Opposite.op (stdFaceInclusionMap S T hS hT hST))
    (by
      apply ULift.ext
      change stdFaceInclusionMap S T hS hT hST ≫ stdFaceMap T hT = stdFaceMap S hS
      exact stdFaceInclusion_comp_stdFaceMap S T hS hT hST)).op

/-- Every vertex of the derived simplex is the barycentre of a nonempty face. -/
lemma sdSimplex_vertex_isMid {k n : ℕ}
    (x : (HomotopyHypothesis.Approximation.Topological.sdComplex k).Simplex n)
    (i : Fin (n + 1)) :
    ∃ S : Finset (Fin (k + 1)), x.1 i = HomotopyHypothesis.Approximation.Topological.PV.mid S := by
  cases h : x.1 i with
  | top j =>
    have hm : HomotopyHypothesis.Approximation.Topological.PV.top j ∈ Finset.univ.image x.1 :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h⟩
    exact False.elim (x.2.2.2 j hm)
  | mid S => exact ⟨S, rfl⟩

/-- The face labeling a vertex in a simplex of the derived standard simplex. -/
noncomputable def sdSimplexFace {k n : ℕ}
    (x : (HomotopyHypothesis.Approximation.Topological.sdComplex k).Simplex n)
    (i : Fin (n + 1)) : Finset (Fin (k + 1)) :=
  Classical.choose (sdSimplex_vertex_isMid x i)

lemma sdSimplexFace_spec {k n : ℕ}
    (x : (HomotopyHypothesis.Approximation.Topological.sdComplex k).Simplex n)
    (i : Fin (n + 1)) :
    x.1 i = HomotopyHypothesis.Approximation.Topological.PV.mid (sdSimplexFace x i) :=
  Classical.choose_spec (sdSimplex_vertex_isMid x i)

lemma sdSimplexFace_nonempty {k n : ℕ}
    (x : (HomotopyHypothesis.Approximation.Topological.sdComplex k).Simplex n)
    (i : Fin (n + 1)) : (sdSimplexFace x i).Nonempty := by
  have hm : HomotopyHypothesis.Approximation.Topological.PV.mid (sdSimplexFace x i) ∈
      Finset.univ.image x.1 :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, sdSimplexFace_spec x i⟩
  exact (x.2.2.1).1 _ hm

lemma sdSimplexFace_ssubset_of_lt {k n : ℕ}
    (x : (HomotopyHypothesis.Approximation.Topological.sdComplex k).Simplex n)
    {i j : Fin (n + 1)} (hij : i < j) :
    sdSimplexFace x i ⊂ sdSimplexFace x j := by
  let S := sdSimplexFace x i
  let T := sdSimplexFace x j
  have hmS : HomotopyHypothesis.Approximation.Topological.PV.mid S ∈ Finset.univ.image x.1 :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, sdSimplexFace_spec x i⟩
  have hmT : HomotopyHypothesis.Approximation.Topological.PV.mid T ∈ Finset.univ.image x.1 :=
    Finset.mem_image.mpr ⟨j, Finset.mem_univ _, sdSimplexFace_spec x j⟩
  have hlt := x.2.1 hij
  rw [sdSimplexFace_spec x i, sdSimplexFace_spec x j] at hlt
  change HomotopyHypothesis.Approximation.Topological.PV.mid S <
    HomotopyHypothesis.Approximation.Topological.PV.mid T at hlt
  rcases (x.2.2.1).2.1 S T hmS hmT with hST | hTS
  · refine Finset.ssubset_iff_subset_ne.mpr ⟨hST, ?_⟩
    intro hEq
    change S = T at hEq
    rw [hEq] at hlt
    exact (lt_irrefl _ hlt)
  · have hcardle : S.card ≤ T.card := by
      have hrank : HomotopyHypothesis.Approximation.Topological.PV.rank
          (HomotopyHypothesis.Approximation.Topological.PV.mid S) <
          HomotopyHypothesis.Approximation.Topological.PV.rank (HomotopyHypothesis.Approximation.Topological.PV.mid T) := by
        change HomotopyHypothesis.Approximation.Topological.PV.rank
            (HomotopyHypothesis.Approximation.Topological.PV.mid S) <
          HomotopyHypothesis.Approximation.Topological.PV.rank (HomotopyHypothesis.Approximation.Topological.PV.mid T) at hlt
        exact hlt
      have houter : toLex (1, toLex (S.card, HomotopyHypothesis.Approximation.Topological.DV.code S)) <
          toLex (1, toLex (T.card, HomotopyHypothesis.Approximation.Topological.DV.code T)) := by
        simpa [HomotopyHypothesis.Approximation.Topological.PV.rank] using hrank
      have hinner : toLex (S.card, HomotopyHypothesis.Approximation.Topological.DV.code S) <
          toLex (T.card, HomotopyHypothesis.Approximation.Topological.DV.code T) :=
        (Prod.Lex.toLex_lt_toLex'.mp houter).2 rfl
      exact (Prod.Lex.toLex_lt_toLex'.mp hinner).1
    have hcardrev : T.card ≤ S.card := Finset.card_le_card hTS
    have hcard : S.card = T.card := Nat.le_antisymm hcardle hcardrev
    have hEq : T = S := Finset.eq_of_subset_of_card_le hTS hcard.le
    change T = S at hEq
    rw [hEq] at hlt
    exact False.elim (lt_irrefl _ hlt)

/-- The strict chain of faces represented by a simplex of the derived standard simplex. -/
noncomputable def stdFaceChain {k n : ℕ}
    (S : Fin (n + 1) → Finset (Fin (k + 1)))
    (hS : ∀ i, (S i).Nonempty)
    (hsub : ∀ i : Fin n, S i.castSucc ⊆ S i.succ) :
    ComposableArrows (Simplicial.BarycentricSubdivision.FaceCategory
      (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk k))) n :=
  ComposableArrows.mkOfObjOfMapSucc
    (fun i => stdFaceObject (S i) (hS i))
    (fun i => stdFaceArrow (S i.castSucc) (S i.succ)
      (hS i.castSucc) (hS i.succ) (hsub i))

lemma stdFaceChain_dimension {k n : ℕ}
    (S : Fin (n + 1) → Finset (Fin (k + 1)))
    (hS : ∀ i, (S i).Nonempty)
    (hsub : ∀ i : Fin n, S i.castSucc ⊆ S i.succ)
    (i : Fin (n + 1)) :
    Simplicial.BarycentricSubdivision.faceDimension (stdFaceChain S hS hsub |>.obj i) = (S i).card - 1 := by
  simp [stdFaceChain, faceDimension_stdFaceObject]

lemma sdSimplexFace_card_strictMono {k n : ℕ}
    (x : (HomotopyHypothesis.Approximation.Topological.sdComplex k).Simplex n) :
    StrictMono (fun i : Fin (n + 1) => (sdSimplexFace x i).card) := by
  intro i j hij
  exact Finset.card_lt_card (sdSimplexFace_ssubset_of_lt x hij)

noncomputable def sdSimplexFaceChain {k n : ℕ}
    (x : (HomotopyHypothesis.Approximation.Topological.sdComplex k).Simplex n) :
    ComposableArrows (Simplicial.BarycentricSubdivision.FaceCategory
      (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk k))) n :=
  stdFaceChain (sdSimplexFace x) (sdSimplexFace_nonempty x)
    (fun _i => (sdSimplexFace_ssubset_of_lt x Fin.castSucc_lt_succ).subset)

lemma sdSimplexFaceChain_dimension_strictMono {k n : ℕ}
    (x : (HomotopyHypothesis.Approximation.Topological.sdComplex k).Simplex n) :
    StrictMono (fun i : Fin (n + 1) =>
      Simplicial.BarycentricSubdivision.faceDimension (sdSimplexFaceChain x |>.obj i)) := by
  intro i j hij
  simp only [sdSimplexFaceChain, stdFaceChain_dimension]
  have hcard := sdSimplexFace_card_strictMono x hij
  have hi : 1 ≤ (sdSimplexFace x i).card := Finset.card_pos.mpr (sdSimplexFace_nonempty x i)
  exact Nat.sub_lt_sub_right hi hcard

/-- The simplex of the strict face nerve determined by a derived simplex. -/
noncomputable def sdSimplexNerveValue {k n : ℕ}
    (x : (HomotopyHypothesis.Approximation.Topological.sdComplex k).Simplex n) :
    (Simplicial.BarycentricSubdivision.firstSubdivision.obj
      (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk k))).obj
      (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)) :=
  ⟨sdSimplexFaceChain x, sdSimplexFaceChain_dimension_strictMono x⟩

lemma semiSimplexCategory_hom_mono
    {a b : HomotopyHypothesis.Henry.SemiSimplexCategory} (f : a ⟶ b) : Mono f := by
  constructor
  intro c g h hgh
  apply CategoryTheory.WideSubcategory.hom_ext
  haveI : Mono f.1 := f.property
  apply (cancel_mono f.1).1
  simpa using congrArg (fun q => q.1) hgh

lemma stdSimplex_map_mono {a b : HomotopyHypothesis.Henry.SemiSimplexCategory}
    (f : a ⟶ b) [Mono f] :
    Mono (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.map f) := by
  apply NatTrans.mono_of_mono_app

lemma faceObjectSimplexMap_eq_stdSimplex_map {k : ℕ}
    (x : Simplicial.BarycentricSubdivision.FaceCategory
      (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk k))) :
    Simplicial.BarycentricSubdivision.faceObjectSimplexMap x =
      HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.map x.unop.val.down := by
  apply CategoryTheory.uliftYonedaEquiv.{u}.injective
  simp only [Simplicial.BarycentricSubdivision.faceObjectSimplexMap,
    HomotopyHypothesis.Henry.SemiSSet.stdSimplex,
    Equiv.apply_symm_apply,
    CategoryTheory.uliftYonedaEquiv_uliftYoneda_map]

lemma standardSimplexFaceCategory_isThin (k : ℕ) :
    Quiver.IsThin (Simplicial.BarycentricSubdivision.FaceCategory
      (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk k))) := by
  intro x y
  refine ⟨?_⟩
  intro f g
  let α := Simplicial.BarycentricSubdivision.faceCategoryArrowUnderlying f
  let β := Simplicial.BarycentricSubdivision.faceCategoryArrowUnderlying g
  let ψ := Simplicial.BarycentricSubdivision.faceObjectSimplexMap y
  letI : Mono y.unop.val.down := semiSimplexCategory_hom_mono _
  haveI : Mono ψ := by
    change Mono (Simplicial.BarycentricSubdivision.faceObjectSimplexMap y)
    rw [faceObjectSimplexMap_eq_stdSimplex_map]
    exact stdSimplex_map_mono _
  have hα := Simplicial.BarycentricSubdivision.faceObjectSimplexMap_naturality f
  have hβ := Simplicial.BarycentricSubdivision.faceObjectSimplexMap_naturality g
  have hmap : HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.map α =
      HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.map β := by
    apply (cancel_mono ψ).1
    calc
      HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.map α ≫ ψ =
          Simplicial.BarycentricSubdivision.faceObjectSimplexMap x := hα
      _ = HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.map β ≫ ψ := hβ.symm
  apply Quiver.Hom.unop_inj
  apply Functor.Elements.hom_ext
  apply Opposite.unop_injective
  exact HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.map_injective hmap

lemma sdSimplexFace_restrict {k : ℕ} {s t : HomotopyHypothesis.Henry.SemiSimplexCategory}
    (f : s ⟶ t)
    (x : ULift ((HomotopyHypothesis.Approximation.Topological.sdComplex k).Simplex t.obj.len))
    (i : Fin (s.obj.len + 1)) :
    sdSimplexFace
      (((HomotopyHypothesis.Approximation.Topological.sdComplex k).toSemiSSet.{u}.map
        (Opposite.op f)) x).down i =
      sdSimplexFace x.down
        (SimplexCategory.Hom.toOrderHom
          (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map f) i) := by
  let x' : (HomotopyHypothesis.Approximation.Topological.sdComplex k).Simplex s.obj.len :=
    (((HomotopyHypothesis.Approximation.Topological.sdComplex k).toSemiSSet.{u}.map
      (Opposite.op f)) x).down
  apply HomotopyHypothesis.Approximation.Topological.PV.mid.inj
  have hleft := sdSimplexFace_spec x' i
  have hright := sdSimplexFace_spec x.down
    (SimplexCategory.Hom.toOrderHom
      (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map f) i)
  have hvertex : x'.1 i = x.down.1
      (SimplexCategory.Hom.toOrderHom
        (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map f) i) := rfl
  rw [hvertex] at hleft
  exact hleft.symm.trans hright

noncomputable def sdSimplexNerveValueAt {k : ℕ}
    {a : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ}
    (x : (HomotopyHypothesis.Approximation.Topological.sdComplex k).Simplex a.unop.obj.len) :
    (Simplicial.BarycentricSubdivision.firstSubdivision.obj
      (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk k))).obj a :=
  ⟨sdSimplexFaceChain x, sdSimplexFaceChain_dimension_strictMono x⟩

noncomputable def sdStandardToFirstSubdivision (k : ℕ) :
    (HomotopyHypothesis.Approximation.Topological.sdComplex k).toSemiSSet.{u} ⟶
      Simplicial.BarycentricSubdivision.firstSubdivision.obj
        (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
          (HomotopyHypothesis.Henry.SemiSimplexCategory.mk k)) := by
  classical
  letI : Quiver.IsThin (Simplicial.BarycentricSubdivision.FaceCategory
      (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk k))) :=
    standardSimplexFaceCategory_isThin k
  refine { app := fun a => TypeCat.ofHom (fun x => sdSimplexNerveValueAt (a := a) x.down), naturality := ?_ }
  intro a b f
  apply TypeCat.homEquiv.injective
  funext x
  apply Subtype.ext
  change sdSimplexFaceChain
      (((HomotopyHypothesis.Approximation.Topological.sdComplex k).toSemiSSet.{u}.map f) x).down =
    (sdSimplexFaceChain x.down).whiskerLeft
      (SimplexCategory.toCat.map
        (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map f.unop)).toFunctor
  refine CategoryTheory.Functor.ext (fun i => ?_) ?_
  · simp only [sdSimplexFaceChain, stdFaceChain,
      CategoryTheory.ComposableArrows.mkOfObjOfMapSucc_obj]
    have hface : sdSimplexFace
        (((HomotopyHypothesis.Approximation.Topological.sdComplex k).toSemiSSet.{u}.map f) x).down i =
        sdSimplexFace x.down
          (SimplexCategory.Hom.toOrderHom
            (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map f.unop) i) := by
      exact sdSimplexFace_restrict (f := f.unop) (x := x) (i := i)
    simp only [hface]
    change stdFaceObject (sdSimplexFace x.down
        (SimplexCategory.Hom.toOrderHom
          (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map f.unop) i)) _ =
      stdFaceObject (sdSimplexFace x.down
        ((SimplexCategory.toCat.map
          (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map f.unop)).toFunctor.obj i)) _
    have hindex :
        (SimplexCategory.toCat.map
          (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map f.unop)).toFunctor.obj i =
          SimplexCategory.Hom.toOrderHom
            (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map f.unop) i := by
      simp [SimplexCategory.toCat]
      rfl
    rw [hindex]
  · intro i j g
    exact Subsingleton.elim _ _

noncomputable def sdStandardMapAt (s : HomotopyHypothesis.Henry.SemiSimplexCategory) :
    HomotopyHypothesis.Approximation.Topological.sdCos.{u}.obj s ⟶
      (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u} ⋙
        Simplicial.BarycentricSubdivision.firstSubdivision.{u}).obj s :=
  sdStandardToFirstSubdivision s.obj.len

lemma sdSimplexFace_cosMap {k l : ℕ}
    (θ : HomotopyHypothesis.Henry.SemiSimplexCategory.mk k ⟶
      HomotopyHypothesis.Henry.SemiSimplexCategory.mk l)
    (a : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ)
    (x : ULift ((HomotopyHypothesis.Approximation.Topological.sdComplex k).Simplex a.unop.obj.len))
    (i : Fin (a.unop.obj.len + 1)) :
    sdSimplexFace
      (((HomotopyHypothesis.Approximation.Topological.sdCos.{u}.map θ).app a x).down)
      i =
      (sdSimplexFace x.down i).image θ.1.toOrderHom := by
  let y := (((HomotopyHypothesis.Approximation.Topological.sdCos.{u}.map θ).app a x).down)
  have hvertex : y.1 i = HomotopyHypothesis.Approximation.Topological.PV.map
      θ.1.toOrderHom (x.down.1 i) := by
    change (HomotopyHypothesis.Approximation.Topological.PV.map
      (SimplexCategory.Hom.toOrderHom
        (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map θ)) ∘ x.down.1) i = _
    rfl
  have hmid : y.1 i = HomotopyHypothesis.Approximation.Topological.PV.mid
      ((sdSimplexFace x.down i).image θ.1.toOrderHom) := by
    rw [hvertex, sdSimplexFace_spec x.down i]
    rfl
  apply (HomotopyHypothesis.Approximation.Topological.PV.mid.inj)
  have hspec := sdSimplexFace_spec y i
  exact (hmid.symm.trans hspec).symm

lemma stdFaceMap_factorization {k l : ℕ}
    (θ : HomotopyHypothesis.Henry.SemiSimplexCategory.mk k ⟶
      HomotopyHypothesis.Henry.SemiSimplexCategory.mk l)
    (S : Finset (Fin (k + 1))) (hS : S.Nonempty)
    (hImage : (S.image θ.1.toOrderHom).Nonempty)
    (e : HomotopyHypothesis.Henry.SemiSimplexCategory.mk
        ((S.image θ.1.toOrderHom).card - 1) ⟶
      HomotopyHypothesis.Henry.SemiSimplexCategory.mk (S.card - 1)) :
    e ≫ stdFaceMap S hS ≫ θ =
      stdFaceMap (S.image θ.1.toOrderHom) hImage := by
  let t : Fin (k + 1) → Fin (l + 1) := θ.1.toOrderHom
  let g := e ≫ stdFaceMap S hS ≫ θ
  have ht : StrictMono t := by
    change StrictMono (SimplexCategory.Hom.toOrderHom θ.1)
    exact HomotopyHypothesis.Approximation.Topological.SemiSimplexCategory.strictMono θ
  have hcompval (i : Fin ((S.image t).card - 1 + 1)) :
      g.1.toOrderHom i =
        t (S.orderEmbOfFin (stdFaceCardEq S hS)
          ((SimplexCategory.Hom.toOrderHom
            (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map e)) i)) := by
    dsimp [g]
    simp [stdFaceMap, SimplexCategory.comp_toOrderHom, Functor.map_comp,
      OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe, Function.comp_apply]
    rfl
  have hmem : ∀ i : Fin ((S.image t).card - 1 + 1),
      g.1.toOrderHom i ∈ S.image t := by
    intro i
    rw [hcompval i]
    exact Finset.mem_image.mpr ⟨S.orderEmbOfFin (stdFaceCardEq S hS)
      ((SimplexCategory.Hom.toOrderHom
        (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map e)) i),
      Finset.orderEmbOfFin_mem S (stdFaceCardEq S hS)
        ((SimplexCategory.Hom.toOrderHom
          (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map e)) i), rfl⟩
  have hfun : (fun i : Fin ((S.image t).card - 1 + 1) => g.1.toOrderHom i) =
      (S.image t).orderEmbOfFin (stdFaceCardEq (S.image t) hImage) :=
    Finset.orderEmbOfFin_unique (stdFaceCardEq (S.image t) hImage) hmem
      (HomotopyHypothesis.Approximation.Topological.SemiSimplexCategory.strictMono g)
  have hOrder :
      SimplexCategory.Hom.toOrderHom
          (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map g) =
        OrderEmbedding.toOrderHom
          ((S.image t).orderEmbOfFin (stdFaceCardEq (S.image t) hImage)) := by
    apply OrderHom.ext
    exact hfun
  apply CategoryTheory.WideSubcategory.hom_ext
  apply SimplexCategory.Hom.ext
  exact hOrder

lemma stdFaceObject_map {k l : ℕ}
    (θ : HomotopyHypothesis.Henry.SemiSimplexCategory.mk k ⟶
      HomotopyHypothesis.Henry.SemiSimplexCategory.mk l)
    (S : Finset (Fin (k + 1))) (hS : S.Nonempty) :
    (Simplicial.BarycentricSubdivision.faceFunctor
      (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.map θ)).obj
        (stdFaceObject S hS) =
      stdFaceObject (S.image θ.1.toOrderHom) (by
          rcases hS with ⟨i, hi⟩
          exact ⟨_, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩) := by
  let t : Fin (k + 1) → Fin (l + 1) := θ.1.toOrderHom
  have ht : StrictMono t := by
    change StrictMono (SimplexCategory.Hom.toOrderHom θ.1)
    exact HomotopyHypothesis.Approximation.Topological.SemiSimplexCategory.strictMono θ
  have hcard : (S.image t).card = S.card := Finset.card_image_of_injective S ht.injective
  have hdim : S.card - 1 = (S.image t).card - 1 := by rw [hcard]
  have hImage : (S.image t).Nonempty := by
    rcases hS with ⟨i, hi⟩
    exact ⟨t i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
  have hobj : Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk
      (S.card - 1)) = Opposite.op
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk ((S.image t).card - 1)) :=
    congrArg Opposite.op
      (congrArg HomotopyHypothesis.Henry.SemiSimplexCategory.mk hdim)
  apply Opposite.unop_injective
  refine Functor.Elements.ext _ _ hobj ?_
  apply ULift.ext
  dsimp [Simplicial.BarycentricSubdivision.faceFunctor, stdFaceObject]
  change (((HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk l)).map (eqToHom hobj))
      (((HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.map θ).app
        (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk (S.card - 1))))
        (ULift.up (stdFaceMap S hS)))).down =
    stdFaceMap (S.image t) hImage
  simpa [hobj, hdim, hcard, HomotopyHypothesis.Henry.SemiSSet.stdSimplex] using
    (stdFaceMap_factorization θ S hS hImage (eqToHom hobj).unop)

theorem sdStandardToFirstSubdivision_naturality {k l : ℕ}
    (θ : HomotopyHypothesis.Henry.SemiSimplexCategory.mk k ⟶
      HomotopyHypothesis.Henry.SemiSimplexCategory.mk l) :
    HomotopyHypothesis.Approximation.Topological.sdCos.{u}.map θ ≫
        sdStandardToFirstSubdivision l =
      sdStandardToFirstSubdivision k ≫
        (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u} ⋙
          Simplicial.BarycentricSubdivision.firstSubdivision.{u}).map θ := by
  letI : Quiver.IsThin (Simplicial.BarycentricSubdivision.FaceCategory
      (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk l))) :=
    standardSimplexFaceCategory_isThin l
  ext a x
  apply Subtype.ext
  change sdSimplexFaceChain
      (((HomotopyHypothesis.Approximation.Topological.sdCos.{u}.map θ).app a x).down) =
    ((Simplicial.BarycentricSubdivision.faceFunctor
      (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.map θ)).mapComposableArrows
        a.unop.obj.len).obj (sdSimplexFaceChain x.down)
  refine CategoryTheory.Functor.ext (fun i => ?_) ?_
  · have hface := sdSimplexFace_cosMap θ a x i
    change stdFaceObject
        (sdSimplexFace ((HomotopyHypothesis.Approximation.Topological.sdCos.{u}.map θ).app a x).down i) _ =
      (Simplicial.BarycentricSubdivision.faceFunctor
        (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.map θ)).obj
        (stdFaceObject (sdSimplexFace x.down i)
          (sdSimplexFace_nonempty x.down i))
    simpa only [hface] using
      (stdFaceObject_map θ (sdSimplexFace x.down i)
        (sdSimplexFace_nonempty x.down i)).symm
  · intro i j f
    exact Subsingleton.elim _ _

noncomputable def sdCosToFirstSubdivision :
    HomotopyHypothesis.Approximation.Topological.sdCos.{u} ⟶
      HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u} ⋙ Simplicial.BarycentricSubdivision.firstSubdivision.{u} where
  app s := sdStandardMapAt s
  naturality {s t} f := by
    let h_s : HomotopyHypothesis.Henry.SemiSimplexCategory.mk s.obj.len = s := by
      apply CategoryTheory.WideSubcategory.ext
      exact SimplexCategory.mk_len s.obj
    let h_t : HomotopyHypothesis.Henry.SemiSimplexCategory.mk t.obj.len = t := by
      apply CategoryTheory.WideSubcategory.ext
      exact SimplexCategory.mk_len t.obj
    cases h_s
    cases h_t
    exact sdStandardToFirstSubdivision_naturality f

/-- Extend the simplexwise comparison to every semi-simplicial set by the Kan-extension property. -/
noncomputable def sdLanToFirstSubdivision :
    HomotopyHypothesis.Approximation.Topological.sdLan.{u} ⟶ Simplicial.BarycentricSubdivision.firstSubdivision.{u} :=
  HomotopyHypothesis.Approximation.Topological.sdLan.{u}.descOfIsLeftKanExtension
    (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit
      HomotopyHypothesis.Approximation.Topological.sdCos.{u})
    Simplicial.BarycentricSubdivision.firstSubdivision.{u}
    sdCosToFirstSubdivision

/-- The vertices of a face in a strict face chain, expressed inside its terminal simplex. -/
def chainTerminalFaceArrow {W : HomotopyHypothesis.Henry.SemiSSet.{u}} {n : ℕ}
    (F : ComposableArrows (Simplicial.BarycentricSubdivision.FaceCategory W) n) (i : Fin (n + 1)) :
    (F.obj i).unop.obj.unop ⟶ (F.obj (Fin.last n)).unop.obj.unop :=
  Simplicial.BarycentricSubdivision.faceCategoryArrowUnderlying (F.map (CategoryTheory.homOfLE (Fin.le_last i)))

def faceChainSubset {W : HomotopyHypothesis.Henry.SemiSSet.{u}} {n : ℕ}
    (F : ComposableArrows (Simplicial.BarycentricSubdivision.FaceCategory W) n) (i : Fin (n + 1)) :
    Finset (Fin ((HomotopyHypothesis.Henry.SemiSimplexCategory.incl.obj
      ((F.obj (Fin.last n)).unop.obj.unop)).len + 1)) :=
  Finset.univ.image (SimplexCategory.Hom.toOrderHom
    (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map
      (chainTerminalFaceArrow F i)))

lemma faceChainSubset_nonempty {W : HomotopyHypothesis.Henry.SemiSSet.{u}} {n : ℕ}
    (F : ComposableArrows (Simplicial.BarycentricSubdivision.FaceCategory W) n)
    (i : Fin (n + 1)) : (faceChainSubset F i).Nonempty := by
  let q := SimplexCategory.Hom.toOrderHom
    (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map
      (chainTerminalFaceArrow F i))
  let v : Fin ((HomotopyHypothesis.Henry.SemiSimplexCategory.incl.obj
      ((F.obj i).unop.obj.unop)).len + 1) := 0
  refine ⟨q v, ?_⟩
  change q v ∈ Finset.univ.image q
  exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩

lemma faceChainSubset_card {W : HomotopyHypothesis.Henry.SemiSSet.{u}} {n : ℕ}
    (F : ComposableArrows (Simplicial.BarycentricSubdivision.FaceCategory W) n) (i : Fin (n + 1)) :
    (faceChainSubset F i).card = Simplicial.BarycentricSubdivision.faceDimension (W := W) (F.obj i) + 1 := by
  let α := chainTerminalFaceArrow F i
  have hmono : Mono (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map α) := by
    change Mono α.1
    exact α.property
  have hinj : Function.Injective
      (SimplexCategory.Hom.toOrderHom
        (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map α)) := by
    rw [← SimplexCategory.mono_iff_injective]
    exact hmono
  change (Finset.univ.image
      (SimplexCategory.Hom.toOrderHom
        (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map α))).card =
    Simplicial.BarycentricSubdivision.faceDimension (W := W) (F.obj i) + 1
  rw [Finset.card_image_of_injective Finset.univ hinj]
  rw [Finset.card_univ, Fintype.card_fin]
  simp [Simplicial.BarycentricSubdivision.semiSimplex_inclusion_length, Simplicial.BarycentricSubdivision.faceDimension]

lemma faceChainSubset_subset_of_le {W : HomotopyHypothesis.Henry.SemiSSet.{u}} {n : ℕ}
    (F : ComposableArrows (Simplicial.BarycentricSubdivision.FaceCategory W) n) {i j : Fin (n + 1)}
    (hij : i ≤ j) : faceChainSubset F i ⊆ faceChainSubset F j := by
  let β := F.map (CategoryTheory.homOfLE hij)
  have hbase : β ≫ F.map (CategoryTheory.homOfLE (Fin.le_last j)) =
      F.map (CategoryTheory.homOfLE (Fin.le_last i)) := by
    calc
      F.map (CategoryTheory.homOfLE hij) ≫
          F.map (CategoryTheory.homOfLE (Fin.le_last j)) =
        F.map (CategoryTheory.homOfLE hij ≫ CategoryTheory.homOfLE (Fin.le_last j)) :=
          (F.map_comp _ _).symm
      _ = F.map (CategoryTheory.homOfLE (Fin.le_last i)) := by
        congr 1
  have hfactor :
      chainTerminalFaceArrow F i =
        Simplicial.BarycentricSubdivision.faceCategoryArrowUnderlying β ≫ chainTerminalFaceArrow F j := by
    calc
      chainTerminalFaceArrow F i =
          Simplicial.BarycentricSubdivision.faceCategoryArrowUnderlying
            (β ≫ F.map (CategoryTheory.homOfLE (Fin.le_last j))) :=
          congrArg Simplicial.BarycentricSubdivision.faceCategoryArrowUnderlying hbase.symm
      _ = Simplicial.BarycentricSubdivision.faceCategoryArrowUnderlying β ≫ chainTerminalFaceArrow F j := by
          rfl
  let α_i := chainTerminalFaceArrow F i
  let α_j := chainTerminalFaceArrow F j
  let β' := Simplicial.BarycentricSubdivision.faceCategoryArrowUnderlying β
  have hq :
      HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map α_i =
        HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map β' ≫
          HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map α_j := by
    calc
      HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map α_i =
          HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map (β' ≫ α_j) := by
            dsimp [α_i, β']
            rw [hfactor]
            rfl
      _ = HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map β' ≫
          HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map α_j := by
            rw [Functor.map_comp]
  let q_i := SimplexCategory.Hom.toOrderHom
    (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map α_i)
  let q_j := SimplexCategory.Hom.toOrderHom
    (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map α_j)
  let q_β := SimplexCategory.Hom.toOrderHom
    (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map β')
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨z, hz, rfl⟩
  apply Finset.mem_image.mpr
  refine ⟨q_β z, Finset.mem_univ _, ?_⟩
  have hval := congrArg (fun q => q.toOrderHom z) hq
  change q_i z = q_j (q_β z) at hval
  exact hval.symm

lemma faceChainSubset_ssubset_of_lt {W : HomotopyHypothesis.Henry.SemiSSet.{u}} {n : ℕ}
    (F : ComposableArrows (Simplicial.BarycentricSubdivision.FaceCategory W) n)
    (hF : StrictMono (fun i : Fin (n + 1) => Simplicial.BarycentricSubdivision.faceDimension (W := W) (F.obj i)))
    {i j : Fin (n + 1)} (hij : i < j) : faceChainSubset F i ⊂ faceChainSubset F j := by
  have hsub : faceChainSubset F i ⊆ faceChainSubset F j :=
    faceChainSubset_subset_of_le F hij.le
  have hcard : (faceChainSubset F i).card < (faceChainSubset F j).card := by
    rw [faceChainSubset_card, faceChainSubset_card]
    exact Nat.add_lt_add_right (hF hij) 1
  exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub, by
    intro heq
    have hcardEq := congrArg Finset.card heq
    omega⟩


/-- Reindex a terminal face subset into the vertex type indexed by its dimension. -/
def faceChainSubsetPV {W : HomotopyHypothesis.Henry.SemiSSet.{u}} {n : ℕ}
    (F : ComposableArrows (Simplicial.BarycentricSubdivision.FaceCategory W) n) (i : Fin (n + 1)) :
    Finset (Fin (Simplicial.BarycentricSubdivision.faceDimension (W := W) (F.obj (Fin.last n)) + 1)) :=
  (faceChainSubset F i).image (fun v => Fin.cast
    (congrArg Nat.succ (by
      simpa [Simplicial.BarycentricSubdivision.faceDimension] using
        Simplicial.BarycentricSubdivision.semiSimplex_inclusion_length ((F.obj (Fin.last n)).unop.obj.unop))) v)

lemma faceChainSubsetPV_nonempty {W : HomotopyHypothesis.Henry.SemiSSet.{u}} {n : ℕ}
    (F : ComposableArrows (Simplicial.BarycentricSubdivision.FaceCategory W) n) (i : Fin (n + 1)) :
    (faceChainSubsetPV F i).Nonempty := by
  obtain ⟨v, hv⟩ := faceChainSubset_nonempty F i
  exact ⟨_, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩

lemma faceChainSubsetPV_card {W : HomotopyHypothesis.Henry.SemiSSet.{u}} {n : ℕ}
    (F : ComposableArrows (Simplicial.BarycentricSubdivision.FaceCategory W) n) (i : Fin (n + 1)) :
    (faceChainSubsetPV F i).card = (faceChainSubset F i).card := by
  let hlen : (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.obj
      ((F.obj (Fin.last n)).unop.obj.unop)).len =
        Simplicial.BarycentricSubdivision.faceDimension (W := W) (F.obj (Fin.last n)) := by
    simpa [Simplicial.BarycentricSubdivision.faceDimension] using
      Simplicial.BarycentricSubdivision.semiSimplex_inclusion_length ((F.obj (Fin.last n)).unop.obj.unop)
  rw [faceChainSubsetPV, Finset.card_image_of_injective _ (Fin.cast_injective (congrArg Nat.succ hlen))]

lemma faceChainSubsetPV_subset_of_le {W : HomotopyHypothesis.Henry.SemiSSet.{u}} {n : ℕ}
    (F : ComposableArrows (Simplicial.BarycentricSubdivision.FaceCategory W) n) {i j : Fin (n + 1)}
    (hij : i ≤ j) : faceChainSubsetPV F i ⊆ faceChainSubsetPV F j := by
  exact Finset.image_subset_image (faceChainSubset_subset_of_le F hij)

lemma faceChainSubsetPV_ssubset_of_lt {W : HomotopyHypothesis.Henry.SemiSSet.{u}} {n : ℕ}
    (F : ComposableArrows (Simplicial.BarycentricSubdivision.FaceCategory W) n)
    (hF : StrictMono (fun i : Fin (n + 1) => Simplicial.BarycentricSubdivision.faceDimension (W := W) (F.obj i)))
    {i j : Fin (n + 1)} (hij : i < j) : faceChainSubsetPV F i ⊂ faceChainSubsetPV F j := by
  apply (Finset.image_ssubset_image (Fin.cast_injective (congrArg Nat.succ (by
    simpa [Simplicial.BarycentricSubdivision.faceDimension] using
      Simplicial.BarycentricSubdivision.semiSimplex_inclusion_length ((F.obj (Fin.last n)).unop.obj.unop))))).2
  exact faceChainSubset_ssubset_of_lt F hF hij

/-- Turn a strict chain of faces into the corresponding simplex of a derived standard simplex. -/
def faceChainDerivedSimplex {W : HomotopyHypothesis.Henry.SemiSSet.{u}} {n : ℕ}
    (F : ComposableArrows (Simplicial.BarycentricSubdivision.FaceCategory W) n)
    (hF : StrictMono (fun i : Fin (n + 1) =>
      Simplicial.BarycentricSubdivision.faceDimension (W := W) (F.obj i))) :
    (HomotopyHypothesis.Approximation.Topological.sdComplex
      (Simplicial.BarycentricSubdivision.faceDimension (W := W) (F.obj (Fin.last n)))).Simplex n := by
  let d := Simplicial.BarycentricSubdivision.faceDimension (W := W) (F.obj (Fin.last n))
  let vertices : Fin (n + 1) → HomotopyHypothesis.Approximation.Topological.PV d :=
    fun i => HomotopyHypothesis.Approximation.Topological.PV.mid (faceChainSubsetPV F i)
  let A := Finset.univ.image vertices
  have hvertices : StrictMono vertices := by
    intro i j hij
    have hssub := faceChainSubsetPV_ssubset_of_lt F hF hij
    have hcard := Finset.card_lt_card hssub
    change HomotopyHypothesis.Approximation.Topological.PV.rank
        (HomotopyHypothesis.Approximation.Topological.PV.mid (faceChainSubsetPV F i)) <
      HomotopyHypothesis.Approximation.Topological.PV.rank
        (HomotopyHypothesis.Approximation.Topological.PV.mid (faceChainSubsetPV F j))
    dsimp [HomotopyHypothesis.Approximation.Topological.PV.rank]
    exact Prod.Lex.toLex_lt_toLex.2
      (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.2 (Or.inl hcard)⟩)
  have hnotTop : ∀ i, HomotopyHypothesis.Approximation.Topological.PV.top i ∉ A := by
    intro i hi
    rcases Finset.mem_image.mp hi with ⟨j, hj, hEq⟩
    cases hEq
  have hlabel (S : Finset (Fin (d + 1)))
      (hS : HomotopyHypothesis.Approximation.Topological.PV.mid S ∈ A) :
      ∃ i, S = faceChainSubsetPV F i := by
    rcases Finset.mem_image.mp hS with ⟨i, hi, hEq⟩
    exact ⟨i, (HomotopyHypothesis.Approximation.Topological.PV.mid.inj hEq).symm⟩
  have hnonempty : ∀ S, HomotopyHypothesis.Approximation.Topological.PV.mid S ∈ A → S.Nonempty := by
    intro S hS
    obtain ⟨i, rfl⟩ := hlabel S hS
    exact faceChainSubsetPV_nonempty F i
  have hpairwise : ∀ S T, HomotopyHypothesis.Approximation.Topological.PV.mid S ∈ A →
      HomotopyHypothesis.Approximation.Topological.PV.mid T ∈ A → S ⊆ T ∨ T ⊆ S := by
    intro S T hS hT
    obtain ⟨i, rfl⟩ := hlabel S hS
    obtain ⟨j, rfl⟩ := hlabel T hT
    rcases le_total i j with hij | hji
    · exact Or.inl (faceChainSubsetPV_subset_of_le F hij)
    · exact Or.inr (faceChainSubsetPV_subset_of_le F hji)
  have hcomplex :
      (HomotopyHypothesis.Approximation.Topological.sdComplex d).S A := by
    refine ⟨?_, hnotTop⟩
    refine ⟨hnonempty, hpairwise, ?_⟩
    intro i S hi hS
    exact False.elim (hnotTop i hi)
  exact ⟨vertices, hvertices, hcomplex⟩

/-- Send a strict face chain to its normal-form simplex in the derived subdivision. -/
noncomputable def faceChainToSdLanValue {W : HomotopyHypothesis.Henry.SemiSSet.{u}}
    {a : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ}
    (z : (Simplicial.BarycentricSubdivision.firstSubdivision.{u}.obj W).obj a) :
    (HomotopyHypothesis.Approximation.Topological.sdLan.{u}.obj W).obj a := by
  let n := a.unop.obj.len
  let F : ComposableArrows (Simplicial.BarycentricSubdivision.FaceCategory W) n := z.1
  let hF : StrictMono (fun i : Fin (n + 1) =>
      Simplicial.BarycentricSubdivision.faceDimension (W := W) (F.obj i)) := z.2
  let c := F.obj (Fin.last n)
  let s := c.unop.obj.unop
  let τ := faceChainDerivedSimplex F hF
  let σ := Simplicial.BarycentricSubdivision.faceObjectSimplexMap c
  exact ((HomotopyHypothesis.Approximation.Topological.sdLan.{u}.map σ).app a)
    (((HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit
      HomotopyHypothesis.Approximation.Topological.sdCos.{u}).app s).app a (ULift.up τ))

lemma chainTerminalFaceArrow_whisker {W : HomotopyHypothesis.Henry.SemiSSet.{u}}
    {n m : ℕ} (F : ComposableArrows (Simplicial.BarycentricSubdivision.FaceCategory W) n)
    (Φ : Fin (m + 1) ⥤ Fin (n + 1)) (i : Fin (m + 1)) :
    chainTerminalFaceArrow F (Φ.obj i) =
      Simplicial.BarycentricSubdivision.faceCategoryArrowUnderlying
        ((F.whiskerLeft Φ).map (CategoryTheory.homOfLE (Fin.le_last i))) ≫
        chainTerminalFaceArrow F (Φ.obj (Fin.last m)) := by
  let α := (F.whiskerLeft Φ).map (CategoryTheory.homOfLE (Fin.le_last i))
  let β := F.map (CategoryTheory.homOfLE (Fin.le_last (Φ.obj i)))
  let γ := F.map (CategoryTheory.homOfLE (Fin.le_last (Φ.obj (Fin.last m))))
  have hbase : α ≫ γ = β := by
    dsimp [α, β, γ, CategoryTheory.ComposableArrows.whiskerLeft]
    rw [← F.map_comp]
    congr 1
  have hcomp := congrArg Simplicial.BarycentricSubdivision.faceCategoryArrowUnderlying hbase.symm
  calc
    chainTerminalFaceArrow F (Φ.obj i) =
        Simplicial.BarycentricSubdivision.faceCategoryArrowUnderlying (F.map
          (CategoryTheory.homOfLE (Fin.le_last (Φ.obj i)))) := rfl
    _ = Simplicial.BarycentricSubdivision.faceCategoryArrowUnderlying
        (F.map (Φ.map (CategoryTheory.homOfLE (Fin.le_last i))) ≫
          F.map (CategoryTheory.homOfLE (Fin.le_last (Φ.obj (Fin.last m)))) ) := hcomp
    _ = Simplicial.BarycentricSubdivision.faceCategoryArrowUnderlying
          (F.map (Φ.map (CategoryTheory.homOfLE (Fin.le_last i)))) ≫
        chainTerminalFaceArrow F (Φ.obj (Fin.last m)) := rfl

lemma faceChainSubset_whiskerLeft {W : HomotopyHypothesis.Henry.SemiSSet.{u}}
    {n m : ℕ} (F : ComposableArrows (Simplicial.BarycentricSubdivision.FaceCategory W) n)
    (Φ : Fin (m + 1) ⥤ Fin (n + 1)) (i : Fin (m + 1)) :
    faceChainSubset F (Φ.obj i) =
      (faceChainSubset (Φ ⋙ F) i).image
        (SimplexCategory.Hom.toOrderHom
          (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map
            (chainTerminalFaceArrow F (Φ.obj (Fin.last m))))) := by
  let F' : ComposableArrows (Simplicial.BarycentricSubdivision.FaceCategory W) m := Φ ⋙ F
  let γ := chainTerminalFaceArrow F (Φ.obj (Fin.last m))
  let β := F.map (Φ.map (CategoryTheory.homOfLE (Fin.le_last i)))
  let αβ := Simplicial.BarycentricSubdivision.faceCategoryArrowUnderlying β
  let qleft := SimplexCategory.Hom.toOrderHom
    (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map
      (chainTerminalFaceArrow F (Φ.obj i)))
  let qright := SimplexCategory.Hom.toOrderHom
    (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map αβ)
  let qγ := SimplexCategory.Hom.toOrderHom
    (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map γ)
  have hmap : qleft = qγ.comp qright := by
    have h := congrArg (fun α => SimplexCategory.Hom.toOrderHom
      (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map α))
      (chainTerminalFaceArrow_whisker F Φ i)
    change qleft = qγ.comp qright at h
    exact h
  have hpoint (v : Fin ((HomotopyHypothesis.Henry.SemiSimplexCategory.incl.obj
        ((F.obj (Φ.obj i)).unop.obj.unop)).len + 1)) :
      qleft v = qγ (qright v) := by
    have h := congrArg (fun q => q v) hmap
    change qleft v = qγ (qright v) at h
    exact h
  have hfun : (qleft : _ → _) = qγ ∘ qright := by
    funext v
    exact hpoint v
  have hrange : faceChainSubset (Φ ⋙ F) i = Finset.univ.image qright := by
    change Finset.univ.image qright = Finset.univ.image qright
    rfl
  calc
    faceChainSubset F (Φ.obj i) = Finset.univ.image qleft := by
      simp [faceChainSubset, qleft, chainTerminalFaceArrow,
        Simplicial.BarycentricSubdivision.semiSimplex_inclusion_length, Simplicial.BarycentricSubdivision.faceDimension]
    _ = Finset.univ.image (qγ ∘ qright) := by
      simpa [Simplicial.BarycentricSubdivision.semiSimplex_inclusion_length, Simplicial.BarycentricSubdivision.faceDimension] using
        congrArg (fun f => Finset.univ.image f) hfun
    _ = (Finset.univ.image qright).image qγ := by
      simpa [Simplicial.BarycentricSubdivision.semiSimplex_inclusion_length, Simplicial.BarycentricSubdivision.faceDimension] using
        (Finset.image_image.symm : Finset.univ.image (qγ ∘ qright) =
          (Finset.univ.image qright).image qγ)
    _ = (faceChainSubset (Φ ⋙ F) i).image qγ := by rw [← hrange]


def faceChainTerminalMapPV {W : HomotopyHypothesis.Henry.SemiSSet.{u}}
    {n m : ℕ} (F : ComposableArrows (Simplicial.BarycentricSubdivision.FaceCategory W) n)
    (Φ : Fin (m + 1) ⥤ Fin (n + 1)) :
    Fin (Simplicial.BarycentricSubdivision.faceDimension (W := W) ((Φ ⋙ F).obj (Fin.last m)) + 1) →
      Fin (Simplicial.BarycentricSubdivision.faceDimension (W := W) (F.obj (Fin.last n)) + 1) := by
  let c' := ((Φ ⋙ F).obj (Fin.last m)).unop.obj.unop
  let c := (F.obj (Fin.last n)).unop.obj.unop
  let h' : (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.obj c').len =
      Simplicial.BarycentricSubdivision.faceDimension (W := W) ((Φ ⋙ F).obj (Fin.last m)) := by
    simpa [c', Simplicial.BarycentricSubdivision.faceDimension] using Simplicial.BarycentricSubdivision.semiSimplex_inclusion_length c'
  let h : (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.obj c).len =
      Simplicial.BarycentricSubdivision.faceDimension (W := W) (F.obj (Fin.last n)) := by
    simpa [c, Simplicial.BarycentricSubdivision.faceDimension] using Simplicial.BarycentricSubdivision.semiSimplex_inclusion_length c
  exact fun v => Fin.cast (congrArg Nat.succ h)
    (SimplexCategory.Hom.toOrderHom
      (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map
        (chainTerminalFaceArrow F (Φ.obj (Fin.last m))))
      (Fin.cast (congrArg Nat.succ h').symm v))

lemma faceChainTerminalMapPV_eq {W : HomotopyHypothesis.Henry.SemiSSet.{u}}
    {n m : ℕ} (F : ComposableArrows (Simplicial.BarycentricSubdivision.FaceCategory W) n)
    (Φ : Fin (m + 1) ⥤ Fin (n + 1)) :
    faceChainTerminalMapPV F Φ =
      SimplexCategory.Hom.toOrderHom
        (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map
          (chainTerminalFaceArrow F (Φ.obj (Fin.last m)))) := by
  funext v
  simp [faceChainTerminalMapPV, Simplicial.BarycentricSubdivision.semiSimplex_inclusion_length,
    Simplicial.BarycentricSubdivision.faceDimension]

lemma faceChainSubsetPV_whiskerLeft {W : HomotopyHypothesis.Henry.SemiSSet.{u}}
    {n m : ℕ} (F : ComposableArrows (Simplicial.BarycentricSubdivision.FaceCategory W) n)
    (Φ : Fin (m + 1) ⥤ Fin (n + 1)) (i : Fin (m + 1)) :
    faceChainSubsetPV F (Φ.obj i) =
      (faceChainSubsetPV (Φ ⋙ F) i).image (faceChainTerminalMapPV F Φ) := by
  unfold faceChainSubsetPV
  rw [faceChainSubset_whiskerLeft]
  simp only [Finset.image_image]
  unfold faceChainTerminalMapPV
  simp [Simplicial.BarycentricSubdivision.semiSimplex_inclusion_length, Simplicial.BarycentricSubdivision.faceDimension,
    Function.comp_def]


lemma faceChainDerivedSimplex_restrict {W : HomotopyHypothesis.Henry.SemiSSet.{u}}
    {m n : ℕ}
    (θ : HomotopyHypothesis.Henry.SemiSimplexCategory.mk m ⟶
      HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)
    (F : ComposableArrows (Simplicial.BarycentricSubdivision.FaceCategory W) n)
    (hF : StrictMono (fun i : Fin (n + 1) =>
      Simplicial.BarycentricSubdivision.faceDimension (W := W) (F.obj i))) :
    let Φ : Fin (m + 1) ⥤ Fin (n + 1) :=
      (SimplexCategory.toCat.map
        (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map θ)).toFunctor
    let F' : ComposableArrows (Simplicial.BarycentricSubdivision.FaceCategory W) m := Φ ⋙ F
    let hF' : StrictMono (fun i : Fin (m + 1) =>
      Simplicial.BarycentricSubdivision.faceDimension (W := W) (F'.obj i)) := by
        intro i j hij
        exact hF (by
          have hθ : StrictMono Φ.obj := by
            intro i j hij
            have hi : Φ.obj i = SimplexCategory.Hom.toOrderHom
                (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map θ) i := by
              simp [Φ, SimplexCategory.toCat]
              rfl
            have hj : Φ.obj j = SimplexCategory.Hom.toOrderHom
                (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map θ) j := by
              simp [Φ, SimplexCategory.toCat]
              rfl
            rw [hi, hj]
            exact HomotopyHypothesis.Approximation.Topological.SemiSimplexCategory.strictMono θ hij
          exact hθ hij)
    let γ := chainTerminalFaceArrow F (Φ.obj (Fin.last m))
    ((HomotopyHypothesis.Approximation.Topological.sdCos.{u}.map γ).app
      (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m))
      (ULift.up (faceChainDerivedSimplex F' hF'))) =
    ((HomotopyHypothesis.Approximation.Topological.sdComplex
      (Simplicial.BarycentricSubdivision.faceDimension (W := W) (F.obj (Fin.last n)))).toSemiSSet.{u}.map
        (Opposite.op θ)) (ULift.up (faceChainDerivedSimplex F hF)) := by
  classical
  dsimp only
  let Φ : Fin (m + 1) ⥤ Fin (n + 1) :=
    (SimplexCategory.toCat.map
      (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map θ)).toFunctor
  let F' : ComposableArrows (Simplicial.BarycentricSubdivision.FaceCategory W) m := Φ ⋙ F
  have hΦ : StrictMono Φ.obj := by
    intro i j hij
    have hi : Φ.obj i = SimplexCategory.Hom.toOrderHom
        (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map θ) i := by
      simp [Φ, SimplexCategory.toCat]
      rfl
    have hj : Φ.obj j = SimplexCategory.Hom.toOrderHom
        (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map θ) j := by
      simp [Φ, SimplexCategory.toCat]
      rfl
    rw [hi, hj]
    exact HomotopyHypothesis.Approximation.Topological.SemiSimplexCategory.strictMono θ hij
  have hF' : StrictMono (fun i : Fin (m + 1) =>
      Simplicial.BarycentricSubdivision.faceDimension (W := W) (F'.obj i)) := by
    intro i j hij
    exact hF (hΦ hij)
  let γ := chainTerminalFaceArrow F (Φ.obj (Fin.last m))
  apply ULift.ext
  apply Subtype.ext
  funext i
  change HomotopyHypothesis.Approximation.Topological.PV.map
      (SimplexCategory.Hom.toOrderHom
        (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map γ))
      ((faceChainDerivedSimplex F' hF').1 i) =
    (faceChainDerivedSimplex F hF).1
      (SimplexCategory.Hom.toOrderHom
        (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map θ) i)
  change HomotopyHypothesis.Approximation.Topological.PV.mid
      ((faceChainSubsetPV F' i).image
        (SimplexCategory.Hom.toOrderHom
          (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map γ))) =
    HomotopyHypothesis.Approximation.Topological.PV.mid (faceChainSubsetPV F (Φ.obj i))
  apply congrArg HomotopyHypothesis.Approximation.Topological.PV.mid
  rw [← faceChainTerminalMapPV_eq F Φ]
  exact (faceChainSubsetPV_whiskerLeft F Φ i).symm


lemma faceObjectSimplexMap_faceFunctor {W V : HomotopyHypothesis.Henry.SemiSSet.{u}}
    (φ : W ⟶ V) (x : Simplicial.BarycentricSubdivision.FaceCategory W) :
    Simplicial.BarycentricSubdivision.faceObjectSimplexMap ((Simplicial.BarycentricSubdivision.faceFunctor φ).obj x) =
      Simplicial.BarycentricSubdivision.faceObjectSimplexMap x ≫ φ := by
  apply (CategoryTheory.uliftYonedaEquiv.{u}
    (X := x.unop.obj.unop)).injective
  rw [CategoryTheory.uliftYonedaEquiv_comp]
  simp [Simplicial.BarycentricSubdivision.faceObjectSimplexMap, Simplicial.BarycentricSubdivision.faceFunctor,
    CategoryTheory.NatTrans.mapElements]
  exact Equiv.apply_symm_apply _ _


lemma faceCategoryArrowUnderlying_faceFunctor_map
    {W V : HomotopyHypothesis.Henry.SemiSSet.{u}} (φ : W ⟶ V)
    {x y : Simplicial.BarycentricSubdivision.FaceCategory W} (f : x ⟶ y) :
    Simplicial.BarycentricSubdivision.faceCategoryArrowUnderlying ((Simplicial.BarycentricSubdivision.faceFunctor φ).map f) =
      Simplicial.BarycentricSubdivision.faceCategoryArrowUnderlying f := rfl


lemma faceChainSubset_faceFunctor_map
    {W V : HomotopyHypothesis.Henry.SemiSSet.{u}} (φ : W ⟶ V)
    {n : ℕ} (F : ComposableArrows (Simplicial.BarycentricSubdivision.FaceCategory W) n) (i : Fin (n + 1)) :
    faceChainSubset (((Simplicial.BarycentricSubdivision.faceFunctor φ).mapComposableArrows n).obj F) i =
      faceChainSubset F i := by
  rfl


lemma faceChainSubsetPV_faceFunctor_map
    {W V : HomotopyHypothesis.Henry.SemiSSet.{u}} (φ : W ⟶ V)
    {n : ℕ} (F : ComposableArrows (Simplicial.BarycentricSubdivision.FaceCategory W) n) (i : Fin (n + 1)) :
    faceChainSubsetPV (((Simplicial.BarycentricSubdivision.faceFunctor φ).mapComposableArrows n).obj F) i =
      faceChainSubsetPV F i := by
  rfl


lemma faceChainDerivedSimplex_faceFunctor_map
    {W V : HomotopyHypothesis.Henry.SemiSSet.{u}} (φ : W ⟶ V)
    {n : ℕ} (F : ComposableArrows (Simplicial.BarycentricSubdivision.FaceCategory W) n)
    (hF : StrictMono (fun i : Fin (n + 1) =>
      Simplicial.BarycentricSubdivision.faceDimension (W := W) (F.obj i))) :
    faceChainDerivedSimplex (((Simplicial.BarycentricSubdivision.faceFunctor φ).mapComposableArrows n).obj F)
      (by
        intro i j hij
        simpa [CategoryTheory.Functor.mapComposableArrows,
          Simplicial.BarycentricSubdivision.faceFunctor_preserves_dimension] using hF hij) =
      faceChainDerivedSimplex F hF := by
  apply Subtype.ext
  funext i
  change HomotopyHypothesis.Approximation.Topological.PV.mid
      (faceChainSubsetPV (((Simplicial.BarycentricSubdivision.faceFunctor φ).mapComposableArrows n).obj F) i) =
    HomotopyHypothesis.Approximation.Topological.PV.mid (faceChainSubsetPV F i)
  rw [faceChainSubsetPV_faceFunctor_map]
  rfl


lemma faceChainToSdLanValue_naturality
    {W V : HomotopyHypothesis.Henry.SemiSSet.{u}} (φ : W ⟶ V)
    {a : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ}
    (z : (Simplicial.BarycentricSubdivision.firstSubdivision.{u}.obj W).obj a) :
    (HomotopyHypothesis.Approximation.Topological.sdLan.{u}.map φ).app a
        (faceChainToSdLanValue z) =
      faceChainToSdLanValue ((Simplicial.BarycentricSubdivision.firstSubdivision.{u}.map φ).app a z) := by
  classical
  let n := a.unop.obj.len
  let F : ComposableArrows (Simplicial.BarycentricSubdivision.FaceCategory W) n := z.1
  let Fφ : ComposableArrows (Simplicial.BarycentricSubdivision.FaceCategory V) n :=
    ((Simplicial.BarycentricSubdivision.faceFunctor φ).mapComposableArrows n).obj F
  let hF : StrictMono (fun i : Fin (n + 1) =>
      Simplicial.BarycentricSubdivision.faceDimension (W := W) (F.obj i)) := z.2
  let hFφ : StrictMono (fun i : Fin (n + 1) =>
      Simplicial.BarycentricSubdivision.faceDimension (W := V) (Fφ.obj i)) := by
    intro i j hij
    simpa [Fφ, CategoryTheory.Functor.mapComposableArrows,
      Simplicial.BarycentricSubdivision.faceFunctor_preserves_dimension] using hF hij
  let zφ : (Simplicial.BarycentricSubdivision.firstSubdivision.{u}.obj V).obj a := ⟨Fφ, hFφ⟩
  have hz : (Simplicial.BarycentricSubdivision.firstSubdivision.{u}.map φ).app a z = zφ := by
    apply Subtype.ext
    rfl
  let c := F.obj (Fin.last n)
  let cφ := Fφ.obj (Fin.last n)
  have hσ : Simplicial.BarycentricSubdivision.faceObjectSimplexMap cφ =
      Simplicial.BarycentricSubdivision.faceObjectSimplexMap c ≫ φ := by
    dsimp [cφ, c, Fφ]
    exact faceObjectSimplexMap_faceFunctor φ c
  have hτ : faceChainDerivedSimplex Fφ hFφ = faceChainDerivedSimplex F hF := by
    exact faceChainDerivedSimplex_faceFunctor_map φ F hF
  rw [hz]
  change (HomotopyHypothesis.Approximation.Topological.sdLan.{u}.map φ).app a
      ((HomotopyHypothesis.Approximation.Topological.sdLan.{u}.map
        (Simplicial.BarycentricSubdivision.faceObjectSimplexMap c)).app a
        (((HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit
          HomotopyHypothesis.Approximation.Topological.sdCos.{u}).app (c.unop.obj.unop)).app a
          (ULift.up (faceChainDerivedSimplex F hF)))) =
    (HomotopyHypothesis.Approximation.Topological.sdLan.{u}.map
      (Simplicial.BarycentricSubdivision.faceObjectSimplexMap cφ)).app a
      (((HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit
        HomotopyHypothesis.Approximation.Topological.sdCos.{u}).app (c.unop.obj.unop)).app a
        (ULift.up (faceChainDerivedSimplex Fφ hFφ)))
  rw [hσ, hτ]
  let x := (((HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit
    HomotopyHypothesis.Approximation.Topological.sdCos.{u}).app (c.unop.obj.unop)).app a)
      (ULift.up (faceChainDerivedSimplex F hF))
  change (HomotopyHypothesis.Approximation.Topological.sdLan.{u}.map φ).app a
      ((HomotopyHypothesis.Approximation.Topological.sdLan.{u}.map
        (Simplicial.BarycentricSubdivision.faceObjectSimplexMap c)).app a x) =
    (HomotopyHypothesis.Approximation.Topological.sdLan.{u}.map
      (Simplicial.BarycentricSubdivision.faceObjectSimplexMap c ≫ φ)).app a x
  exact (congrArg (fun η => η.app a x)
    (HomotopyHypothesis.Approximation.Topological.sdLan.map_comp
      (Simplicial.BarycentricSubdivision.faceObjectSimplexMap c) φ)).symm

lemma faceChainToSdLanValue_restrict
    {W : HomotopyHypothesis.Henry.SemiSSet.{u}} {m n : ℕ}
    (θ : HomotopyHypothesis.Henry.SemiSimplexCategory.mk m ⟶
      HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)
    (z : (Simplicial.BarycentricSubdivision.firstSubdivision.{u}.obj W).obj
      (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))) :
    ((HomotopyHypothesis.Approximation.Topological.sdLan.{u}.obj W).map (Opposite.op θ))
        (faceChainToSdLanValue z) =
      faceChainToSdLanValue
        (((Simplicial.BarycentricSubdivision.firstSubdivision.{u}.obj W).map (Opposite.op θ)) z) := by
  classical
  let F : ComposableArrows (Simplicial.BarycentricSubdivision.FaceCategory W) n := z.1
  let hF : StrictMono (fun i : Fin (n + 1) =>
      Simplicial.BarycentricSubdivision.faceDimension (W := W) (F.obj i)) := z.2
  let Φ : Fin (m + 1) ⥤ Fin (n + 1) :=
    (SimplexCategory.toCat.map
      (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map θ)).toFunctor
  let F' : ComposableArrows (Simplicial.BarycentricSubdivision.FaceCategory W) m := Φ ⋙ F
  have hΦ : StrictMono Φ.obj := by
    intro i j hij
    have hi : Φ.obj i = SimplexCategory.Hom.toOrderHom
        (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map θ) i := by
      simp [Φ, SimplexCategory.toCat]
      rfl
    have hj : Φ.obj j = SimplexCategory.Hom.toOrderHom
        (HomotopyHypothesis.Henry.SemiSimplexCategory.incl.map θ) j := by
      simp [Φ, SimplexCategory.toCat]
      rfl
    rw [hi, hj]
    exact HomotopyHypothesis.Approximation.Topological.SemiSimplexCategory.strictMono θ hij
  have hF' : StrictMono (fun i : Fin (m + 1) =>
      Simplicial.BarycentricSubdivision.faceDimension (W := W) (F'.obj i)) := by
    intro i j hij
    exact hF (hΦ hij)
  let z' : (Simplicial.BarycentricSubdivision.firstSubdivision.{u}.obj W).obj
      (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m)) := ⟨F', hF'⟩
  have hz : ((Simplicial.BarycentricSubdivision.firstSubdivision.{u}.obj W).map (Opposite.op θ)) z = z' := by
    apply Subtype.ext
    rfl
  let c := F.obj (Fin.last n)
  let c' := F'.obj (Fin.last m)
  let s := c.unop.obj.unop
  let s' := c'.unop.obj.unop
  let τ := faceChainDerivedSimplex F hF
  let τ' := faceChainDerivedSimplex F' hF'
  let γ := chainTerminalFaceArrow F (Φ.obj (Fin.last m))
  let σ := Simplicial.BarycentricSubdivision.faceObjectSimplexMap c
  let σ' := Simplicial.BarycentricSubdivision.faceObjectSimplexMap c'
  have hτ : ((HomotopyHypothesis.Approximation.Topological.sdCos.{u}.map γ).app
        (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m))
        (ULift.up τ')) =
      (((HomotopyHypothesis.Approximation.Topological.sdComplex
        (Simplicial.BarycentricSubdivision.faceDimension (W := W) (F.obj (Fin.last n)))).toSemiSSet.{u}.map
          (Opposite.op θ)) (ULift.up τ)) := by
    simpa only [Φ, F', hF', γ, τ, τ'] using
      (faceChainDerivedSimplex_restrict θ F hF)
  have hσ : HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.map γ ≫ σ = σ' := by
    simpa [σ, σ', γ, c, c', chainTerminalFaceArrow, F'] using
      (Simplicial.BarycentricSubdivision.faceObjectSimplexMap_naturality
        (F.map (CategoryTheory.homOfLE (Fin.le_last (Φ.obj (Fin.last m))))) )
  rw [hz]
  change ((HomotopyHypothesis.Approximation.Topological.sdLan.{u}.obj W).map (Opposite.op θ))
      ((HomotopyHypothesis.Approximation.Topological.sdLan.{u}.map σ).app
        (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))
        ((HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit
          HomotopyHypothesis.Approximation.Topological.sdCos.{u}).app s |>.app
          (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))
          (ULift.up τ))) =
    (HomotopyHypothesis.Approximation.Topological.sdLan.{u}.map σ').app
      (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m))
      ((HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit
        HomotopyHypothesis.Approximation.Topological.sdCos.{u}).app s' |>.app
        (Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m))
        (ULift.up τ'))
  let a := Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)
  let b := Opposite.op (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m)
  let η := (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit
    HomotopyHypothesis.Approximation.Topological.sdCos.{u})
  let τU := ULift.up τ
  let x := (η.app s).app a τU
  let y := (η.app s').app b (ULift.up τ')
  have houter := (HomotopyHypothesis.Approximation.Topological.sdLan.map σ).naturality_apply
    (Opposite.op θ) x
  have hindexVal := congrArg (fun q => q τU) ((η.app s).naturality (Opposite.op θ))
  change (η.app s).app b
        (((HomotopyHypothesis.Approximation.Topological.sdCos.obj s).map (Opposite.op θ)) τU) =
      (((HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u} ⋙
        HomotopyHypothesis.Approximation.Topological.sdLan).obj s).map (Opposite.op θ))
          ((η.app s).app a τU) at hindexVal
  have hchainVal := congrArg (fun q => q.app b (ULift.up τ')) (η.naturality γ)
  change (η.app s).app b
        ((HomotopyHypothesis.Approximation.Topological.sdCos.map γ).app b (ULift.up τ')) =
      (HomotopyHypothesis.Approximation.Topological.sdLan.map
        (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.map γ)).app b y at hchainVal
  have hmaps := congrArg (fun q => q.app b y)
    (HomotopyHypothesis.Approximation.Topological.sdLan.map_comp
      (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.map γ) σ)
  change (HomotopyHypothesis.Approximation.Topological.sdLan.map
      (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.map γ ≫ σ)).app b y =
    (HomotopyHypothesis.Approximation.Topological.sdLan.map σ).app b
      ((HomotopyHypothesis.Approximation.Topological.sdLan.map
        (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.map γ)).app b y) at hmaps
  change ((HomotopyHypothesis.Approximation.Topological.sdLan.obj W).map (Opposite.op θ))
      ((HomotopyHypothesis.Approximation.Topological.sdLan.map σ).app a x) =
    (HomotopyHypothesis.Approximation.Topological.sdLan.map σ').app b y
  calc
    _ = (HomotopyHypothesis.Approximation.Topological.sdLan.map σ).app b
        ((HomotopyHypothesis.Approximation.Topological.sdLan.obj
          (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj s)).map
            (Opposite.op θ) x) := houter.symm
    _ = (HomotopyHypothesis.Approximation.Topological.sdLan.map σ).app b
        (((HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit
          HomotopyHypothesis.Approximation.Topological.sdCos.{u}).app s).app b
          (((HomotopyHypothesis.Approximation.Topological.sdComplex
            (Simplicial.BarycentricSubdivision.faceDimension (W := W) (F.obj (Fin.last n)))).toSemiSSet.{u}.map
              (Opposite.op θ)) (ULift.up τ))) := by
          exact congrArg ((HomotopyHypothesis.Approximation.Topological.sdLan.map σ).app b) hindexVal.symm
    _ = (HomotopyHypothesis.Approximation.Topological.sdLan.map σ).app b
        (((HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit
          HomotopyHypothesis.Approximation.Topological.sdCos.{u}).app s).app b
          ((HomotopyHypothesis.Approximation.Topological.sdCos.{u}.map γ).app b (ULift.up τ'))) := by
          rw [← hτ]
    _ = (HomotopyHypothesis.Approximation.Topological.sdLan.map σ).app b
        ((HomotopyHypothesis.Approximation.Topological.sdLan.map
          (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.map γ)).app b y) := by
          exact congrArg ((HomotopyHypothesis.Approximation.Topological.sdLan.map σ).app b) hchainVal
    _ = (HomotopyHypothesis.Approximation.Topological.sdLan.map σ').app b y := by
          calc
            _ = (HomotopyHypothesis.Approximation.Topological.sdLan.map
                (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.map γ ≫ σ)).app b y := hmaps.symm
            _ = (HomotopyHypothesis.Approximation.Topological.sdLan.map σ').app b y := by rw [hσ]

lemma sdSimplexFace_faceChainDerivedSimplex
    {W : HomotopyHypothesis.Henry.SemiSSet.{u}} {n : ℕ}
    (F : ComposableArrows (Simplicial.BarycentricSubdivision.FaceCategory W) n)
    (hF : StrictMono (fun i : Fin (n + 1) =>
      Simplicial.BarycentricSubdivision.faceDimension (W := W) (F.obj i))) (i : Fin (n + 1)) :
    sdSimplexFace (faceChainDerivedSimplex F hF) i = faceChainSubsetPV F i := by
  apply HomotopyHypothesis.Approximation.Topological.PV.mid.inj
  exact (sdSimplexFace_spec (faceChainDerivedSimplex F hF) i).symm

noncomputable def faceChainToSdLanMap (W : HomotopyHypothesis.Henry.SemiSSet.{u}) :
    Simplicial.BarycentricSubdivision.firstSubdivision.{u}.obj W ⟶
      HomotopyHypothesis.Approximation.Topological.sdLan.{u}.obj W := by
  classical
  refine { app := fun a => TypeCat.ofHom (fun z => faceChainToSdLanValue z), naturality := ?_ }
  intro a b f
  apply TypeCat.homEquiv.injective
  funext z
  let ha : HomotopyHypothesis.Henry.SemiSimplexCategory.mk a.unop.obj.len = a.unop := by
    apply CategoryTheory.WideSubcategory.ext
    exact SimplexCategory.mk_len a.unop.obj
  let hb : HomotopyHypothesis.Henry.SemiSimplexCategory.mk b.unop.obj.len = b.unop := by
    apply CategoryTheory.WideSubcategory.ext
    exact SimplexCategory.mk_len b.unop.obj
  cases ha
  cases hb
  exact (faceChainToSdLanValue_restrict f.unop z).symm

noncomputable def faceChainToSdLan :
    Simplicial.BarycentricSubdivision.firstSubdivision.{u} ⟶ HomotopyHypothesis.Approximation.Topological.sdLan.{u} where
  app W := faceChainToSdLanMap W
  naturality {W V} φ := by
    ext a z
    exact (faceChainToSdLanValue_naturality φ z).symm

end HomotopyHypothesis.Simplicial.SubdivisionComparison
