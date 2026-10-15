import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Dprism
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismBdry
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismBdryComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismBdryIota
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Inst42
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV
/-!
# The derived cylinder of a simplex collapses

The collapse is obtained by attaching the simplices containing the full middle face in increasing
rank, each along the horn opposite the barycenter of its top face.
-/

universe u v w

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.DerivedPrismCollapse

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet
open HomotopyHypothesis.Approximation.Topological
open PV

private def pvEncode {k : ℕ} : PV k → Fin (k + 1) ⊕ Finset (Fin (k + 1))
  | .top i => Sum.inl i
  | .mid S => Sum.inr S

private theorem pvEncode_injective {k : ℕ} :
    Function.Injective (pvEncode : PV k → Fin (k + 1) ⊕ Finset (Fin (k + 1))) := by
  intro a b h
  cases a <;> cases b <;> simp_all [pvEncode]

private noncomputable instance pvFintype {k : ℕ} : Fintype (PV k) :=
  Fintype.ofInjective pvEncode pvEncode_injective

private theorem types_isPushout_of_cover {A B C P : Type u}
    {f : A ⟶ B} {g : A ⟶ C} {l : B ⟶ P} {r : C ⟶ P}
    (hcomm : ∀ a, l (f a) = r (g a)) (hl : Function.Injective l)
    (hr : Function.Injective r)
    (hcover : ∀ p, (PSigma fun b => l b = p) ⊕ (PSigma fun c => r c = p))
    (hoverlap : ∀ b c, l b = r c → ∃ a, f a = b ∧ g a = c) :
    IsPushout f g l r := by
  classical
  let condition : f ≫ l = g ≫ r := by
    ext a
    exact hcomm a
  let rep : ∀ p : P, (PSigma fun b : B => l b = p) ⊕ (PSigma fun c : C => r c = p) := hcover
  let desc : ∀ s : PushoutCocone f g, P ⟶ s.pt := fun s => ↾fun p =>
    match rep p with
    | Sum.inl ⟨b, _⟩ => s.inl b
    | Sum.inr ⟨c, _⟩ => s.inr c
  refine IsPushout.of_isColimit (c := PushoutCocone.mk l r condition)
    (PushoutCocone.IsColimit.mk condition desc ?_ ?_ ?_)
  · intro s
    apply ConcreteCategory.hom_ext
    intro b
    change desc s (l b) = s.inl b
    dsimp only [desc]
    cases hrep : rep (l b) with
    | inl h =>
        obtain ⟨b', hb'⟩ := h
        have : b' = b := hl (hb'.trans rfl)
        subst b'
        simp only [ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply, hrep]
    | inr h =>
        obtain ⟨c, hc⟩ := h
        obtain ⟨a, rfl, rfl⟩ := hoverlap b c hc.symm
        have hsq := congrArg (fun e : A ⟶ s.pt => e a) s.condition
        simpa only [types_comp_apply, ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply,
          hrep] using hsq.symm
  · intro s
    apply ConcreteCategory.hom_ext
    intro c
    change desc s (r c) = s.inr c
    dsimp only [desc]
    cases hrep : rep (r c) with
    | inl h =>
        obtain ⟨b, hb⟩ := h
        obtain ⟨a, rfl, rfl⟩ := hoverlap b c hb
        have hsq := congrArg (fun e : A ⟶ s.pt => e a) s.condition
        simpa only [types_comp_apply, ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply,
          hrep] using hsq
    | inr h =>
        obtain ⟨c', hc'⟩ := h
        have : c' = c := hr (hc'.trans rfl)
        subst c'
        simp only [ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply, hrep]
  · intro s m hm₁ hm₂
    apply ConcreteCategory.hom_ext
    intro p
    change m p = desc s p
    dsimp only [desc]
    cases hrep : rep p with
    | inl h =>
        obtain ⟨b, rfl⟩ := h
        simpa only [types_comp_apply, ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply,
          hrep] using congrArg (fun e : B ⟶ s.pt => e b) hm₁
    | inr h =>
        obtain ⟨c, rfl⟩ := h
        simpa only [types_comp_apply, ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply,
          hrep] using congrArg (fun e : C ⟶ s.pt => e c) hm₂

private theorem isPushout_subfunctor_sup_range {C : Type v} [Category.{w} C]
    {D F : C ⥤ Type u} (A : Subfunctor D) (S : Subfunctor F) (η : D ⟶ F)
    (g : A.toFunctor ⟶ S.toFunctor) (hcomm : A.ι ≫ η = g ≫ S.ι)
    [Mono η]
    (hinter : ∀ (U : C) (x : D.obj U), η.app U x ∈ S.obj U → x ∈ A.obj U) :
    IsPushout A.ι g
      (Subfunctor.lift η (G := Subfunctor.range η) (by rfl) ≫
        Subfunctor.homOfLe (G := Subfunctor.range η)
          (le_sup_right : Subfunctor.range η ≤ S ⊔ Subfunctor.range η))
      (Subfunctor.homOfLe (G := S) (le_sup_left : S ≤ S ⊔ Subfunctor.range η)) := by
  apply IsPushout.of_forall_isPushout_app
  intro U
  apply types_isPushout_of_cover
  · intro x
    apply Subtype.ext
    exact congrFun (congrArg (fun e => e.app U) hcomm) x
  · intro x y h
    have h' : η.app U x = η.app U y :=
      congrArg (fun z : (S ⊔ Subfunctor.range η).obj U => (z : F.obj U)) h
    exact (mono_iff_injective (η.app U)).1 inferInstance h'
  · intro x y h
    apply Subtype.ext
    exact congrArg (fun z : (S ⊔ Subfunctor.range η).obj U => (z : F.obj U)) h
  · intro x
    classical
    by_cases hxS : x.val ∈ S.obj U
    · exact Sum.inr ⟨⟨x.val, hxS⟩, rfl⟩
    · have hxR : x.val ∈ (Subfunctor.range η).obj U := by
        have hx' : x.val ∈ S.obj U ∨ x.val ∈ (Subfunctor.range η).obj U := by
          simpa using x.property
        exact hx'.resolve_left hxS
      let y : D.obj U := Classical.choose hxR
      have hy : η.app U y = x.val := Classical.choose_spec hxR
      exact Sum.inl ⟨y, Subtype.ext hy⟩
  · intro x y h
    have h' : η.app U x = y.val :=
      congrArg (fun z : (S ⊔ Subfunctor.range η).obj U => (z : F.obj U)) h
    have hx : x ∈ A.obj U := hinter U x (h'.symm ▸ y.property)
    refine ⟨⟨x, hx⟩, rfl, ?_⟩
    apply Subtype.ext
    have hc := congrFun (congrArg (fun e => e.app U) hcomm) ⟨x, hx⟩
    exact hc.symm.trans h'

private noncomputable def simplexOfVertexSet {k r : ℕ} (A : Finset (PV k))
    (hcard : A.card = r + 2) (hK : (dprismComplex k).S A) :
    HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk (r + 1)) ⟶ dprism.{u} k := by
  classical
  let e := A.orderEmbOfFin hcard
  refine
    { app := fun X => ↾fun σ => ULift.up
        ⟨(fun i => e (σ.down.hom.toOrderHom i)), ?_, ?_⟩
      naturality := ?_ }
  · exact e.strictMono.comp
      (HomotopyHypothesis.Approximation.Topological.SemiSimplexCategory.strictMono σ.down)
  · refine (dprismComplex k).down ?_ hK
    apply Finset.image_subset_iff.mpr
    intro i hi
    exact Finset.orderEmbOfFin_mem A hcard (σ.down.hom.toOrderHom i)
  · intro X Y f
    apply ConcreteCategory.hom_ext
    intro σ
    apply ULift.ext
    apply Subtype.ext
    funext i
    rfl

private theorem simplexOfVertexSet_mono {k r : ℕ} (A : Finset (PV k))
    (hcard : A.card = r + 2) (hK : (dprismComplex k).S A) :
    Mono (simplexOfVertexSet A hcard hK) := by
  classical
  let e := A.orderEmbOfFin hcard
  rw [NatTrans.mono_iff_mono_app]
  intro X
  apply (mono_iff_injective _).2
  intro x y hxy
  apply ULift.ext
  apply WideSubcategory.hom_ext
  apply SimplexCategory.Hom.ext'
  ext i
  have hv := congrArg (fun σ => σ.1 i) (congrArg ULift.down hxy)
  dsimp [simplexOfVertexSet] at hv
  change e (x.down.hom.toOrderHom i) = e (y.down.hom.toOrderHom i) at hv
  exact congrArg Fin.val (e.injective hv)

private noncomputable def dprismVertices {k : ℕ}
    {X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ}
    (σ : (dprism.{u} k).obj X) : Finset (PV k) :=
  @Finset.image (Fin (X.unop.obj.len + 1)) (PV k)
    LinearOrder.toDecidableEq σ.down.1 Finset.univ

private theorem simplexOfVertexSet_vertices_subset {k r : ℕ} (A : Finset (PV k))
    (hcard : A.card = r + 2) (hK : (dprismComplex k).S A)
    (X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ)
    (σ : (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk (r + 1))).obj X) :
    dprismVertices ((simplexOfVertexSet A hcard hK).app X σ) ⊆ A := by
  classical
  letI : DecidableEq (PV k) := LinearOrder.toDecidableEq
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨i, _, rfl⟩
  change (A.orderEmbOfFin hcard) (σ.down.hom.toOrderHom i) ∈ A
  exact Finset.orderEmbOfFin_mem A hcard _

private theorem simplexOfVertexSet_app_apply {k r : ℕ} (A : Finset (PV k))
    (hcard : A.card = r + 2) (hK : (dprismComplex k).S A)
    (X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ)
    (σ : (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk (r + 1))).obj X)
    (i : Fin (X.unop.obj.len + 1)) :
    ((simplexOfVertexSet A hcard hK).app X σ).down.1 i =
      (A.orderEmbOfFin hcard) (σ.down.hom.toOrderHom i) := rfl

private theorem simplexOfVertexSet_nonhorn_facet_subset {k r : ℕ} (A : Finset (PV k))
    (hcard : A.card = r + 2) (hK : (dprismComplex k).S A)
    (X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ) (j : Fin (r + 2))
    (σ : (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk (r + 1))).obj X)
    (hσ : σ ∉ (horn.{u} (r + 1) j).obj X) :
    A.erase (A.orderEmbOfFin hcard j) ⊆
      dprismVertices ((simplexOfVertexSet A hcard hK).app X σ) := by
  classical
  intro z hz
  rcases Finset.mem_erase.mp hz with ⟨hzk, hzA⟩
  let l : Fin (r + 2) := (A.orderIsoOfFin hcard).symm ⟨z, hzA⟩
  have hleq : A.orderEmbOfFin hcard l = z := by
    rw [← Finset.coe_orderIsoOfFin_apply A hcard l]
    simp [l]
  have hlj : l ≠ j := by
    intro h
    exact hzk (hleq.symm.trans (congrArg (A.orderEmbOfFin hcard) h))
  have hlRange : l ∈ Set.range (σ.down.hom.toOrderHom) := by
    by_contra hnot
    exact hσ ⟨l, hlj, hnot⟩
  rcases hlRange with ⟨i, hi⟩
  letI : DecidableEq (PV k) := LinearOrder.toDecidableEq
  apply Finset.mem_image.mpr
  refine ⟨i, Finset.mem_univ _, ?_⟩
  rw [simplexOfVertexSet_app_apply, hi]
  exact hleq

private theorem simplexOfVertexSet_horn_facet_subset {k r : ℕ} (A : Finset (PV k))
    (hcard : A.card = r + 2) (hK : (dprismComplex k).S A)
    (X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ) (j : Fin (r + 2))
    (σ : (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk (r + 1))).obj X)
    (hσ : σ ∈ (horn.{u} (r + 1) j).obj X) :
    ∃ l : Fin (r + 2), l ≠ j ∧
      dprismVertices ((simplexOfVertexSet A hcard hK).app X σ) ⊆
        A.erase (A.orderEmbOfFin hcard l) := by
  classical
  obtain ⟨l, hlj, hl⟩ := hσ
  refine ⟨l, hlj, ?_⟩
  intro z hz
  change z ∈ @Finset.image (Fin (X.unop.obj.len + 1)) (PV k)
    LinearOrder.toDecidableEq ((simplexOfVertexSet A hcard hK).app X σ).down.1
    Finset.univ at hz
  rcases (@Finset.mem_image (Fin (X.unop.obj.len + 1)) (PV k)
    LinearOrder.toDecidableEq ((simplexOfVertexSet A hcard hK).app X σ).down.1
    Finset.univ z).mp hz with ⟨i, -, hzi⟩
  apply Finset.mem_erase.mpr
  refine ⟨?_, ?_⟩
  · intro h
    apply hl
    exact ⟨i, (A.orderEmbOfFin hcard).injective (hzi.trans h)⟩
  · exact hzi ▸ Finset.orderEmbOfFin_mem A hcard (σ.down.hom.toOrderHom i)

private theorem simplexOfVertexSet_factor {k r : ℕ} (A : Finset (PV k))
    (hcard : A.card = r + 2) (hK : (dprismComplex k).S A)
    (X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ)
    (σ : (dprism.{u} k).obj X)
    (hverts : ∀ i, σ.down.1 i ∈ A) :
    ∃ τ : (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk (r + 1))).obj X,
      (simplexOfVertexSet A hcard hK).app X τ = σ := by
  classical
  letI : DecidableEq (PV k) := LinearOrder.toDecidableEq
  let e := A.orderEmbOfFin hcard
  let θ : Fin (X.unop.obj.len + 1) → Fin (r + 2) := fun i =>
    (A.orderIsoOfFin hcard).symm ⟨σ.down.1 i, hverts i⟩
  have hθ : StrictMono θ := by
    intro i j hij
    apply (A.orderIsoOfFin hcard).symm.strictMono
    exact σ.down.2.1 hij
  let o : Fin (X.unop.obj.len + 1) →o Fin (r + 2) := ⟨θ, hθ.monotone⟩
  let f : SimplexCategory.Hom X.unop.obj (SimplexCategory.mk (r + 1)) :=
    SimplexCategory.Hom.mk o
  have hf : Mono f := (SimplexCategory.mono_iff_injective).2 hθ.injective
  let τ : X.unop ⟶ HomotopyHypothesis.Henry.SemiSimplexCategory.mk (r + 1) := ⟨f, hf⟩
  refine ⟨ULift.up τ, ?_⟩
  apply ULift.ext
  apply Subtype.ext
  funext i
  change e (θ i) = σ.down.1 i
  simp [e, θ, Finset.orderEmbOfFin]

private def middleFaces {k : ℕ} (A : Finset (PV k)) :
    Finset (Finset (Fin (k + 1))) :=
  Finset.univ.filter fun S => PV.mid S ∈ A

private def topSet {k : ℕ} (A : Finset (PV k)) : Finset (Fin (k + 1)) :=
  Finset.univ.filter fun i => PV.top i ∈ A

private def middleCount {k : ℕ} (A : Finset (PV k)) : ℕ := (middleFaces A).card

private def topCount {k : ℕ} (A : Finset (PV k)) : ℕ := (topSet A).card

private def prismHigh {k : ℕ} (A : Finset (PV k)) : Prop :=
  (dprismComplex k).S A ∧ PV.mid (Finset.univ : Finset (Fin (k + 1))) ∈ A ∧
    (topSet A).Nonempty ∧ PV.mid (topSet A) ∈ A

private abbrev PrismCell (k : ℕ) := {A : Finset (PV k) // prismHigh A}

private noncomputable instance prismCellFintype {k : ℕ} : Fintype (PrismCell k) :=
  Fintype.ofFinite _

private theorem dprism_addFullMid_of_top {k : ℕ} (A : Finset (PV k))
    (hK : (dprismComplex k).S A) (hT : (topSet A).Nonempty) :
    (dprismComplex k).S
      (insert (PV.mid (Finset.univ : Finset (Fin (k + 1))) ) A) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro S hS
    rcases Finset.mem_insert.mp hS with h | h
    · injection h with hS
      subst S
      exact ⟨0, Finset.mem_univ _⟩
    · exact hK.1 S h
  · intro S S' hS hS'
    rcases Finset.mem_insert.mp hS with h | h
    · injection h with hS
      subst S
      rcases Finset.mem_insert.mp hS' with h' | h'
      · injection h' with hS'
        subst S'
        exact Or.inl (Finset.Subset.rfl)
      · exact Or.inr (Finset.subset_univ _)
    · rcases Finset.mem_insert.mp hS' with h' | h'
      · injection h' with hS'
        subst S'
        exact Or.inl (Finset.subset_univ _)
      · exact hK.2.1 S S' h h'
  · intro i S hi hS
    have hiA : PV.top i ∈ A := by
      rcases Finset.mem_insert.mp hi with h | h
      · cases h
      · exact h
    rcases Finset.mem_insert.mp hS with h | h
    · injection h with hS
      subst S
      exact Finset.mem_univ i
    · exact hK.2.2 i S hiA h

private theorem dprism_addTopPivot {k : ℕ} (A : Finset (PV k))
    (hK : (dprismComplex k).S A) (hT : (topSet A).Nonempty) :
    (dprismComplex k).S (insert (PV.mid (topSet A)) A) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro S hS
    rcases Finset.mem_insert.mp hS with h | h
    · injection h with hS
      subst S
      obtain ⟨i, hi⟩ := hT
      exact ⟨i, hi⟩
    · exact hK.1 S h
  · intro S S' hS hS'
    rcases Finset.mem_insert.mp hS with h | h
    · injection h with hS
      subst S
      rcases Finset.mem_insert.mp hS' with h' | h'
      · injection h' with hEq
        subst S'
        exact Or.inl (Finset.Subset.rfl)
      · have hsub : topSet A ⊆ S' := by
          intro i hi
          exact hK.2.2 i S' (Finset.mem_filter.mp hi).2 h'
        exact Or.inl hsub
    · rcases Finset.mem_insert.mp hS' with h' | h'
      · injection h' with hS'
        subst S'
        have hsub : topSet A ⊆ S := by
          intro i hi
          exact hK.2.2 i S (Finset.mem_filter.mp hi).2 h
        exact Or.inr hsub
      · exact hK.2.1 S S' h h'
  · intro i S hi hS
    have hiA : PV.top i ∈ A := by
      rcases Finset.mem_insert.mp hi with h | h
      · cases h
      · exact h
    rcases Finset.mem_insert.mp hS with h | h
    · injection h with hS
      subst S
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiA⟩
    · exact hK.2.2 i S hiA h

private theorem prismCell_card_ge_two {k : ℕ} (a : PrismCell k) : 2 ≤ a.val.card := by
  obtain ⟨i, hi⟩ := a.property.2.2.1
  have hlt : 1 < a.val.card := Finset.one_lt_card.mpr
    ⟨PV.mid (Finset.univ : Finset (Fin (k + 1))), a.property.2.1,
      PV.top i, (Finset.mem_filter.mp hi).2,
      by simp⟩
  omega

private noncomputable def prismCellSimplex {k : ℕ} (a : PrismCell k) :
    HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk (a.val.card - 2 + 1)) ⟶
        dprism.{u} k := by
  have hge := prismCell_card_ge_two a
  exact simplexOfVertexSet a.val (by omega) a.property.1

private def prismCellRank {k : ℕ} (a : PrismCell k) : ℕ ×ₗ ℕ :=
  toLex (topCount a.val, middleCount a.val)

private noncomputable def prismCellOrderRank {k : ℕ} (a : PrismCell k) :
    (ℕ ×ₗ ℕ) ×ₗ Fin (Fintype.card (PrismCell k)) :=
  toLex (prismCellRank a, Fintype.equivFin (PrismCell k) a)

private theorem prismCellOrderRank_injective {k : ℕ} :
    Function.Injective (prismCellOrderRank (k := k)) := by
  intro a b h
  change toLex (prismCellRank a, Fintype.equivFin (PrismCell k) a) =
    toLex (prismCellRank b, Fintype.equivFin (PrismCell k) b) at h
  have hp := toLex_inj.mp h
  exact (Fintype.equivFin (PrismCell k)).injective (Prod.mk.inj hp).2

private theorem prismCellOrderRank_lt_of_rank_lt {k : ℕ} {a b : PrismCell k}
    (h : prismCellRank a < prismCellRank b) : prismCellOrderRank a < prismCellOrderRank b := by
  change toLex (prismCellRank a, Fintype.equivFin (PrismCell k) a) <
    toLex (prismCellRank b, Fintype.equivFin (PrismCell k) b)
  rw [Prod.Lex.toLex_lt_toLex]
  exact Or.inl h

private noncomputable def prismCellPivotIndex {k : ℕ} (a : PrismCell k) :
    Fin (a.val.card - 2 + 2) := by
  have hcard : a.val.card = (a.val.card - 2) + 2 := by
    have h := prismCell_card_ge_two a
    omega
  exact (a.val.orderIsoOfFin hcard).symm
    ⟨PV.mid (topSet a.val), a.property.2.2.2⟩

private theorem prismCellPivotIndex_apply {k : ℕ} (a : PrismCell k)
    (hcard : a.val.card = (a.val.card - 2) + 2) :
    (a.val.orderEmbOfFin hcard) (prismCellPivotIndex a) = PV.mid (topSet a.val) := by
  simp [prismCellPivotIndex, Finset.orderEmbOfFin]

private theorem prismCell_topFacet_partner {k : ℕ} (a : PrismCell k)
    {i : Fin (k + 1)} (hi : PV.top i ∈ a.val)
    (hT : (topSet (a.val.erase (PV.top i))).Nonempty) :
    ∃ b : PrismCell k, a.val.erase (PV.top i) ⊆ b.val ∧
      prismCellRank b < prismCellRank a := by
  classical
  let A := a.val
  let F := A.erase (PV.top i)
  have hKF : (dprismComplex k).S F := (dprismComplex k).down (Finset.erase_subset _ _) a.property.1
  have htopSetF : topSet F = (topSet A).erase i := by
    ext j
    simp [topSet, F, A, Finset.mem_erase, hi]
  have hK := dprism_addTopPivot F hKF hT
  let B := insert (PV.mid (topSet F)) F
  have hfullF : PV.mid (Finset.univ : Finset (Fin (k + 1))) ∈ F :=
    Finset.mem_erase.mpr ⟨by simp, a.property.2.1⟩
  have hfullB : PV.mid (Finset.univ : Finset (Fin (k + 1))) ∈ B :=
    Finset.mem_insert_of_mem hfullF
  have htopSetB : topSet B = topSet F := by
    ext j
    simp [topSet, B]
  have htopB : (topSet B).Nonempty := by simpa [htopSetB] using hT
  have hpivotB : PV.mid (topSet B) ∈ B := by
    rw [htopSetB]
    exact Finset.mem_insert_self _ _
  let b : PrismCell k := ⟨B, ⟨hK, hfullB, htopB, hpivotB⟩⟩
  refine ⟨b, ?_, ?_⟩
  · exact Finset.subset_insert _ _
  · have himem : i ∈ topSet A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    have hcount : topCount B + 1 = topCount A := by
      change (topSet B).card + 1 = (topSet A).card
      rw [htopSetB, htopSetF, Finset.card_erase_of_mem himem]
      have hpos : 0 < (topSet A).card := Finset.card_pos.mpr ⟨i, himem⟩
      omega
    change toLex (topCount B, middleCount B) < toLex (topCount A, middleCount A)
    rw [Prod.Lex.toLex_lt_toLex]
    exact Or.inl (by omega)

private theorem prismCell_midFacet_partner {k : ℕ} (a : PrismCell k)
    {S : Finset (Fin (k + 1))} (hS : PV.mid S ∈ a.val)
    (hSneFull : S ≠ Finset.univ) (hSnePivot : S ≠ topSet a.val) :
    ∃ b : PrismCell k, a.val.erase (PV.mid S) ⊆ b.val ∧
      prismCellRank b < prismCellRank a := by
  classical
  let A := a.val
  let F := A.erase (PV.mid S)
  have hKF : (dprismComplex k).S F := (dprismComplex k).down (Finset.erase_subset _ _) a.property.1
  have hfullF : PV.mid Finset.univ ∈ F := by
    apply Finset.mem_erase.mpr
    refine ⟨?_, a.property.2.1⟩
    intro h
    injection h with hEq
    exact hSneFull hEq.symm
  have htopSetF : topSet F = topSet A := by
    ext i
    simp [topSet, F, A, Finset.mem_erase]
  have hpivotF : PV.mid (topSet A) ∈ F := by
    apply Finset.mem_erase.mpr
    refine ⟨?_, a.property.2.2.2⟩
    intro h
    injection h with hEq
    exact hSnePivot hEq.symm
  let b : PrismCell k := ⟨F, ⟨hKF, hfullF,
    by simpa [htopSetF] using a.property.2.2.1,
    by simpa [htopSetF] using hpivotF⟩⟩
  refine ⟨b, Finset.Subset.rfl, ?_⟩
  have hmidSets : middleFaces F = (middleFaces A).erase S := by
    ext T
    simp [middleFaces, F, A, Finset.mem_erase]
  have hSmem : S ∈ middleFaces A := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS⟩
  have hcount : middleCount F + 1 = middleCount A := by
    change (middleFaces F).card + 1 = (middleFaces A).card
    rw [hmidSets, Finset.card_erase_of_mem hSmem]
    have hpos : 0 < (middleFaces A).card := Finset.card_pos.mpr ⟨S, hSmem⟩
    omega
  change toLex (topCount F, middleCount F) < toLex (topCount A, middleCount A)
  rw [Prod.Lex.toLex_lt_toLex]
  exact Or.inr ⟨by simp [topCount, htopSetF], by omega⟩

private noncomputable def headFace {k : ℕ} (A : Finset (PV k)) :
    Finset (Fin (k + 1)) :=
  if h : (middleFaces A).Nonempty then
    Classical.choose (Finset.exists_max_image (middleFaces A) Finset.card h)
  else ∅

private theorem headFace_mem_of_mid {k : ℕ} {A : Finset (PV k)}
    (hmid : PV.mid (Finset.univ : Finset (Fin (k + 1))) ∈ A) : PV.mid (headFace A) ∈ A := by
  have hne : (middleFaces A).Nonempty := ⟨Finset.univ, by simp [middleFaces, hmid]⟩
  have hspec := Classical.choose_spec (Finset.exists_max_image (middleFaces A) Finset.card hne)
  have hmem : headFace A ∈ middleFaces A := by simp [headFace, hne, hspec.1]
  simpa [middleFaces] using hmem

private theorem headFace_superset_of_chain {k : ℕ} {A : Finset (PV k)}
    (hne : (middleFaces A).Nonempty)
    (hchain : ∀ S S', PV.mid S ∈ A → PV.mid S' ∈ A → S ⊆ S' ∨ S' ⊆ S)
    (S : Finset (Fin (k + 1))) (hS : PV.mid S ∈ A) : S ⊆ headFace A := by
  have hspec := Classical.choose_spec (Finset.exists_max_image (middleFaces A) Finset.card hne)
  have hhead : headFace A ∈ middleFaces A := by simp [headFace, hne, hspec.1]
  have hS' : S ∈ middleFaces A := by simp [middleFaces, hS]
  have hnest := hchain S (headFace A) hS (by simpa [middleFaces] using hhead)
  rcases hnest with h | h
  · exact h
  · have hmax : S.card ≤ (headFace A).card := by
      simpa [headFace, hne] using hspec.2 S hS'
    exact (Finset.eq_of_subset_of_card_le h hmax).symm.subset

private theorem erase_midFull_is_boundary {k : ℕ} (A : Finset (PV k))
    (hK : (dprismComplex k).S A)
    (hfull : PV.mid (Finset.univ : Finset (Fin (k + 1))) ∈ A)
    (hTopNotFull : ¬ ∀ i, PV.top i ∈ A) :
    (dprismBdryComplex k).S (A.erase (PV.mid Finset.univ)) := by
  classical
  let F := A.erase (PV.mid (Finset.univ : Finset (Fin (k + 1))))
  have hF : (dprismComplex k).S F := (dprismComplex k).down (Finset.erase_subset _ _) hK
  have hfullF : PV.mid (Finset.univ : Finset (Fin (k + 1))) ∉ F := by simp [F]
  have hside : (∀ i, PV.top i ∉ F) ∨
      ∃ i, PV.top i ∉ F ∧ ∀ S, PV.mid S ∈ F → i ∉ S := by
    by_cases hmidF : ∃ S, PV.mid S ∈ F
    · have hne : (middleFaces F).Nonempty := by
        rcases hmidF with ⟨S, hS⟩
        exact ⟨S, by simp [middleFaces, hS]⟩
      have hhead : PV.mid (headFace F) ∈ F := by
        have hh : headFace F ∈ middleFaces F := by
          let hspec := Classical.choose_spec
            (Finset.exists_max_image (middleFaces F) Finset.card hne)
          simpa [headFace, hne, hspec.1]
        simpa [middleFaces] using hh
      have hheadNe : headFace F ≠ (Finset.univ : Finset (Fin (k + 1))) := by
        intro heq
        exact hfullF (heq ▸ hhead)
      have hex : ∃ i, i ∉ headFace F := by
        by_contra h
        have hall : (Finset.univ : Finset (Fin (k + 1))) ⊆ headFace F := by
          intro i hi
          by_contra hnot
          exact h ⟨i, hnot⟩
        exact hheadNe (Finset.univ_subset_iff.mp hall)
      obtain ⟨i, hi⟩ := hex
      have htop : PV.top i ∉ F := by
        intro hti
        exact hi (hF.2.2 i (headFace F) hti hhead)
      refine Or.inr ⟨i, htop, ?_⟩
      intro S hS
      have hsubset := headFace_superset_of_chain hne
        (fun S₁ S₂ h₁ h₂ => hF.2.1 S₁ S₂ h₁ h₂) S hS
      exact fun hmem => hi (hsubset hmem)
    · obtain ⟨i, hi⟩ := Classical.not_forall.mp hTopNotFull
      refine Or.inr ⟨i, ?_, ?_⟩
      · intro h
        have hsub : A.erase (PV.mid Finset.univ) ⊆ A := Finset.erase_subset _ _
        exact hi (hsub h)
      · intro S hS
        exact False.elim (hmidF ⟨S, hS⟩)
  exact ⟨hF, hside⟩

private theorem prismCell_missingFacet_coface_rank {k : ℕ} (a b : PrismCell k)
    (hba : a ≠ b) (hsub : a.val.erase (PV.mid (topSet a.val)) ⊆ b.val) :
    prismCellRank a < prismCellRank b := by
  classical
  let A := a.val
  let B := b.val
  have htopSub : topSet A ⊆ topSet B := by
    intro i hi
    have htopA : PV.top i ∈ A := (Finset.mem_filter.mp hi).2
    have htopErase : PV.top i ∈ A.erase (PV.mid (topSet A)) :=
      Finset.mem_erase.mpr ⟨by simp, htopA⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsub htopErase⟩
  have htopLe : topCount A ≤ topCount B := Finset.card_le_card htopSub
  by_cases htopLt : topCount A < topCount B
  · change toLex (topCount A, middleCount A) < toLex (topCount B, middleCount B)
    rw [Prod.Lex.toLex_lt_toLex]
    exact Or.inl htopLt
  · have htopEq : topCount A = topCount B := by omega
    have htopSetEq : topSet A = topSet B :=
      Finset.eq_of_subset_of_card_le htopSub (by simpa [topCount] using htopEq.ge)
    have hmidSub : middleFaces A ⊆ middleFaces B := by
      intro S hS
      have hmidA : PV.mid S ∈ A := by simpa [middleFaces] using hS
      by_cases hST : S = topSet A
      · subst S
        have hmidB : PV.mid (topSet B) ∈ B := b.property.2.2.2
        have hmem : topSet B ∈ middleFaces B := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmidB⟩
        rw [htopSetEq]
        exact hmem
      · have hmidErase : PV.mid S ∈ A.erase (PV.mid (topSet A)) := by
          apply Finset.mem_erase.mpr
          refine ⟨?_, hmidA⟩
          intro heq
          injection heq with hEq
          exact hST hEq
        exact by simpa [middleFaces] using hsub hmidErase
    have hmidLe : middleCount A ≤ middleCount B := Finset.card_le_card hmidSub
    by_cases hmidLt : middleCount A < middleCount B
    · change toLex (topCount A, middleCount A) < toLex (topCount B, middleCount B)
      rw [Prod.Lex.toLex_lt_toLex]
      exact Or.inr ⟨htopEq, hmidLt⟩
    · have hmidEq : middleCount A = middleCount B := by omega
      have hmidSetEq : middleFaces A = middleFaces B :=
        Finset.eq_of_subset_of_card_le hmidSub (by simpa [middleCount] using hmidEq.ge)
      have hAB : A = B := by
        ext z
        cases z with
        | top i =>
            have hA : PV.top i ∈ A ↔ i ∈ topSet A := by simp [topSet]
            have hB : PV.top i ∈ B ↔ i ∈ topSet B := by simp [topSet]
            rw [hA, hB, htopSetEq]
        | mid S =>
            have hA : PV.mid S ∈ A ↔ S ∈ middleFaces A := by simp [middleFaces]
            have hB : PV.mid S ∈ B ↔ S ∈ middleFaces B := by simp [middleFaces]
            rw [hA, hB, hmidSetEq]
      exact False.elim (hba (Subtype.ext hAB))

private theorem prismCell_otherFacet {k : ℕ} (a : PrismCell k)
    (z : PV k) (hz : z ∈ a.val) (hzPivot : z ≠ PV.mid (topSet a.val)) :
    (dprismBdryComplex k).S (a.val.erase z) ∨
      ∃ b : PrismCell k, a.val.erase z ⊆ b.val ∧ prismCellRank b < prismCellRank a := by
  classical
  cases z with
  | top i =>
      have htop : PV.top i ∈ a.val := hz
      by_cases hT : (topSet (a.val.erase (PV.top i))).Nonempty
      · exact Or.inr (prismCell_topFacet_partner a htop hT)
      · apply Or.inl
        refine ⟨(dprismComplex k).down (Finset.erase_subset _ _) a.property.1, ?_⟩
        exact Or.inl (fun j hj => hT ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩)
  | mid S =>
      have hmid : PV.mid S ∈ a.val := hz
      by_cases hfull : S = Finset.univ
      · subst S
        have hTopNotFull : ¬ ∀ i, PV.top i ∈ a.val := by
          intro hall
          have hT : topSet a.val = Finset.univ := by
            ext i
            simp [topSet, hall]
          apply hzPivot
          exact congrArg PV.mid hT.symm
        exact Or.inl (erase_midFull_is_boundary a.val a.property.1 a.property.2.1 hTopNotFull)
      · have hSnePivot : S ≠ topSet a.val := by
          intro h
          apply hzPivot
          exact congrArg PV.mid h
        exact Or.inr (prismCell_midFacet_partner a hmid hfull hSnePivot)

private theorem prismMissingFacet_notBoundary {k : ℕ} (a : PrismCell k) :
    ¬ (dprismBdryComplex k).S (a.val.erase (PV.mid (topSet a.val))) := by
  classical
  intro hB
  let F := a.val.erase (PV.mid (topSet a.val))
  obtain ⟨j, hj⟩ := a.property.2.2.1
  have htopA : PV.top j ∈ a.val := (Finset.mem_filter.mp hj).2
  have htopF : PV.top j ∈ F := Finset.mem_erase.mpr ⟨by simp, htopA⟩
  rcases hB.2 with hNoTop | ⟨i, hi, hside⟩
  · exact hNoTop j htopF
  · by_cases hiT : i ∈ topSet a.val
    · have htopi : PV.top i ∈ a.val := (Finset.mem_filter.mp hiT).2
      exact hi (Finset.mem_erase.mpr ⟨by simp, htopi⟩)
    · by_cases hTfull : topSet a.val = Finset.univ
      · exact hiT (hTfull.symm ▸ Finset.mem_univ i)
      · have hfullF : PV.mid Finset.univ ∈ F := by
          apply Finset.mem_erase.mpr
          refine ⟨?_, a.property.2.1⟩
          intro heq
          injection heq with hEq
          exact hTfull hEq.symm
        exact hside _ hfullF (Finset.mem_univ i)

private def boundaryStage {k : ℕ} : Subfunctor (dprism.{u} k) :=
  Subfunctor.range (dprismBdryι.{u} k)

private theorem boundaryStage_of_vertices {k : ℕ}
    (X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ)
    (x : (dprism.{u} k).obj X)
    (hB : (dprismBdryComplex k).S (dprismVertices x)) :
    x ∈ (boundaryStage (k := k)).obj X := by
  classical
  let y : (dprismBdryComplex k).Simplex X.unop.obj.len :=
    ⟨x.down.1, x.down.2.1, by simpa [dprismVertices] using hB⟩
  refine ⟨ULift.up y, ?_⟩
  apply ULift.ext
  apply Subtype.ext
  rfl

private theorem boundaryStage_vertices {k : ℕ}
    (X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ)
    (x : (dprism.{u} k).obj X)
    (hx : x ∈ (boundaryStage (k := k)).obj X) :
    (dprismBdryComplex k).S (dprismVertices x) := by
  classical
  letI : DecidableEq (PV k) := LinearOrder.toDecidableEq
  rcases hx with ⟨y, hy⟩
  have hfun : y.down.1 = x.down.1 := by
    funext i
    have h := congrArg (fun z => z.1 i) (congrArg ULift.down hy)
    change y.down.1 i = x.down.1 i at h
    exact h
  have hB := y.down.2.2
  rw [hfun] at hB
  simpa [dprismVertices] using hB

private noncomputable def prismStage {k : ℕ} (H : Finset (PrismCell k)) :
    Subfunctor (dprism.{u} k) :=
  boundaryStage (k := k) ⊔ H.sup (fun a => Subfunctor.range (prismCellSimplex a))

private theorem prismStage_insert {k : ℕ} (H : Finset (PrismCell k)) (a : PrismCell k) :
    prismStage (insert a H) =
      prismStage H ⊔ Subfunctor.range (prismCellSimplex a) := by
  classical
  simp [prismStage, Finset.sup_insert, sup_assoc, sup_comm, sup_left_comm]

private theorem prismStage_mem_iff {k : ℕ} (H : Finset (PrismCell k))
    (X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ)
    (x : (dprism.{u} k).obj X) :
    x ∈ (prismStage H).obj X ↔
      x ∈ (boundaryStage (k := k)).obj X ∨
        ∃ a ∈ H, x ∈ (Subfunctor.range (prismCellSimplex a)).obj X := by
  classical
  induction H using Finset.induction_on with
  | empty => simp [prismStage]
  | @insert a H ha ih =>
      rw [prismStage_insert, Subfunctor.max_obj, Set.mem_union]
      constructor
      · rintro (hx | hx)
        · rcases ih.mp hx with hb | ⟨b, hbH, hb⟩
          · exact Or.inl hb
          · exact Or.inr ⟨b, Finset.mem_insert_of_mem hbH, hb⟩
        · exact Or.inr ⟨a, Finset.mem_insert_self a H, hx⟩
      · rintro (hb | ⟨b, hbH, hx⟩)
        · exact Or.inl (ih.mpr (Or.inl hb))
        · rcases Finset.mem_insert.mp hbH with rfl | hbH
          · exact Or.inr hx
          · exact Or.inl (ih.mpr (Or.inr ⟨b, hbH, hx⟩))

private theorem mem_prismCellRange_of_vertices_subset {k : ℕ} (a : PrismCell k)
    (X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ)
    (x : (dprism.{u} k).obj X) (hverts : dprismVertices x ⊆ a.val) :
    x ∈ (Subfunctor.range (prismCellSimplex a)).obj X := by
  classical
  letI : DecidableEq (PV k) := LinearOrder.toDecidableEq
  have hcard : a.val.card = (a.val.card - 2) + 2 := by
    have h := prismCell_card_ge_two a
    omega
  have hverts' : ∀ i, x.down.1 i ∈ a.val := by
    intro i
    have hi : x.down.1 i ∈ dprismVertices x := by
      change x.down.1 i ∈ @Finset.image (Fin (X.unop.obj.len + 1)) (PV k)
        LinearOrder.toDecidableEq x.down.1 Finset.univ
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    exact hverts hi
  obtain ⟨τ, hτ⟩ := simplexOfVertexSet_factor a.val hcard a.property.1 X x hverts'
  refine ⟨τ, ?_⟩
  simpa [prismCellSimplex] using hτ

private theorem prismCellRange_vertices_subset {k : ℕ} (a : PrismCell k)
    (X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ)
    (x : (dprism.{u} k).obj X)
    (hx : x ∈ (Subfunctor.range (prismCellSimplex a)).obj X) :
    dprismVertices x ⊆ a.val := by
  classical
  letI : DecidableEq (PV k) := LinearOrder.toDecidableEq
  have hcard : a.val.card = (a.val.card - 2) + 2 := by
    have h := prismCell_card_ge_two a
    omega
  rcases hx with ⟨σ, hσ⟩
  rw [← hσ]
  simpa [prismCellSimplex] using
    (simplexOfVertexSet_vertices_subset a.val hcard a.property.1 X σ)

private theorem elementary_anodyne_of_isPushout {A B D E : SemiSSet.{u}}
    {f : A ⟶ B} {g : A ⟶ D} {f' : D ⟶ E} {g' : B ⟶ E}
    (sq : IsPushout g f f' g')
    (hf : (hornInclusions.pushouts ⊔ MorphismProperty.isomorphisms SemiSSet.{u}) f) :
    (hornInclusions.pushouts ⊔ MorphismProperty.isomorphisms SemiSSet.{u}) f' := by
  rcases hf with hf | hf
  · exact Or.inl (MorphismProperty.of_isPushout sq hf)
  · haveI : IsIso f := hf
    exact Or.inr sq.isIso_inl_of_isIso

private theorem anodyne_of_isPushout {A B D E : SemiSSet.{u}}
    {f : A ⟶ B} {g : A ⟶ D} {f' : D ⟶ E} {g' : B ⟶ E}
    (sq : IsPushout g f f' g') (hf : anodyne f) : anodyne f' := by
  unfold anodyne at hf ⊢
  induction hf generalizing D E with
  | of f hf => exact .of _ (elementary_anodyne_of_isPushout sq hf)
  | id A => exact .of _ (Or.inr sq.isIso_inl_of_isIso)
  | @comp_of A B C f h hf hh ih =>
      have left := IsPushout.of_hasPushout g f
      have right := sq.of_top' left
      have hi := ih left
      have ht := elementary_anodyne_of_isPushout right hh
      simpa only [IsPushout.inl_desc] using
        MorphismProperty.multiplicativeClosure.comp_of _ _ hi ht

private theorem anodyne_horn {r : ℕ} (j : Fin (r + 2)) :
    anodyne ((horn.{u} (r + 1) j).ι) := by
  unfold anodyne
  apply MorphismProperty.multiplicativeClosure.of
  apply Or.inl
  apply hornInclusions.le_pushouts
  change MorphismProperty.ofHoms
    (fun p : Σ d : ℕ, Fin (d + 2) => (horn.{u} (p.1 + 1) p.2).ι)
    ((horn.{u} (r + 1) j).ι)
  exact MorphismProperty.ofHoms.mk
    (f := fun p : Σ d : ℕ, Fin (d + 2) => (horn.{u} (p.1 + 1) p.2).ι) ⟨r, j⟩

private theorem isPushout_hornCell {r : ℕ} (j : Fin (r + 2))
    {K : SemiSSet.{u}} (S : Subfunctor K)
    (η : HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk (r + 1)) ⟶ K) [Mono η]
    (hfaces : Subfunctor.range ((horn.{u} (r + 1) j).ι ≫ η) ≤ S)
    (hinter : ∀ (X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ)
      (x : (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk (r + 1))).obj X),
      η.app X x ∈ S.obj X → x ∈ (horn.{u} (r + 1) j).obj X) :
    IsPushout (horn.{u} (r + 1) j).ι
      (Subfunctor.lift ((horn.{u} (r + 1) j).ι ≫ η) hfaces)
      (Subfunctor.lift η (G := Subfunctor.range η) (by rfl) ≫
        Subfunctor.homOfLe (G := Subfunctor.range η)
          (le_sup_right : Subfunctor.range η ≤ S ⊔ Subfunctor.range η))
      (Subfunctor.homOfLe (G := S) (le_sup_left : S ≤ S ⊔ Subfunctor.range η)) := by
  let g := Subfunctor.lift ((horn.{u} (r + 1) j).ι ≫ η) hfaces
  have hcomm : (horn.{u} (r + 1) j).ι ≫ η = g ≫ S.ι := by simp [g]
  exact isPushout_subfunctor_sup_range
    (C := HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ)
    (horn.{u} (r + 1) j) S η g hcomm hinter

private theorem anodyne_subfunctor_hornStep {r : ℕ} (j : Fin (r + 2))
    {K : SemiSSet.{u}} (S T : Subfunctor K)
    (η : HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk (r + 1)) ⟶ K) [Mono η]
    (hfaces : Subfunctor.range ((horn.{u} (r + 1) j).ι ≫ η) ≤ S)
    (hinter : ∀ (X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ)
      (x : (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk (r + 1))).obj X),
      η.app X x ∈ S.obj X → x ∈ (horn.{u} (r + 1) j).obj X)
    (hT : T = S ⊔ Subfunctor.range η) (hle : S ≤ T) : anodyne (Subfunctor.homOfLe hle) := by
  subst T
  have hsq := isPushout_hornCell j S η hfaces hinter
  have hh := anodyne_of_isPushout hsq.flip (anodyne_horn j)
  simpa using hh

private theorem prismCell_hornStep {k : ℕ}
    (H : Finset (PrismCell k)) (a : PrismCell k)
    (hDown : ∀ b : PrismCell k,
      prismCellOrderRank b < prismCellOrderRank a → b ∈ H)
    (hUpper : ∀ b : PrismCell k, b ∈ H → prismCellOrderRank b < prismCellOrderRank a) :
    anodyne.{u} (Subfunctor.homOfLe
      (show prismStage H ≤ prismStage (insert a H) from by
        rw [prismStage_insert]
        exact le_sup_left)) := by
  classical
  let S := prismStage H
  let T := prismStage (insert a H)
  let η := prismCellSimplex a
  let r := a.val.card - 2
  have hge := prismCell_card_ge_two a
  have hcard : a.val.card = r + 2 := by dsimp [r]; omega
  let j : Fin (r + 2) := prismCellPivotIndex a
  have hPivotIndex : (a.val.orderEmbOfFin hcard) j = PV.mid (topSet a.val) := by
    simpa [j] using prismCellPivotIndex_apply a hcard
  have hmono : Mono η := by
    dsimp [η, prismCellSimplex]
    exact simplexOfVertexSet_mono a.val hcard a.property.1
  letI : Mono η := hmono
  have hfaces : Subfunctor.range ((horn.{u} (r + 1) j).ι ≫ η) ≤ S := by
    intro X x hx
    rcases hx with ⟨τ, rfl⟩
    rcases τ with ⟨σ, hσ⟩
    change η.app X σ ∈ S.obj X
    obtain ⟨l, hlj, hverts⟩ := simplexOfVertexSet_horn_facet_subset
      a.val hcard a.property.1 X j σ hσ
    have hverts' : dprismVertices (η.app X σ) ⊆
        a.val.erase (a.val.orderEmbOfFin hcard l) := by
      simpa [η, prismCellSimplex] using hverts
    let z := (a.val.orderEmbOfFin hcard) l
    have hz : z ∈ a.val := Finset.orderEmbOfFin_mem a.val hcard l
    have hzj : z ≠ PV.mid (topSet a.val) := by
      intro h
      apply hlj
      apply (a.val.orderEmbOfFin hcard).injective
      calc
        (a.val.orderEmbOfFin hcard) l = z := rfl
        _ = PV.mid (topSet a.val) := h
        _ = (a.val.orderEmbOfFin hcard) j := hPivotIndex.symm
    rcases prismCell_otherFacet a z hz hzj with hboundary | ⟨b, hfacet, hbrank⟩
    · have hboundary' : (dprismBdryComplex k).S (dprismVertices (η.app X σ)) :=
        (dprismBdryComplex k).down hverts' hboundary
      exact (prismStage_mem_iff H X (η.app X σ)).2
        (Or.inl (boundaryStage_of_vertices X (η.app X σ) hboundary'))
    · have hb : b ∈ H := hDown b (prismCellOrderRank_lt_of_rank_lt hbrank)
      have hxrange : η.app X σ ∈ (Subfunctor.range (prismCellSimplex b)).obj X :=
        mem_prismCellRange_of_vertices_subset b X (η.app X σ)
          (Finset.Subset.trans hverts' hfacet)
      exact (prismStage_mem_iff H X (η.app X σ)).2 (Or.inr ⟨b, hb, hxrange⟩)
  have hNoBoundary := prismMissingFacet_notBoundary a
  have hinter : ∀ (X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ)
      (σ : (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk (r + 1))).obj X),
      η.app X σ ∈ S.obj X → σ ∈ (horn.{u} (r + 1) j).obj X := by
    intro X σ hσS
    by_contra hσ
    have hmissing : a.val.erase (PV.mid (topSet a.val)) ⊆
        dprismVertices (η.app X σ) := by
      simpa [η, prismCellSimplex, j, hPivotIndex] using
        (simplexOfVertexSet_nonhorn_facet_subset a.val hcard a.property.1 X j σ hσ)
    rcases (prismStage_mem_iff H X (η.app X σ)).1 hσS with hbnd | ⟨b, hb, hrange⟩
    · have hboundary := boundaryStage_vertices X (η.app X σ) hbnd
      exact hNoBoundary ((dprismBdryComplex k).down hmissing hboundary)
    · have hverts := prismCellRange_vertices_subset b X (η.app X σ) hrange
      have hcoface : a.val.erase (PV.mid (topSet a.val)) ⊆ b.val :=
        Finset.Subset.trans hmissing hverts
      have hba : a ≠ b := by
        intro hab
        subst b
        exact (lt_irrefl _ (hUpper a hb))
      have hrank := prismCell_missingFacet_coface_rank a b hba hcoface
      have htotal := prismCellOrderRank_lt_of_rank_lt hrank
      exact lt_asymm htotal (hUpper b hb)
  have hT : T = S ⊔ Subfunctor.range η := by
    simpa [T, S, η] using prismStage_insert H a
  have hle : S ≤ T := by rw [hT]; exact le_sup_left
  exact anodyne_subfunctor_hornStep j S T η hfaces hinter hT hle

private theorem subfunctor_homOfLe_comp {C : Type v} [Category.{w} C]
    {F : C ⥤ Type u} {A B D : Subfunctor F}
    (hAB : A ≤ B) (hBD : B ≤ D) :
    Subfunctor.homOfLe hAB ≫ Subfunctor.homOfLe hBD =
      Subfunctor.homOfLe (hAB.trans hBD) := by
  ext X x
  rfl

private theorem anodyne_comp {A B C : SemiSSet.{u}}
    {f : A ⟶ B} {g : B ⟶ C} (hf : anodyne f) (hg : anodyne g) :
    anodyne (f ≫ g) := by
  unfold anodyne at hf hg ⊢
  induction hg generalizing A with
  | of g hg => exact MorphismProperty.multiplicativeClosure.comp_of f g hf hg
  | id _ => simpa using hf
  | comp_of g₁ g₂ hg₁ hg₂ ih =>
      rw [← Category.assoc]
      exact MorphismProperty.multiplicativeClosure.comp_of _ _ (ih hf) hg₂

private def prismCellsDownClosed {k : ℕ} (H : Finset (PrismCell k)) : Prop :=
  ∀ a ∈ H, ∀ b, prismCellOrderRank b < prismCellOrderRank a → b ∈ H

private theorem prismStage_downClosed_anodyne {k : ℕ} (H : Finset (PrismCell k))
    (hdown : prismCellsDownClosed H) :
    anodyne.{u} (Subfunctor.homOfLe
      (show boundaryStage (k := k) ≤ prismStage H from le_sup_left)) := by
  classical
  induction H using Finset.induction_on_max_value (prismCellOrderRank (k := k)) with
  | empty =>
      let f : (boundaryStage (k := k)).toFunctor ⟶ (prismStage (∅ : Finset (PrismCell k))).toFunctor :=
        Subfunctor.homOfLe (show boundaryStage (k := k) ≤ prismStage ∅ from le_sup_left)
      have hEq : prismStage (∅ : Finset (PrismCell k)) = boundaryStage := by simp [prismStage]
      have hIso : IsIso.{u, u + 1} f := by
        rw [NatTrans.isIso_iff_isIso_app]
        intro X
        rw [isIso_iff_bijective]
        constructor
        · exact (mono_iff_injective _).1 inferInstance
        · intro y
          have hy : y.val ∈ (boundaryStage (k := k)).obj X := by
            rw [← hEq]
            exact y.property
          refine ⟨⟨y.val, hy⟩, ?_⟩
          apply Subtype.ext
          rfl
      unfold anodyne
      exact MorphismProperty.multiplicativeClosure.of _
        (Or.inr (MorphismProperty.isomorphisms.infer_property _))
  | insert a H ha hmax ih =>
      have hdownH : prismCellsDownClosed H := by
        intro b hb c hcb
        have hc := hdown b (Finset.mem_insert_of_mem hb) c hcb
        rcases Finset.mem_insert.mp hc with hca | hcH
        · subst c
          exact False.elim ((not_lt_of_ge (hmax b hb)) hcb)
        · exact hcH
      have hLower : ∀ b : PrismCell k,
          prismCellOrderRank b < prismCellOrderRank a → b ∈ H := by
        intro b hba
        have hb := hdown a (Finset.mem_insert_self a H) b hba
        rcases Finset.mem_insert.mp hb with hEq | hbH
        · subst b
          exact False.elim (lt_irrefl _ hba)
        · exact hbH
      have hUpper : ∀ b : PrismCell k, b ∈ H →
          prismCellOrderRank b < prismCellOrderRank a := by
        intro b hb
        have hle := hmax b hb
        by_contra hnot
        have heq : prismCellOrderRank b = prismCellOrderRank a :=
          le_antisymm hle (le_of_not_gt hnot)
        have hba : b = a := prismCellOrderRank_injective heq
        subst b
        exact ha hb
      have hIH := ih hdownH
      have hstep := prismCell_hornStep H a hLower hUpper
      have hle₁ : boundaryStage (k := k) ≤ prismStage H := le_sup_left
      have hle₂ : prismStage H ≤ prismStage (insert a H) := by
        rw [prismStage_insert]
        exact le_sup_left
      have hcomp := anodyne_comp hIH hstep
      rw [subfunctor_homOfLe_comp hle₁ hle₂] at hcomp
      exact hcomp

private theorem prismStage_all_anodyne {k : ℕ} :
    anodyne.{u} (Subfunctor.homOfLe
      (show boundaryStage (k := k) ≤ prismStage Finset.univ from le_sup_left)) := by
  apply prismStage_downClosed_anodyne
  intro a ha b hba
  exact Finset.mem_univ b

private theorem prismStage_contains_all {k : ℕ}
    (X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ)
    (x : (dprism.{u} k).obj X) : x ∈ (prismStage (Finset.univ : Finset (PrismCell k))).obj X := by
  classical
  let A := dprismVertices x
  have hK : (dprismComplex k).S A := x.down.2.2
  by_cases hB : (dprismBdryComplex k).S A
  · exact (prismStage_mem_iff Finset.univ X x).2
      (Or.inl (boundaryStage_of_vertices X x hB))
  · have hNoTop : ¬ (∀ i, PV.top i ∉ A) := by
      intro hall
      exact hB ⟨hK, Or.inl hall⟩
    obtain ⟨i, hi⟩ := Classical.not_forall.mp hNoTop
    have hiA : PV.top i ∈ A := by
      by_contra hnot
      exact hi hnot
    have hT : (topSet A).Nonempty :=
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiA⟩⟩
    let F := insert (PV.mid (Finset.univ : Finset (Fin (k + 1)))) A
    have hKF : (dprismComplex k).S F := by
      simpa [F] using dprism_addFullMid_of_top A hK hT
    have htopSetF : topSet F = topSet A := by
      ext j
      simp [topSet, F]
    have hTF : (topSet F).Nonempty := by rw [htopSetF]; exact hT
    let B := insert (PV.mid (topSet F)) F
    have hKB : (dprismComplex k).S B := by
      simpa [B] using dprism_addTopPivot F hKF hTF
    have htopSetB : topSet B = topSet F := by
      ext j
      simp [topSet, B]
    have hfullB : PV.mid (Finset.univ : Finset (Fin (k + 1))) ∈ B :=
      Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have hTB : (topSet B).Nonempty := by rw [htopSetB, htopSetF]; exact hT
    have hpivotB : PV.mid (topSet B) ∈ B := by
      rw [htopSetB]
      exact Finset.mem_insert_self _ _
    let b : PrismCell k := ⟨B, ⟨hKB, hfullB, hTB, hpivotB⟩⟩
    have hverts : dprismVertices x ⊆ b.val := by
      intro z hz
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz)
    have hrange := mem_prismCellRange_of_vertices_subset b X x hverts
    exact (prismStage_mem_iff Finset.univ X x).2
      (Or.inr ⟨b, Finset.mem_univ _, hrange⟩)

private theorem prismStage_all_eq_top {k : ℕ} :
    prismStage (Finset.univ : Finset (PrismCell k)) = ⊤ := by
  apply le_antisymm
  · exact le_top
  · intro X x hx
    exact prismStage_contains_all X x

/-- The derived cylinder of a simplex collapses onto its derived end and proper-face cylinders. -/
theorem anodyne_dprismBdryι_proof (k : ℕ) :
    anodyne (dprismBdryι.{u} k) := by
  classical
  let η := dprismBdryι.{u} k
  have hmono : Mono η := by
    rw [NatTrans.mono_iff_mono_app]
    intro X
    apply (mono_iff_injective _).2
    intro x y hxy
    apply ULift.ext
    apply Subtype.ext
    have hfun := congrArg (fun z => z.down.1) hxy
    change x.down.1 = y.down.1 at hfun
    exact hfun
  letI : Mono η := hmono
  have hStage : anodyne (Subfunctor.homOfLe
      (show boundaryStage (k := k) ≤ prismStage Finset.univ from le_sup_left)) :=
    prismStage_all_anodyne
  have hfull : prismStage (Finset.univ : Finset (PrismCell k)) = ⊤ :=
    prismStage_all_eq_top
  haveI : IsIso (Subfunctor.ι (prismStage (Finset.univ : Finset (PrismCell k)))) := by
    rw [hfull]
    infer_instance
  have hstageι : anodyne
      (Subfunctor.ι (prismStage (Finset.univ : Finset (PrismCell k)))) := by
    unfold anodyne
    apply MorphismProperty.multiplicativeClosure.of
    exact Or.inr (MorphismProperty.isomorphisms.infer_property _)
  have hboundaryStageι : anodyne (Subfunctor.ι (boundaryStage (k := k))) := by
    have hcomp := anodyne_comp hStage hstageι
    rw [Subfunctor.homOfLe_ι] at hcomp
    exact hcomp
  have htoRange : IsIso (Subfunctor.toRange η) := inferInstance
  have htoRangeAnodyne : anodyne (Subfunctor.toRange η) := by
    unfold anodyne
    apply MorphismProperty.multiplicativeClosure.of
    exact Or.inr (MorphismProperty.isomorphisms.infer_property _)
  have hfinal := anodyne_comp htoRangeAnodyne hboundaryStageι
  change anodyne (Subfunctor.toRange η ≫ (Subfunctor.range η).ι) at hfinal
  rw [Subfunctor.toRange_ι] at hfinal
  exact hfinal

#print axioms anodyne_dprismBdryι_proof


end HomotopyHypothesis.Approximation.DerivedPrismCollapse
