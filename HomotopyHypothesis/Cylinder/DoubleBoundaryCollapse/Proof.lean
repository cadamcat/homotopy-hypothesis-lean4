import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DV
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylD
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDBoundary
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDBoundaryComplex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDBoundaryIota
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDComplex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.Inst57
/-!
# Collapsing a derived double cylinder

The boundary inclusion is built by attaching the mapping-cylinder and prism simplices along horns.
-/

universe u v w

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Cylinder.DoubleBoundaryCollapse

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet
open HomotopyHypothesis.Approximation.Topological

private def dvEncode {n m : ℕ} : DV n m →
    (Fin (n + 1) ⊕ Finset (Fin (n + 1))) ⊕ Fin (m + 1)
  | .top i => Sum.inl (Sum.inl i)
  | .mid S => Sum.inl (Sum.inr S)
  | .bot c => Sum.inr c

private theorem dvEncode_injective {n m : ℕ} :
    Function.Injective (dvEncode : DV n m →
      (Fin (n + 1) ⊕ Finset (Fin (n + 1))) ⊕ Fin (m + 1)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [dvEncode]

private noncomputable instance dvFintype {n m : ℕ} : Fintype (DV n m) :=
  Fintype.ofInjective dvEncode dvEncode_injective

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

private noncomputable def simplexOfVertexSet {n m r : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) (A : Finset (DV n m))
    (hcard : A.card = r + 2) (hK : (dcylDComplex v).S A) :
    HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk (r + 1)) ⟶ dcylD.{u} v := by
  classical
  letI : DecidableEq (DV n m) := LinearOrder.toDecidableEq
  let e := A.orderEmbOfFin hcard
  refine
    { app := fun X => ↾fun σ => ULift.up
        ⟨(fun i => e (σ.down.hom.toOrderHom i)), ?_, ?_⟩
      naturality := ?_ }
  · exact e.strictMono.comp (HomotopyHypothesis.Approximation.Topological.SemiSimplexCategory.strictMono σ.down)
  · refine (dcylDComplex v).down ?_ hK
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

private theorem simplexOfVertexSet_mono {n m r : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) (A : Finset (DV n m))
    (hcard : A.card = r + 2) (hK : (dcylDComplex v).S A) :
    Mono (simplexOfVertexSet v A hcard hK) := by
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

private noncomputable def dcylVertices {n m : ℕ} {v : Fin (n + 1) → Fin (m + 1)}
    {X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ}
    (σ : dcylD.{u} v |>.obj X) : Finset (DV n m) :=
  @Finset.image (Fin (X.unop.obj.len + 1)) (DV n m)
    LinearOrder.toDecidableEq σ.down.1 Finset.univ

private theorem dcylVertices_eq_image {n m : ℕ} {v : Fin (n + 1) → Fin (m + 1)}
    {X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ} (σ : (dcylD.{u} v).obj X) :
    dcylVertices σ = @Finset.image (Fin (X.unop.obj.len + 1)) (DV n m)
      LinearOrder.toDecidableEq σ.down.1 Finset.univ := rfl

private theorem dcylVertices_eq_linearImage {n m : ℕ} {v : Fin (n + 1) → Fin (m + 1)}
    {X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ} (σ : (dcylD.{u} v).obj X) :
    dcylVertices σ = @Finset.image (Fin (X.unop.obj.len + 1)) (DV n m)
      LinearOrder.toDecidableEq σ.down.1 Finset.univ := rfl

private def eraseDV {n m : ℕ} (A : Finset (DV n m)) (z : DV n m) : Finset (DV n m) :=
  A.erase z

private theorem dcylVertices_simplexOfVertexSet_subset {n m r : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) (A : Finset (DV n m))
    (hcard : A.card = r + 2) (hK : (dcylDComplex v).S A)
    (X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ)
    (σ : (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk (r + 1))).obj X) :
    dcylVertices ((simplexOfVertexSet v A hcard hK).app X σ) ⊆ A := by
  classical
  letI : DecidableEq (DV n m) := LinearOrder.toDecidableEq
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨i, _, rfl⟩
  change (A.orderEmbOfFin hcard) (σ.down.hom.toOrderHom i) ∈ A
  exact Finset.orderEmbOfFin_mem A hcard _

private theorem simplexOfVertexSet_app_apply {n m r : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) (A : Finset (DV n m))
    (hcard : A.card = r + 2) (hK : (dcylDComplex v).S A)
    (X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ)
    (σ : (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk (r + 1))).obj X)
    (i : Fin (X.unop.obj.len + 1)) :
    ((simplexOfVertexSet v A hcard hK).app X σ).down.1 i =
      (A.orderEmbOfFin hcard) (σ.down.hom.toOrderHom i) := rfl

private theorem simplexOfVertexSet_nonhorn_facet_subset {n m r : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) (A : Finset (DV n m))
    (hcard : A.card = r + 2) (hK : (dcylDComplex v).S A)
    (X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ) (k : Fin (r + 2))
    (σ : (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk (r + 1))).obj X)
    (hσ : σ ∉ (horn.{u} (r + 1) k).obj X) :
    eraseDV A (A.orderEmbOfFin hcard k) ⊆
      dcylVertices ((simplexOfVertexSet v A hcard hK).app X σ) := by
  classical
  intro z hz
  rcases Finset.mem_erase.mp hz with ⟨hzk, hzA⟩
  let j : Fin (r + 2) := (A.orderIsoOfFin hcard).symm ⟨z, hzA⟩
  have hjeq : A.orderEmbOfFin hcard j = z := by
    rw [← Finset.coe_orderIsoOfFin_apply A hcard j]
    simp [j]
  have hjne : j ≠ k := by
    intro h
    exact hzk (hjeq.symm.trans (congrArg (A.orderEmbOfFin hcard) h))
  have hjRange : j ∈ Set.range (σ.down.hom.toOrderHom) := by
    by_contra hnot
    exact hσ ⟨j, hjne, hnot⟩
  rcases hjRange with ⟨i, hi⟩
  letI : DecidableEq (DV n m) := LinearOrder.toDecidableEq
  apply Finset.mem_image.mpr
  refine ⟨i, Finset.mem_univ _, ?_⟩
  rw [simplexOfVertexSet_app_apply]
  rw [hi]
  exact hjeq

private theorem simplexOfVertexSet_horn_facet_subset {n m r : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) (A : Finset (DV n m))
    (hcard : A.card = r + 2) (hK : (dcylDComplex v).S A)
    (X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ) (k : Fin (r + 2))
    (σ : (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk (r + 1))).obj X)
    (hσ : σ ∈ (horn.{u} (r + 1) k).obj X) :
    ∃ j : Fin (r + 2), j ≠ k ∧
      dcylVertices ((simplexOfVertexSet v A hcard hK).app X σ) ⊆
        eraseDV A (A.orderEmbOfFin hcard j) := by
  classical
  obtain ⟨j, hjk, hj⟩ := hσ
  refine ⟨j, hjk, ?_⟩
  intro z hz
  change z ∈ @Finset.image (Fin (X.unop.obj.len + 1)) (DV n m)
    LinearOrder.toDecidableEq ((simplexOfVertexSet v A hcard hK).app X σ).down.1
    Finset.univ at hz
  rcases (@Finset.mem_image (Fin (X.unop.obj.len + 1)) (DV n m)
    LinearOrder.toDecidableEq ((simplexOfVertexSet v A hcard hK).app X σ).down.1
    Finset.univ z).mp hz with ⟨i, -, hzi⟩
  apply Finset.mem_erase.mpr
  refine ⟨?_, ?_⟩
  · intro h
    apply hj
    exact ⟨i, (A.orderEmbOfFin hcard).injective (hzi.trans h)⟩
  · exact hzi ▸ Finset.orderEmbOfFin_mem A hcard (σ.down.hom.toOrderHom i)

private theorem simplexOfVertexSet_factor {n m r : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) (A : Finset (DV n m))
    (hcard : A.card = r + 2) (hK : (dcylDComplex v).S A)
    (X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ)
    (σ : dcylD.{u} v |>.obj X)
    (hverts : ∀ i, σ.down.1 i ∈ A) :
    ∃ τ : (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk (r + 1))).obj X,
      (simplexOfVertexSet v A hcard hK).app X τ = σ := by
  classical
  letI : DecidableEq (DV n m) := LinearOrder.toDecidableEq
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

private def middleFaces {n m : ℕ} (A : Finset (DV n m)) :
    Finset (Finset (Fin (n + 1))) :=
  Finset.univ.filter fun S => DV.mid S ∈ A

private noncomputable def tailFace {n m : ℕ} (A : Finset (DV n m)) :
    Finset (Fin (n + 1)) :=
  if h : (middleFaces A).Nonempty then
    Classical.choose (Finset.exists_min_image (middleFaces A) Finset.card h)
  else ∅

private theorem tailFace_mem_of_mid {n m : ℕ} {A : Finset (DV n m)}
    (hmid : DV.mid (Finset.univ : Finset (Fin (n + 1))) ∈ A) :
    DV.mid (tailFace A) ∈ A := by
  have hne : (middleFaces A).Nonempty := by
    exact ⟨Finset.univ, by simp [middleFaces, hmid]⟩
  have hspec := Classical.choose_spec
    (Finset.exists_min_image (middleFaces A) Finset.card hne)
  have hmem : tailFace A ∈ middleFaces A := by
    simp [tailFace, hne, hspec.1]
  simpa [middleFaces] using hmem

private theorem tailFace_subset_of_chain {n m : ℕ} {A : Finset (DV n m)}
    (hmid : DV.mid (Finset.univ : Finset (Fin (n + 1))) ∈ A)
    (hchain : ∀ S S', DV.mid S ∈ A → DV.mid S' ∈ A → S ⊆ S' ∨ S' ⊆ S)
    (S : Finset (Fin (n + 1))) (hS : DV.mid S ∈ A) : tailFace A ⊆ S := by
  have hne : (middleFaces A).Nonempty := by
    exact ⟨Finset.univ, by simp [middleFaces, hmid]⟩
  have hspec := Classical.choose_spec
    (Finset.exists_min_image (middleFaces A) Finset.card hne)
  have htail : tailFace A ∈ middleFaces A := by
    simp [tailFace, hne, hspec.1]
  have hS' : S ∈ middleFaces A := by simp [middleFaces, hS]
  have hnest := hchain (tailFace A) S (by simpa [middleFaces] using htail) hS
  rcases hnest with h | h
  · exact h
  · have hmin : (tailFace A).card ≤ S.card := by
      simpa [tailFace, hne] using hspec.2 S hS'
    exact (Finset.eq_of_subset_of_card_le h hmin).symm.subset

private noncomputable def headFace {n m : ℕ} (A : Finset (DV n m)) :
    Finset (Fin (n + 1)) :=
  if h : (middleFaces A).Nonempty then
    Classical.choose (Finset.exists_max_image (middleFaces A) Finset.card h)
  else ∅

private theorem headFace_mem_of_mid {n m : ℕ} {A : Finset (DV n m)}
    (hmid : DV.mid (Finset.univ : Finset (Fin (n + 1))) ∈ A) :
    DV.mid (headFace A) ∈ A := by
  have hne : (middleFaces A).Nonempty := by
    exact ⟨Finset.univ, by simp [middleFaces, hmid]⟩
  have hspec := Classical.choose_spec
    (Finset.exists_max_image (middleFaces A) Finset.card hne)
  have hmem : headFace A ∈ middleFaces A := by
    simp [headFace, hne, hspec.1]
  simpa [middleFaces] using hmem

private theorem headFace_superset_of_chain {n m : ℕ} {A : Finset (DV n m)}
    (hne : (middleFaces A).Nonempty)
    (hchain : ∀ S S', DV.mid S ∈ A → DV.mid S' ∈ A → S ⊆ S' ∨ S' ⊆ S)
    (S : Finset (Fin (n + 1))) (hS : DV.mid S ∈ A) : S ⊆ headFace A := by
  have hspec := Classical.choose_spec
    (Finset.exists_max_image (middleFaces A) Finset.card hne)
  have hhead : headFace A ∈ middleFaces A := by
    simp [headFace, hne, hspec.1]
  have hS' : S ∈ middleFaces A := by simp [middleFaces, hS]
  have hnest := hchain S (headFace A) hS (by simpa [middleFaces] using hhead)
  rcases hnest with h | h
  · exact h
  · have hmax : S.card ≤ (headFace A).card := by
      simpa [headFace, hne] using hspec.2 S hS'
    exact (Finset.eq_of_subset_of_card_le h hmax).symm.subset

private theorem erase_midFull_is_boundary {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) (A : Finset (DV n m))
    (hK : (dcylDComplex v).S A)
    (hfull : DV.mid (Finset.univ : Finset (Fin (n + 1))) ∈ A)
    (hTopNotFull : ¬ ∀ i, DV.top i ∈ A) :
    (dcylDBoundaryComplex v).S (A.erase (DV.mid Finset.univ)) := by
  classical
  let F := A.erase (DV.mid (Finset.univ : Finset (Fin (n + 1))))
  have hF : (dcylDComplex v).S F :=
    (dcylDComplex v).down (Finset.erase_subset _ _) hK
  have hfullF : DV.mid (Finset.univ : Finset (Fin (n + 1))) ∉ F := by
    simp [F]
  have hside :
      (∀ z ∈ F, ∃ c, z = DV.bot c) ∨
        ∃ i, DV.top i ∉ F ∧ ∀ S, DV.mid S ∈ F → i ∉ S := by
    by_cases hmidF : ∃ S, DV.mid S ∈ F
    · have hne : (middleFaces F).Nonempty := by
        rcases hmidF with ⟨S, hS⟩
        exact ⟨S, by simp [middleFaces, hS]⟩
      have hspec := Classical.choose_spec
        (Finset.exists_max_image (middleFaces F) Finset.card hne)
      have hhead : DV.mid (headFace F) ∈ F := by
        have hm : headFace F ∈ middleFaces F := by
          simp [headFace, hne, hspec.1]
        simpa [middleFaces] using hm
      have hheadNe : headFace F ≠ (Finset.univ : Finset (Fin (n + 1))) := by
        intro heq
        exact hfullF (heq ▸ hhead)
      have hex : ∃ i, i ∉ headFace F := by
        by_contra h
        have hall : (Finset.univ : Finset (Fin (n + 1))) ⊆ headFace F := by
          intro i hi
          by_contra hnot
          exact h ⟨i, hnot⟩
        exact hheadNe (Finset.univ_subset_iff.mp hall)
      obtain ⟨i, hi⟩ := hex
      have htop : DV.top i ∉ F := by
        intro hti
        have hiA : DV.top i ∈ A := (Finset.erase_subset _ _) hti
        have hheadA : DV.mid (headFace F) ∈ A := (Finset.erase_subset _ _) hhead
        exact hi (hK.2.2.2.1 i (headFace F) hiA hheadA)
      refine Or.inr ⟨i, htop, ?_⟩
      intro S hS
      have hsubset := headFace_superset_of_chain hne
        (fun S₁ S₂ h₁ h₂ => hK.2.1 S₁ S₂
          ((Finset.erase_subset _ _) h₁) ((Finset.erase_subset _ _) h₂)) S hS
      exact fun hmem => hi (hsubset hmem)
    · obtain ⟨i, hi⟩ := Classical.not_forall.mp hTopNotFull
      refine Or.inr ⟨i, ?_, ?_⟩
      · intro h
        exact hi ((Finset.erase_subset _ _) h)
      · intro S hS
        exact False.elim (hmidF ⟨S, hS⟩)
  exact ⟨hF, hside⟩

private def topSet {n m : ℕ} (A : Finset (DV n m)) : Finset (Fin (n + 1)) :=
  Finset.univ.filter fun i => DV.top i ∈ A

private def botSet {n m : ℕ} (A : Finset (DV n m)) : Finset (Fin (m + 1)) :=
  Finset.univ.filter fun c => DV.bot c ∈ A

private def middleCount {n m : ℕ} (A : Finset (DV n m)) : ℕ := (middleFaces A).card

private def topCount {n m : ℕ} (A : Finset (DV n m)) : ℕ := (topSet A).card

private def botCount {n m : ℕ} (A : Finset (DV n m)) : ℕ := (botSet A).card

private noncomputable def botPivot {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1))
    (A : Finset (DV n m)) : Fin (m + 1) :=
  if h : (tailFace A).Nonempty then v ((tailFace A).min' h) else v 0

private def mapHigh {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1))
    (A : Finset (DV n m)) : Prop :=
  (dcylDComplex v).S A ∧
    DV.mid (Finset.univ : Finset (Fin (n + 1))) ∈ A ∧
    (∀ i, DV.top i ∉ A) ∧ DV.bot (botPivot v A) ∈ A

private def prismHigh {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1))
    (A : Finset (DV n m)) : Prop :=
  (dcylDComplex v).S A ∧
    DV.mid (Finset.univ : Finset (Fin (n + 1))) ∈ A ∧
    (topSet A).Nonempty ∧ DV.mid (topSet A) ∈ A

private theorem dcylD_addBotPivot {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1))
    (A : Finset (DV n m)) (hK : (dcylDComplex v).S A)
    (hfull : DV.mid (Finset.univ : Finset (Fin (n + 1))) ∈ A)
    (hNoTop : ∀ i, DV.top i ∉ A) :
    (dcylDComplex v).S (insert (DV.bot (botPivot v A)) A) := by
  have htail : DV.mid (tailFace A) ∈ A := tailFace_mem_of_mid hfull
  have htailNonempty : (tailFace A).Nonempty := hK.1 (tailFace A) htail
  have hpivot : ∃ k ∈ tailFace A, v k = botPivot v A := by
    refine ⟨(tailFace A).min' htailNonempty, Finset.min'_mem _ _, ?_⟩
    simp [botPivot, htailNonempty]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro S hS
    have hSA : DV.mid S ∈ A := by
      rcases Finset.mem_insert.mp hS with h | h
      · cases h
      · exact h
    exact hK.1 S hSA
  · intro S S' hS hS'
    have hSA : DV.mid S ∈ A := by
      rcases Finset.mem_insert.mp hS with h | h
      · cases h
      · exact h
    have hS'A : DV.mid S' ∈ A := by
      rcases Finset.mem_insert.mp hS' with h | h
      · cases h
      · exact h
    exact hK.2.1 S S' hSA hS'A
  · intro i c hi hc
    have hiA : DV.top i ∈ A := by
      rcases Finset.mem_insert.mp hi with h | h
      · cases h
      · exact h
    exact False.elim (hNoTop i hiA)
  · intro i S hi hS
    have hiA : DV.top i ∈ A := by
      rcases Finset.mem_insert.mp hi with h | h
      · cases h
      · exact h
    exact False.elim (hNoTop i hiA)
  · intro c S hc hS
    have hSA : DV.mid S ∈ A := by
      rcases Finset.mem_insert.mp hS with h | h
      · cases h
      · exact h
    rcases Finset.mem_insert.mp hc with hc | hc
    · have hcp : c = botPivot v A := by injection hc
      subst c
      obtain ⟨k, hk, hkv⟩ := hpivot
      have htailS := tailFace_subset_of_chain hfull hK.2.1 S hSA
      exact ⟨k, htailS hk, hkv⟩
    · exact hK.2.2.2.2 c S hc hSA

private theorem dcylD_addTopPivot {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1))
    (A : Finset (DV n m)) (hK : (dcylDComplex v).S A)
    (hT : (topSet A).Nonempty) :
    (dcylDComplex v).S (insert (DV.mid (topSet A)) A) := by
  classical
  obtain ⟨i, hiT⟩ := hT
  have htop : DV.top i ∈ A := (Finset.mem_filter.mp hiT).2
  have hNoBot : ∀ c, DV.bot c ∉ A := by
    intro c hc
    exact hK.2.2.1 i c htop hc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro S hS
    rcases Finset.mem_insert.mp hS with h | h
    · injection h with hST
      rw [hST]
      exact ⟨i, hiT⟩
    · exact hK.1 S h
  · intro S S' hS hS'
    rcases Finset.mem_insert.mp hS with h | h
    · injection h with hST
      subst S
      rcases Finset.mem_insert.mp hS' with h' | h'
      · injection h' with hEq
        subst S'
        exact Or.inl (Finset.Subset.rfl)
      · have hTS : topSet A ⊆ S' := by
          intro j hj
          have htop' : DV.top j ∈ A := (Finset.mem_filter.mp hj).2
          exact hK.2.2.2.1 j S' htop' h'
        exact Or.inl hTS
    · rcases Finset.mem_insert.mp hS' with h' | h'
      · injection h' with hT'
        subst S'
        have hTS : topSet A ⊆ S := by
          intro j hj
          have htop' : DV.top j ∈ A := (Finset.mem_filter.mp hj).2
          exact hK.2.2.2.1 j S htop' h
        exact Or.inr hTS
      · exact hK.2.1 S S' h h'
  · intro j c hj hc
    have hcA : DV.bot c ∈ A := by
      rcases Finset.mem_insert.mp hc with h | h
      · cases h
      · exact h
    exact hNoBot c hcA
  · intro j S hj hS
    have hjA : DV.top j ∈ A := by
      rcases Finset.mem_insert.mp hj with h | h
      · cases h
      · exact h
    rcases Finset.mem_insert.mp hS with h | h
    · injection h with hST
      subst S
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjA⟩
    · exact hK.2.2.2.1 j S hjA h
  · intro c S hc hS
    have hcA : DV.bot c ∈ A := by
      rcases Finset.mem_insert.mp hc with h | h
      · cases h
      · exact h
    exact False.elim (hNoBot c hcA)

private abbrev MapCell {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1)) :=
  {A : Finset (DV n m) // mapHigh v A}

private abbrev PrismCell {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1)) :=
  {A : Finset (DV n m) // prismHigh v A}

private theorem mapCell_card_ge_two {n m : ℕ} {v : Fin (n + 1) → Fin (m + 1)}
    (a : MapCell v) : 2 ≤ a.val.card := by
  have hlt : 1 < a.val.card := Finset.one_lt_card.mpr
    ⟨DV.mid Finset.univ, a.property.2.1,
      DV.bot (botPivot v a.val), a.property.2.2.2, by simp⟩
  omega

private theorem prismCell_card_ge_two {n m : ℕ} {v : Fin (n + 1) → Fin (m + 1)}
    (a : PrismCell v) : 2 ≤ a.val.card := by
  rcases a.property.2.2.1 with ⟨i, hi⟩
  have hlt : 1 < a.val.card := Finset.one_lt_card.mpr
    ⟨DV.mid Finset.univ, a.property.2.1, DV.top i, (Finset.mem_filter.mp hi).2, by simp⟩
  omega

private noncomputable instance mapCellFintype {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) : Fintype (MapCell v) := by
  classical
  exact Fintype.ofFinite _

private noncomputable instance prismCellFintype {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) : Fintype (PrismCell v) := by
  classical
  exact Fintype.ofFinite _

private noncomputable def mapCellSimplex {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1))
    (a : MapCell v) :
    HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk (a.val.card - 2 + 1)) ⟶ dcylD.{u} v := by
  have hge := mapCell_card_ge_two a
  exact simplexOfVertexSet v a.val (by omega) a.property.1

private noncomputable def prismCellSimplex {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1))
    (a : PrismCell v) :
    HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk (a.val.card - 2 + 1)) ⟶ dcylD.{u} v := by
  have hge := prismCell_card_ge_two a
  exact simplexOfVertexSet v a.val (by omega) a.property.1

private def mapCellRank {n m : ℕ} {v : Fin (n + 1) → Fin (m + 1)}
    (a : MapCell v) : ℕ ×ₗ ℕ := toLex (middleCount a.val, botCount a.val)

private def prismCellRank {n m : ℕ} {v : Fin (n + 1) → Fin (m + 1)}
    (a : PrismCell v) : ℕ ×ₗ ℕ := toLex (topCount a.val, middleCount a.val)

private noncomputable def mapCellOrderRank {n m : ℕ} {v : Fin (n + 1) → Fin (m + 1)}
    (a : MapCell v) : (ℕ ×ₗ ℕ) ×ₗ Fin (Fintype.card (MapCell v)) :=
  toLex (mapCellRank a, Fintype.equivFin (MapCell v) a)

private theorem mapCellOrderRank_injective {n m : ℕ} {v : Fin (n + 1) → Fin (m + 1)} :
    Function.Injective (mapCellOrderRank (v := v)) := by
  intro a b h
  change toLex (mapCellRank a, Fintype.equivFin (MapCell v) a) =
    toLex (mapCellRank b, Fintype.equivFin (MapCell v) b) at h
  have hp := toLex_inj.mp h
  exact (Fintype.equivFin (MapCell v)).injective (Prod.mk.inj hp).2

private theorem mapCellOrderRank_lt_of_rank_lt {n m : ℕ}
    {v : Fin (n + 1) → Fin (m + 1)} {a b : MapCell v}
    (h : mapCellRank a < mapCellRank b) : mapCellOrderRank a < mapCellOrderRank b := by
  change toLex (mapCellRank a, Fintype.equivFin (MapCell v) a) <
    toLex (mapCellRank b, Fintype.equivFin (MapCell v) b)
  rw [Prod.Lex.toLex_lt_toLex]
  exact Or.inl h

private noncomputable def prismCellOrderRank {n m : ℕ} {v : Fin (n + 1) → Fin (m + 1)}
    (a : PrismCell v) : (ℕ ×ₗ ℕ) ×ₗ Fin (Fintype.card (PrismCell v)) :=
  toLex (prismCellRank a, Fintype.equivFin (PrismCell v) a)

private theorem prismCellOrderRank_injective {n m : ℕ} {v : Fin (n + 1) → Fin (m + 1)} :
    Function.Injective (prismCellOrderRank (v := v)) := by
  intro a b h
  change toLex (prismCellRank a, Fintype.equivFin (PrismCell v) a) =
    toLex (prismCellRank b, Fintype.equivFin (PrismCell v) b) at h
  have hp := toLex_inj.mp h
  exact (Fintype.equivFin (PrismCell v)).injective (Prod.mk.inj hp).2

private theorem prismCellOrderRank_lt_of_rank_lt {n m : ℕ}
    {v : Fin (n + 1) → Fin (m + 1)} {a b : PrismCell v}
    (h : prismCellRank a < prismCellRank b) :
    prismCellOrderRank a < prismCellOrderRank b := by
  change toLex (prismCellRank a, Fintype.equivFin (PrismCell v) a) <
    toLex (prismCellRank b, Fintype.equivFin (PrismCell v) b)
  rw [Prod.Lex.toLex_lt_toLex]
  exact Or.inl h

private theorem prismCell_topFacet_partner {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) (a : PrismCell v) {i : Fin (n + 1)}
    (hi : DV.top i ∈ a.val)
    (hT : (topSet (a.val.erase (DV.top i))).Nonempty) :
    ∃ b : PrismCell v, a.val.erase (DV.top i) ⊆ b.val ∧ prismCellRank b < prismCellRank a := by
  classical
  let A := a.val
  let F := A.erase (DV.top i)
  have hKF : (dcylDComplex v).S F := (dcylDComplex v).down (Finset.erase_subset _ _) a.property.1
  have hfullF : DV.mid Finset.univ ∈ F := by
    exact Finset.mem_erase.mpr ⟨by simp, a.property.2.1⟩
  have hK := dcylD_addTopPivot v F hKF hT
  let B := insert (DV.mid (topSet F)) F
  have hfullB : DV.mid Finset.univ ∈ B := Finset.mem_insert_of_mem hfullF
  have htopSetB : topSet B = topSet F := by
    ext j
    simp [topSet, B]
  have hTmem : DV.mid (topSet F) ∈ B := Finset.mem_insert_self _ _
  let b : PrismCell v := ⟨B, ⟨hK, hfullB, by simpa [htopSetB] using hT,
    by simpa [htopSetB] using hTmem⟩⟩
  refine ⟨b, ?_, ?_⟩
  · exact Finset.subset_insert _ _
  · have htopSets : topSet F = (topSet A).erase i := by
      ext j
      simp [topSet, F, A, Finset.mem_erase, hi]
    have himem : i ∈ topSet A := by simp [topSet, A, hi]
    have hcount : topCount B + 1 = topCount A := by
      change (topSet B).card + 1 = (topSet A).card
      rw [htopSetB, htopSets, Finset.card_erase_of_mem himem]
      have hpos : 0 < (topSet A).card := Finset.card_pos.mpr ⟨i, himem⟩
      omega
    change toLex (topCount B, middleCount B) < toLex (topCount A, middleCount A)
    rw [Prod.Lex.toLex_lt_toLex]
    exact Or.inl (by omega)

private noncomputable def mapCellPivotIndex {n m : ℕ} {v : Fin (n + 1) → Fin (m + 1)}
    (a : MapCell v) : Fin (a.val.card - 2 + 2) := by
  have hcard : a.val.card = (a.val.card - 2) + 2 := by
    have h := mapCell_card_ge_two a
    omega
  exact (a.val.orderIsoOfFin hcard).symm ⟨DV.bot (botPivot v a.val), a.property.2.2.2⟩

private noncomputable def prismCellPivotIndex {n m : ℕ} {v : Fin (n + 1) → Fin (m + 1)}
    (a : PrismCell v) : Fin (a.val.card - 2 + 2) := by
  have hcard : a.val.card = (a.val.card - 2) + 2 := by
    have h := prismCell_card_ge_two a
    omega
  exact (a.val.orderIsoOfFin hcard).symm ⟨DV.mid (topSet a.val), a.property.2.2.2⟩

private theorem mapCellPivotIndex_apply {n m : ℕ} {v : Fin (n + 1) → Fin (m + 1)}
    (a : MapCell v) (hcard : a.val.card = (a.val.card - 2) + 2) :
    (a.val.orderEmbOfFin hcard) (mapCellPivotIndex (v := v) a) =
      DV.bot (botPivot v a.val) := by
  rw [← Finset.coe_orderIsoOfFin_apply a.val hcard (mapCellPivotIndex (v := v) a)]
  simp [mapCellPivotIndex]

private theorem prismCellPivotIndex_apply {n m : ℕ} {v : Fin (n + 1) → Fin (m + 1)}
    (a : PrismCell v) (hcard : a.val.card = (a.val.card - 2) + 2) :
    (a.val.orderEmbOfFin hcard) (prismCellPivotIndex (v := v) a) =
      DV.mid (topSet a.val) := by
  rw [← Finset.coe_orderIsoOfFin_apply a.val hcard (prismCellPivotIndex (v := v) a)]
  simp [prismCellPivotIndex]

private theorem mapCell_missingFacet_coface_rank {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) (a b : MapCell v)
    (hba : a ≠ b)
    (hsub : a.val.erase (DV.bot (botPivot v a.val)) ⊆ b.val) :
    mapCellRank a < mapCellRank b := by
  classical
  let A := a.val
  let B := b.val
  have hmidSub : middleFaces A ⊆ middleFaces B := by
    intro S hS
    have hmidA : DV.mid S ∈ A := by simpa [middleFaces] using hS
    have hmidB : DV.mid S ∈ B := by
      apply hsub
      exact Finset.mem_erase.mpr ⟨by simp, hmidA⟩
    simpa [middleFaces] using hmidB
  have hmidLe : middleCount A ≤ middleCount B := Finset.card_le_card hmidSub
  by_cases hlt : middleCount A < middleCount B
  · change toLex (middleCount A, botCount A) < toLex (middleCount B, botCount B)
    rw [Prod.Lex.toLex_lt_toLex]
    exact Or.inl hlt
  · have hmidEq : middleCount A = middleCount B := by omega
    have hfacesEq : middleFaces A = middleFaces B :=
      Finset.eq_of_subset_of_card_le hmidSub (by simpa [middleCount] using hmidEq.ge)
    have htail : tailFace A = tailFace B := by simp [tailFace, hfacesEq]
    have hpivot : botPivot v A = botPivot v B := by simp [botPivot, htail]
    have hPivotB : DV.bot (botPivot v A) ∈ B := by
      rw [hpivot]
      exact b.property.2.2.2
    have hAB : A ⊆ B := by
      intro z hz
      by_cases hp : z = DV.bot (botPivot v A)
      · simpa [hp] using hPivotB
      · exact hsub (Finset.mem_erase.mpr ⟨hp, hz⟩)
    have hABne : A ≠ B := by
      intro h
      apply hba
      exact Subtype.ext h
    have hBotSub : botSet A ⊆ botSet B := by
      intro c hc
      have hcA : DV.bot c ∈ A := by simpa [botSet] using hc
      have hcB := hAB hcA
      simpa [botSet] using hcB
    have hBotNe : botSet A ≠ botSet B := by
      intro heq
      apply hABne
      ext z
      cases z with
      | top i =>
          constructor
          · intro h
            exact False.elim (a.property.2.2.1 i h)
          · intro h
            exact False.elim (b.property.2.2.1 i h)
      | mid S =>
          have hh := congrArg (fun T : Finset (Finset (Fin (n + 1))) => S ∈ T) hfacesEq
          simpa [middleFaces] using hh
      | bot c =>
          have hh := congrArg (fun T : Finset (Fin (m + 1)) => c ∈ T) heq
          simpa [botSet] using hh
    have hBotStrict : botSet A ⊂ botSet B := Finset.ssubset_iff_subset_ne.mpr ⟨hBotSub, hBotNe⟩
    have hBotCard : botCount A < botCount B := Finset.card_lt_card hBotStrict
    change toLex (middleCount A, botCount A) < toLex (middleCount B, botCount B)
    rw [Prod.Lex.toLex_lt_toLex]
    exact Or.inr ⟨hmidEq, hBotCard⟩

private theorem prismCell_missingFacet_coface_rank {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) (a b : PrismCell v)
    (hba : a ≠ b)
    (hsub : a.val.erase (DV.mid (topSet a.val)) ⊆ b.val) :
    prismCellRank a < prismCellRank b := by
  classical
  let A := a.val
  let B := b.val
  have htopSub : topSet A ⊆ topSet B := by
    intro i hi
    have htopA : DV.top i ∈ A := (Finset.mem_filter.mp hi).2
    have htopErase : DV.top i ∈ A.erase (DV.mid (topSet A)) := by
      exact Finset.mem_erase.mpr ⟨by simp, htopA⟩
    have htopB : DV.top i ∈ B := hsub htopErase
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, htopB⟩
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
      have hmidA : DV.mid S ∈ A := by simpa [middleFaces] using hS
      by_cases hST : S = topSet A
      · subst S
        have hmidB : DV.mid (topSet B) ∈ B := b.property.2.2.2
        have hmidB' : topSet B ∈ middleFaces B :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmidB⟩
        rw [htopSetEq]
        exact hmidB'
      · have hmidErase : DV.mid S ∈ A.erase (DV.mid (topSet A)) := by
          apply Finset.mem_erase.mpr
          refine ⟨?_, hmidA⟩
          intro heq
          injection heq with hEq
          exact hST hEq
        have hmidB : DV.mid S ∈ B := hsub hmidErase
        simpa [middleFaces] using hmidB
    have hmidLe : middleCount A ≤ middleCount B := Finset.card_le_card hmidSub
    by_cases hmidLt : middleCount A < middleCount B
    · change toLex (topCount A, middleCount A) < toLex (topCount B, middleCount B)
      rw [Prod.Lex.toLex_lt_toLex]
      exact Or.inr ⟨htopEq, hmidLt⟩
    · have hmidEq : middleCount A = middleCount B := by omega
      have hmidSetEq : middleFaces A = middleFaces B :=
        Finset.eq_of_subset_of_card_le hmidSub (by simpa [middleCount] using hmidEq.ge)
      have hNoBotA : ∀ c, DV.bot c ∉ A := by
        rcases a.property.2.2.1 with ⟨i, hi⟩
        have htopA : DV.top i ∈ A := (Finset.mem_filter.mp hi).2
        intro c hc
        exact a.property.1.2.2.1 i c htopA hc
      have hNoBotB : ∀ c, DV.bot c ∉ B := by
        rcases b.property.2.2.1 with ⟨i, hi⟩
        have htopB : DV.top i ∈ B := (Finset.mem_filter.mp hi).2
        intro c hc
        exact b.property.1.2.2.1 i c htopB hc
      have hAB : A = B := by
        ext z
        cases z with
        | top i =>
            have hA : DV.top i ∈ A ↔ i ∈ topSet A := by simp [topSet]
            have hB : DV.top i ∈ B ↔ i ∈ topSet B := by simp [topSet]
            rw [hA, hB, htopSetEq]
        | mid S =>
            have hA : DV.mid S ∈ A ↔ S ∈ middleFaces A := by simp [middleFaces]
            have hB : DV.mid S ∈ B ↔ S ∈ middleFaces B := by simp [middleFaces]
            rw [hA, hB, hmidSetEq]
        | bot c => simp [hNoBotA c, hNoBotB c]
      exact False.elim (hba (Subtype.ext hAB))

private theorem mapCell_botFacet_partner {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1))
    (a : MapCell v) {c : Fin (m + 1)} (hc : DV.bot c ∈ a.val)
    (hcne : c ≠ botPivot v a.val) :
    ∃ b : MapCell v, a.val.erase (DV.bot c) ⊆ b.val ∧ mapCellRank b < mapCellRank a := by
  classical
  let A := a.val
  let B := A.erase (DV.bot c)
  have hK : (dcylDComplex v).S B := (dcylDComplex v).down (Finset.erase_subset _ _) a.property.1
  have hmid : DV.mid Finset.univ ∈ B := by
    exact Finset.mem_erase.mpr ⟨by simp, a.property.2.1⟩
  have hNoTop : ∀ i, DV.top i ∉ B := by
    intro i hi
    exact a.property.2.2.1 i ((Finset.erase_subset _ _) hi)
  have htail : tailFace B = tailFace A := by
    simp [tailFace, middleFaces, B, A]
  have hpivot : botPivot v B = botPivot v A := by simp [botPivot, htail]
  have hpivNe : botPivot v A ≠ c := by
    intro h
    exact hcne h.symm
  have hbot : DV.bot (botPivot v B) ∈ B := by
    rw [hpivot]
    exact Finset.mem_erase.mpr ⟨by simpa using hpivNe, a.property.2.2.2⟩
  let b : MapCell v := ⟨B, ⟨hK, hmid, hNoTop, hbot⟩⟩
  refine ⟨b, by dsimp [b, B, A]; exact Finset.Subset.rfl, ?_⟩
  have hmidSet : middleFaces B = middleFaces A := by
    ext S
    simp [middleFaces, B, A]
  have hbotSet : botSet B = (botSet A).erase c := by
    ext c'
    simp [botSet, B, A, Finset.mem_erase]
  have hcmem : c ∈ botSet A := by simp [botSet, A, hc]
  have hmidCount : middleCount B = middleCount A := by
    simp [middleCount, hmidSet]
  have hbotCount : botCount B = botCount A - 1 := by
    change (botSet B).card = (botSet A).card - 1
    rw [hbotSet, Finset.card_erase_of_mem hcmem]
  have hpos : 0 < botCount A := Finset.card_pos.mpr ⟨c, hcmem⟩
  change toLex (middleCount B, botCount B) < toLex (middleCount A, botCount A)
  rw [Prod.Lex.toLex_lt_toLex]
  exact Or.inr ⟨hmidCount, by omega⟩

private theorem mapCell_midFacet_partner {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1))
    (a : MapCell v) {S : Finset (Fin (n + 1))} (hS : DV.mid S ∈ a.val)
    (hSne : S ≠ Finset.univ) :
    ∃ b : MapCell v, a.val.erase (DV.mid S) ⊆ b.val ∧ mapCellRank b < mapCellRank a := by
  classical
  let A := a.val
  let F := A.erase (DV.mid S)
  have hK : (dcylDComplex v).S F := (dcylDComplex v).down (Finset.erase_subset _ _) a.property.1
  have hfullA : DV.mid Finset.univ ∈ A := a.property.2.1
  have hfullF : DV.mid Finset.univ ∈ F := by
    apply Finset.mem_erase.mpr
    refine ⟨?_, hfullA⟩
    intro h
    injection h with hs
    exact hSne hs.symm
  have hNoTopF : ∀ i, DV.top i ∉ F := by
    intro i hi
    exact a.property.2.2.1 i ((Finset.erase_subset _ _) hi)
  let B := insert (DV.bot (botPivot v F)) F
  have hKB := dcylD_addBotPivot v F hK hfullF hNoTopF
  have hNoTopB : ∀ i, DV.top i ∉ B := by
    intro i hi
    rcases Finset.mem_insert.mp hi with hi | hi
    · cases hi
    · exact hNoTopF i hi
  have hmidSets : middleFaces F = (middleFaces A).erase S := by
    ext T
    simp [middleFaces, F, A, Finset.mem_erase]
  have hmidSetsB : middleFaces B = middleFaces F := by
    ext T
    simp [middleFaces, B, Finset.mem_insert]
  have htail : tailFace B = tailFace F := by simp [tailFace, hmidSetsB]
  have hpivot : botPivot v B = botPivot v F := by simp [botPivot, htail]
  have hmidB : DV.mid Finset.univ ∈ B := Finset.mem_insert_of_mem hfullF
  have hbotB : DV.bot (botPivot v B) ∈ B := by
    rw [hpivot]
    exact Finset.mem_insert_self _ _
  let b : MapCell v := ⟨B, ⟨hKB, hmidB, hNoTopB, hbotB⟩⟩
  refine ⟨b, ?_, ?_⟩
  · exact Finset.subset_insert _ _
  · have hSmem : S ∈ middleFaces A := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS⟩
    have hcardErase : ((middleFaces A).erase S).card + 1 = (middleFaces A).card := by
      rw [Finset.card_erase_of_mem hSmem]
      have hcardpos : 0 < (middleFaces A).card := Finset.card_pos.mpr ⟨S, hSmem⟩
      omega
    have hcount : middleCount B + 1 = middleCount A := by
      change (middleFaces B).card + 1 = (middleFaces A).card
      rw [hmidSetsB, hmidSets]
      exact hcardErase
    change toLex (middleCount B, botCount B) < toLex (middleCount A, botCount A)
    rw [Prod.Lex.toLex_lt_toLex]
    exact Or.inl (by omega)

private theorem prismCell_midFacet_partner {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) (a : PrismCell v)
    {S : Finset (Fin (n + 1))} (hS : DV.mid S ∈ a.val)
    (hSneFull : S ≠ Finset.univ) (hSnePivot : S ≠ topSet a.val) :
    ∃ b : PrismCell v, a.val.erase (DV.mid S) ⊆ b.val ∧ prismCellRank b < prismCellRank a := by
  classical
  let A := a.val
  let F := A.erase (DV.mid S)
  have hKF : (dcylDComplex v).S F := (dcylDComplex v).down (Finset.erase_subset _ _) a.property.1
  have hfullF : DV.mid Finset.univ ∈ F := by
    apply Finset.mem_erase.mpr
    refine ⟨?_, a.property.2.1⟩
    intro h
    injection h with hEq
    exact hSneFull hEq.symm
  have htopSetF : topSet F = topSet A := by
    ext i
    simp [topSet, F, A, Finset.mem_erase]
  have hmidPivotF : DV.mid (topSet A) ∈ F := by
    apply Finset.mem_erase.mpr
    refine ⟨?_, a.property.2.2.2⟩
    intro h
    injection h with hEq
    exact hSnePivot hEq.symm
  let b : PrismCell v := ⟨F, ⟨hKF, hfullF, by simpa [htopSetF] using a.property.2.2.1,
    by simpa [htopSetF] using hmidPivotF⟩⟩
  refine ⟨b, Finset.Subset.rfl, ?_⟩
  have hmidSets : middleFaces F = (middleFaces A).erase S := by
    ext T
    simp [middleFaces, F, A, Finset.mem_erase]
  have hSmem : S ∈ middleFaces A := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS⟩
  have hcardErase : ((middleFaces A).erase S).card + 1 = (middleFaces A).card := by
    rw [Finset.card_erase_of_mem hSmem]
    have hcardpos : 0 < (middleFaces A).card := Finset.card_pos.mpr ⟨S, hSmem⟩
    omega
  have hcount : middleCount F + 1 = middleCount A := by
    change (middleFaces F).card + 1 = (middleFaces A).card
    rw [hmidSets]
    exact hcardErase
  change toLex (topCount F, middleCount F) < toLex (topCount A, middleCount A)
  rw [Prod.Lex.toLex_lt_toLex]
  exact Or.inr ⟨by simp [topCount, htopSetF], by omega⟩

private def boundaryStage {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1)) :
    Subfunctor (dcylD.{u} v) := Subfunctor.range (dcylDBoundaryι.{u} v)

private theorem boundaryStage_of_vertices {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1))
    (X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ)
    (x : (dcylD.{u} v).obj X)
    (hB : (dcylDBoundaryComplex v).S (dcylVertices x)) :
    x ∈ (boundaryStage v).obj X := by
  letI : DecidableEq (DV n m) := LinearOrder.toDecidableEq
  have hImage : dcylVertices x = Finset.univ.image x.down.1 := dcylVertices_eq_image x
  let y : (dcylDBoundaryComplex v).Simplex X.unop.obj.len :=
    ⟨x.down.1, x.down.2.1, by
      exact hB⟩
  refine ⟨ULift.up y, ?_⟩
  apply ULift.ext
  apply Subtype.ext
  rfl

private theorem boundaryStage_vertices {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1))
    (X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ)
    (x : (dcylD.{u} v).obj X)
    (hx : x ∈ (boundaryStage v).obj X) :
    (dcylDBoundaryComplex v).S (dcylVertices x) := by
  letI : DecidableEq (DV n m) := LinearOrder.toDecidableEq
  rcases hx with ⟨y, hy⟩
  have hfun : y.down.1 = x.down.1 := by
    funext i
    have h := congrArg (fun z => z.1 i) (congrArg ULift.down hy)
    change y.down.1 i = x.down.1 i at h
    exact h
  have hImage : dcylVertices x = Finset.univ.image x.down.1 := dcylVertices_eq_image x
  have hB := y.down.2.2
  rw [hfun] at hB
  simpa [dcylVertices] using hB

private noncomputable def mapStage {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1))
    (H : Finset (MapCell v)) : Subfunctor (dcylD.{u} v) :=
  boundaryStage v ⊔ H.sup (fun a => Subfunctor.range (mapCellSimplex v a))

private noncomputable def prismStage {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1))
    (H : Finset (PrismCell v)) : Subfunctor (dcylD.{u} v) :=
  mapStage v Finset.univ ⊔ H.sup (fun a => Subfunctor.range (prismCellSimplex v a))

private theorem mapStage_insert {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1))
    (H : Finset (MapCell v)) (a : MapCell v) :
    mapStage v (insert a H) =
      mapStage v H ⊔ Subfunctor.range (mapCellSimplex v a) := by
  classical
  letI : DecidableEq (DV n m) := LinearOrder.toDecidableEq
  simp [mapStage, Finset.sup_insert, sup_assoc, sup_comm, sup_left_comm]

private theorem prismStage_insert {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1))
    (H : Finset (PrismCell v)) (a : PrismCell v) :
    prismStage v (insert a H) =
      prismStage v H ⊔ Subfunctor.range (prismCellSimplex v a) := by
  classical
  simp [prismStage, Finset.sup_insert, sup_assoc, sup_comm, sup_left_comm]

private theorem mapStage_mem_iff {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1))
    (H : Finset (MapCell v)) (X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ)
    (x : (dcylD.{u} v).obj X) :
    x ∈ (mapStage v H).obj X ↔
      x ∈ (boundaryStage v).obj X ∨
        ∃ a ∈ H, x ∈ (Subfunctor.range (mapCellSimplex v a)).obj X := by
  classical
  induction H using Finset.induction_on with
  | empty => simp [mapStage]
  | @insert a H ha ih =>
      rw [mapStage_insert, Subfunctor.max_obj, Set.mem_union]
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

private theorem prismStage_mem_iff {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1))
    (H : Finset (PrismCell v)) (X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ)
    (x : (dcylD.{u} v).obj X) :
    x ∈ (prismStage v H).obj X ↔
      x ∈ (mapStage v Finset.univ).obj X ∨
        ∃ a ∈ H, x ∈ (Subfunctor.range (prismCellSimplex v a)).obj X := by
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

private theorem mem_mapCellRange_of_vertices_subset {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) (a : MapCell v)
    (X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ)
    (x : (dcylD.{u} v).obj X)
    (hverts : dcylVertices x ⊆ a.val) :
    x ∈ (Subfunctor.range (mapCellSimplex v a)).obj X := by
  classical
  letI : DecidableEq (DV n m) := LinearOrder.toDecidableEq
  have hcard : a.val.card = (a.val.card - 2) + 2 := by
    have h := mapCell_card_ge_two a
    omega
  have hverts' : ∀ i, x.down.1 i ∈ a.val := by
    intro i
    have hi : x.down.1 i ∈ dcylVertices x := by
      change x.down.1 i ∈ @Finset.image (Fin (X.unop.obj.len + 1)) (DV n m)
        LinearOrder.toDecidableEq x.down.1 Finset.univ
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    exact hverts hi
  obtain ⟨τ, hτ⟩ := simplexOfVertexSet_factor v a.val hcard a.property.1 X x hverts'
  refine ⟨τ, ?_⟩
  simpa [mapCellSimplex] using hτ

private theorem mapCellRange_vertices_subset {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) (a : MapCell v)
    (X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ)
    (x : (dcylD.{u} v).obj X)
    (hx : x ∈ (Subfunctor.range (mapCellSimplex v a)).obj X) :
    dcylVertices x ⊆ a.val := by
  classical
  letI : DecidableEq (DV n m) := LinearOrder.toDecidableEq
  have hcard : a.val.card = (a.val.card - 2) + 2 := by
    have h := mapCell_card_ge_two a
    omega
  rcases hx with ⟨σ, hσ⟩
  rw [← hσ]
  simpa [mapCellSimplex] using
    (dcylVertices_simplexOfVertexSet_subset v a.val hcard a.property.1 X σ)

private theorem mem_prismCellRange_of_vertices_subset {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) (a : PrismCell v)
    (X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ)
    (x : (dcylD.{u} v).obj X)
    (hverts : dcylVertices x ⊆ a.val) :
    x ∈ (Subfunctor.range (prismCellSimplex v a)).obj X := by
  classical
  letI : DecidableEq (DV n m) := LinearOrder.toDecidableEq
  have hcard : a.val.card = (a.val.card - 2) + 2 := by
    have h := prismCell_card_ge_two a
    omega
  have hverts' : ∀ i, x.down.1 i ∈ a.val := by
    intro i
    have hi : x.down.1 i ∈ dcylVertices x := by
      change x.down.1 i ∈ @Finset.image (Fin (X.unop.obj.len + 1)) (DV n m)
        LinearOrder.toDecidableEq x.down.1 Finset.univ
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    exact hverts hi
  obtain ⟨τ, hτ⟩ := simplexOfVertexSet_factor v a.val hcard a.property.1 X x hverts'
  refine ⟨τ, ?_⟩
  simpa [prismCellSimplex] using hτ

private theorem prismCellRange_vertices_subset {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) (a : PrismCell v)
    (X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ)
    (x : (dcylD.{u} v).obj X)
    (hx : x ∈ (Subfunctor.range (prismCellSimplex v a)).obj X) :
    dcylVertices x ⊆ a.val := by
  classical
  letI : DecidableEq (DV n m) := LinearOrder.toDecidableEq
  have hcard : a.val.card = (a.val.card - 2) + 2 := by
    have h := prismCell_card_ge_two a
    omega
  rcases hx with ⟨σ, hσ⟩
  rw [← hσ]
  simpa [prismCellSimplex] using
    (dcylVertices_simplexOfVertexSet_subset v a.val hcard a.property.1 X σ)

private theorem mapStage_contains_fullMid {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1))
    (X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ)
    (x : (dcylD.{u} v).obj X)
    (hfull : DV.mid (Finset.univ : Finset (Fin (n + 1))) ∈ dcylVertices x)
    (hNoTop : ∀ i, DV.top i ∉ dcylVertices x) :
    x ∈ (mapStage v Finset.univ).obj X := by
  classical
  letI : DecidableEq (DV n m) := LinearOrder.toDecidableEq
  let A := dcylVertices x
  have hK : (dcylDComplex v).S A := x.down.2.2
  let B := insert (DV.bot (botPivot v A)) A
  have hKB : (dcylDComplex v).S B := by
    simpa [B] using dcylD_addBotPivot v A hK hfull hNoTop
  have hfullB : DV.mid Finset.univ ∈ B := Finset.mem_insert_of_mem hfull
  have hNoTopB : ∀ i, DV.top i ∉ B := by
    intro i hi
    rcases Finset.mem_insert.mp hi with hi | hi
    · cases hi
    · exact hNoTop i hi
  have hbotB : DV.bot (botPivot v B) ∈ B := by
    have hmiddleFaces : middleFaces B = middleFaces A := by
      ext S
      simp [middleFaces, B]
    have htail : tailFace B = tailFace A := by
      simp [tailFace, hmiddleFaces]
    have hpivot : botPivot v B = botPivot v A := by simp [botPivot, htail]
    rw [hpivot]
    exact Finset.mem_insert_self _ _
  let b : MapCell v := ⟨B, ⟨hKB, hfullB, hNoTopB, hbotB⟩⟩
  have hverts : dcylVertices x ⊆ b.val := by
    intro z hz
    exact Finset.mem_insert_of_mem hz
  have hrange := mem_mapCellRange_of_vertices_subset v b X x hverts
  apply (mapStage_mem_iff v Finset.univ X x).2
  exact Or.inr ⟨b, Finset.mem_univ _, hrange⟩

private theorem boundary_vertices_of_noTop_noFullMid {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1))
    (X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ)
    (x : (dcylD.{u} v).obj X)
    (hNoTop : ∀ i, DV.top i ∉ dcylVertices x)
    (hNoFull : DV.mid (Finset.univ : Finset (Fin (n + 1))) ∉ dcylVertices x) :
    (dcylDBoundaryComplex v).S (dcylVertices x) := by
  classical
  let A := dcylVertices x
  have hK : (dcylDComplex v).S A := x.down.2.2
  by_cases hmid : ∃ S, DV.mid S ∈ A
  · have hne : (middleFaces A).Nonempty := by
      rcases hmid with ⟨S, hS⟩
      exact ⟨S, by simp [middleFaces, hS]⟩
    have hhead : DV.mid (headFace A) ∈ A := by
      have hh : headFace A ∈ middleFaces A := by
        let hspec := Classical.choose_spec
          (Finset.exists_max_image (middleFaces A) Finset.card hne)
        simpa [headFace, hne, hspec.1]
      simpa [middleFaces] using hh
    have hheadNe : headFace A ≠ (Finset.univ : Finset (Fin (n + 1))) := by
      intro heq
      exact hNoFull (heq ▸ hhead)
    obtain ⟨i, hi⟩ : ∃ i, i ∉ headFace A := by
      by_contra h
      have hsub : (Finset.univ : Finset (Fin (n + 1))) ⊆ headFace A := by
        intro j hj
        by_contra hj'
        exact h ⟨j, hj'⟩
      exact hheadNe (Finset.univ_subset_iff.mp hsub)
    refine ⟨hK, Or.inr ⟨i, hNoTop i, ?_⟩⟩
    intro S hS hiS
    have hsubset := headFace_superset_of_chain hne
      (fun S₁ S₂ h₁ h₂ => hK.2.1 S₁ S₂ h₁ h₂) S hS
    exact hi (hsubset hiS)
  · refine ⟨hK, Or.inl ?_⟩
    intro z hz
    cases z with
    | top i => exact False.elim (hNoTop i hz)
    | mid S => exact False.elim (hmid ⟨S, hz⟩)
    | bot c => exact ⟨c, rfl⟩

private theorem mapStage_contains_noTop {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1))
    (X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ)
    (x : (dcylD.{u} v).obj X)
    (hNoTop : ∀ i, DV.top i ∉ dcylVertices x) :
    x ∈ (mapStage v Finset.univ).obj X := by
  by_cases hfull : DV.mid (Finset.univ : Finset (Fin (n + 1))) ∈ dcylVertices x
  · exact mapStage_contains_fullMid v X x hfull hNoTop
  · apply (mapStage_mem_iff v Finset.univ X x).2
    exact Or.inl (boundaryStage_of_vertices v X x
      (boundary_vertices_of_noTop_noFullMid v X x hNoTop hfull))

private theorem mapCell_otherFacet {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) (a : MapCell v)
    (z : DV n m) (hz : z ∈ a.val)
    (hzPivot : z ≠ DV.bot (botPivot v a.val)) :
    (dcylDBoundaryComplex v).S (a.val.erase z) ∨
      ∃ b : MapCell v, a.val.erase z ⊆ b.val ∧ mapCellRank b < mapCellRank a := by
  classical
  have hTopNotFull : ¬ ∀ i, DV.top i ∈ a.val := by
    intro hall
    exact a.property.2.2.1 0 (hall 0)
  cases z with
  | top i => exact False.elim (a.property.2.2.1 i hz)
  | mid S =>
      by_cases hfull : S = Finset.univ
      · subst S
        exact Or.inl (erase_midFull_is_boundary v a.val a.property.1 a.property.2.1
          hTopNotFull)
      · exact Or.inr (mapCell_midFacet_partner v a hz hfull)
  | bot c =>
      have hcne : c ≠ botPivot v a.val := by
        intro hc
        apply hzPivot
        exact congrArg DV.bot hc
      exact Or.inr (mapCell_botFacet_partner v a hz hcne)

private theorem prismCell_otherFacet {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) (a : PrismCell v)
    (z : DV n m) (hz : z ∈ a.val)
    (hzPivot : z ≠ DV.mid (topSet a.val)) :
    (dcylDBoundaryComplex v).S (a.val.erase z) ∨
      (∀ i, DV.top i ∉ a.val.erase z) ∨
      ∃ b : PrismCell v, a.val.erase z ⊆ b.val ∧ prismCellRank b < prismCellRank a := by
  classical
  cases z with
  | top i =>
      have htop : DV.top i ∈ a.val := hz
      by_cases hT : (topSet (a.val.erase (DV.top i))).Nonempty
      · exact Or.inr (Or.inr (prismCell_topFacet_partner v a htop hT))
      · apply Or.inr (Or.inl ?_)
        intro j hj
        apply hT
        exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  | mid S =>
      have hmid : DV.mid S ∈ a.val := hz
      by_cases hfull : S = Finset.univ
      · subst S
        have hTopNotFull : ¬ ∀ i, DV.top i ∈ a.val := by
          intro hall
          have hT : topSet a.val = Finset.univ := by
            ext i
            simp [topSet, hall]
          apply hzPivot
          exact congrArg DV.mid hT.symm
        exact Or.inl (erase_midFull_is_boundary v a.val a.property.1 a.property.2.1
          hTopNotFull)
      · have hSnePivot : S ≠ topSet a.val := by
          intro h
          apply hzPivot
          exact congrArg DV.mid h
        exact Or.inr (Or.inr (prismCell_midFacet_partner v a hmid hfull hSnePivot))
  | bot c =>
      rcases a.property.2.2.1 with ⟨i, hi⟩
      have htop : DV.top i ∈ a.val := (Finset.mem_filter.mp hi).2
      exact False.elim (a.property.1.2.2.1 i c htop hz)

private theorem prismMissingFacet_notBoundary {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) (a : PrismCell v) :
    ¬ (dcylDBoundaryComplex v).S
      (eraseDV a.val (DV.mid (topSet a.val))) := by
  classical
  intro hB
  let F := eraseDV a.val (DV.mid (topSet a.val))
  rcases a.property.2.2.1 with ⟨j, hj⟩
  have htopA : DV.top j ∈ a.val := (Finset.mem_filter.mp hj).2
  have htopF : DV.top j ∈ F := by
    exact Finset.mem_erase.mpr ⟨by simp, htopA⟩
  rcases hB.2 with hbot | ⟨i, hi, hside⟩
  · obtain ⟨c, hc⟩ := hbot _ htopF
    cases hc
  · by_cases hiT : i ∈ topSet a.val
    · have htopi : DV.top i ∈ a.val := (Finset.mem_filter.mp hiT).2
      exact hi (Finset.mem_erase.mpr ⟨by simp, htopi⟩)
    · by_cases hTfull : topSet a.val = Finset.univ
      · have hiT' : i ∈ topSet a.val := hTfull.symm ▸ Finset.mem_univ i
        exact hiT hiT'
      · have hfullF : DV.mid Finset.univ ∈ F := by
          apply Finset.mem_erase.mpr
          refine ⟨?_, a.property.2.1⟩
          intro heq
          injection heq with hEq
          exact hTfull hEq.symm
        exact hside _ hfullF (Finset.mem_univ i)

private theorem elementary_anodyne_of_isPushout {A B D E : SemiSSet.{u}}
    {f : A ⟶ B} {g : A ⟶ D} {f' : D ⟶ E} {g' : B ⟶ E}
    (sq : IsPushout g f f' g')
    (hf : (hornInclusions.pushouts ⊔ MorphismProperty.isomorphisms SemiSSet.{u}) f) :
    (hornInclusions.pushouts ⊔ MorphismProperty.isomorphisms SemiSSet.{u}) f' := by
  rcases hf with hf | hf
  · exact Or.inl (MorphismProperty.of_isPushout sq hf)
  · haveI : IsIso f := hf
    exact Or.inr sq.isIso_inl_of_isIso

/-- Finite composites of horn pushouts and isomorphisms are stable under pushout. -/
theorem anodyne_of_isPushout {A B D E : SemiSSet.{u}}
    {f : A ⟶ B} {g : A ⟶ D} {f' : D ⟶ E} {g' : B ⟶ E}
    (sq : IsPushout g f f' g') (hf : anodyne f) : anodyne f' := by
  unfold anodyne at hf ⊢
  induction hf generalizing D E with
  | of f hf =>
    exact .of _ (elementary_anodyne_of_isPushout sq hf)
  | id A =>
    exact .of _ (Or.inr sq.isIso_inl_of_isIso)
  | @comp_of A B C f h hf hh ih =>
    have left := IsPushout.of_hasPushout g f
    have right := sq.of_top' left
    have hi := ih left
    have ht := elementary_anodyne_of_isPushout right hh
    simpa only [IsPushout.inl_desc] using
      MorphismProperty.multiplicativeClosure.comp_of _ _ hi ht

private theorem anodyne_horn {r : ℕ} (k : Fin (r + 2)) :
    anodyne ((horn.{u} (r + 1) k).ι) := by
  unfold anodyne
  apply MorphismProperty.multiplicativeClosure.of
  apply Or.inl
  apply hornInclusions.le_pushouts
  change MorphismProperty.ofHoms
    (fun p : Σ d : ℕ, Fin (d + 2) => (horn.{u} (p.1 + 1) p.2).ι)
    ((horn.{u} (r + 1) k).ι)
  exact MorphismProperty.ofHoms.mk
    (f := fun p : Σ d : ℕ, Fin (d + 2) => (horn.{u} (p.1 + 1) p.2).ι) ⟨r, k⟩

private theorem isPushout_hornCell {r : ℕ} (k : Fin (r + 2))
    {K : SemiSSet.{u}} (S : Subfunctor K)
    (η : HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk (r + 1)) ⟶ K) [Mono η]
    (hfaces : Subfunctor.range ((horn.{u} (r + 1) k).ι ≫ η) ≤ S)
    (hinter : ∀ (X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ)
      (x : (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk (r + 1))).obj X),
      η.app X x ∈ S.obj X → x ∈ (horn.{u} (r + 1) k).obj X) :
    IsPushout (horn.{u} (r + 1) k).ι
      (Subfunctor.lift ((horn.{u} (r + 1) k).ι ≫ η) hfaces)
      (Subfunctor.lift η (G := Subfunctor.range η) (by rfl) ≫
        Subfunctor.homOfLe (G := Subfunctor.range η)
          (le_sup_right : Subfunctor.range η ≤ S ⊔ Subfunctor.range η))
      (Subfunctor.homOfLe (G := S) (le_sup_left : S ≤ S ⊔ Subfunctor.range η)) := by
  let g := Subfunctor.lift ((horn.{u} (r + 1) k).ι ≫ η) hfaces
  have hcomm : (horn.{u} (r + 1) k).ι ≫ η = g ≫ S.ι := by
    simp [g]
  exact isPushout_subfunctor_sup_range
    (C := HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ)
    (horn.{u} (r + 1) k) S η g hcomm hinter

private theorem anodyne_subfunctor_hornStep {r : ℕ} (k : Fin (r + 2))
    {K : SemiSSet.{u}} (S T : Subfunctor K)
    (η : HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk (r + 1)) ⟶ K) [Mono η]
    (hfaces : Subfunctor.range ((horn.{u} (r + 1) k).ι ≫ η) ≤ S)
    (hinter : ∀ (X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ)
      (x : (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk (r + 1))).obj X),
      η.app X x ∈ S.obj X → x ∈ (horn.{u} (r + 1) k).obj X)
    (hT : T = S ⊔ Subfunctor.range η) (hle : S ≤ T) :
    anodyne (Subfunctor.homOfLe hle) := by
  subst T
  have hsq := isPushout_hornCell k S η hfaces hinter
  have hh := anodyne_of_isPushout hsq.flip (anodyne_horn k)
  simpa using hh

private theorem mapCell_hornStep {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) (H : Finset (MapCell v)) (a : MapCell v)
    (hDown : ∀ b : MapCell v, mapCellOrderRank b < mapCellOrderRank a → b ∈ H)
    (hUpper : ∀ b : MapCell v, b ∈ H → mapCellOrderRank b < mapCellOrderRank a) :
    anodyne.{u} (Subfunctor.homOfLe
      (show mapStage v H ≤ mapStage v (insert a H) from by
        rw [mapStage_insert]
        exact le_sup_left)) := by
  classical
  let S := mapStage v H
  let T := mapStage v (insert a H)
  let η := mapCellSimplex v a
  let r := a.val.card - 2
  have hge := mapCell_card_ge_two a
  have hcard : a.val.card = r + 2 := by dsimp [r]; omega
  let k : Fin (r + 2) := mapCellPivotIndex (v := v) a
  have hPivotIndex : (a.val.orderEmbOfFin hcard) k = DV.bot (botPivot v a.val) := by
    simpa [k] using mapCellPivotIndex_apply a hcard
  have hmono : Mono η := by
    dsimp [η, mapCellSimplex]
    exact simplexOfVertexSet_mono v a.val hcard a.property.1
  letI : Mono η := hmono
  have hfaces : Subfunctor.range ((horn.{u} (r + 1) k).ι ≫ η) ≤ S := by
    intro X x hx
    rcases hx with ⟨τ, rfl⟩
    rcases τ with ⟨σ, hσ⟩
    change η.app X σ ∈ S.obj X
    obtain ⟨j, hjk, hverts⟩ := simplexOfVertexSet_horn_facet_subset
      v a.val hcard a.property.1 X k σ hσ
    have hverts' : dcylVertices (η.app X σ) ⊆
        eraseDV a.val (a.val.orderEmbOfFin hcard j) := by
      simpa [η, mapCellSimplex] using hverts
    let z := (a.val.orderEmbOfFin hcard) j
    have hz : z ∈ a.val := by
      exact Finset.orderEmbOfFin_mem a.val hcard j
    have hzk : z ≠ DV.bot (botPivot v a.val) := by
      intro h
      apply hjk
      apply (a.val.orderEmbOfFin hcard).injective
      calc
        (a.val.orderEmbOfFin hcard) j = z := rfl
        _ = DV.bot (botPivot v a.val) := h
        _ = (a.val.orderEmbOfFin hcard) k := hPivotIndex.symm
    rcases mapCell_otherFacet v a z hz hzk with hboundary | ⟨b, hfacet, hbrank⟩
    · have hboundary' : (dcylDBoundaryComplex v).S (dcylVertices (η.app X σ)) :=
        (dcylDBoundaryComplex v).down hverts' hboundary
      exact (mapStage_mem_iff v H X (η.app X σ)).2
        (Or.inl (boundaryStage_of_vertices v X (η.app X σ) hboundary'))
    · have hb : b ∈ H := hDown b (mapCellOrderRank_lt_of_rank_lt hbrank)
      have hxrange : η.app X σ ∈ (Subfunctor.range (mapCellSimplex v b)).obj X :=
        mem_mapCellRange_of_vertices_subset v b X (η.app X σ)
          (Finset.Subset.trans hverts' hfacet)
      exact (mapStage_mem_iff v H X (η.app X σ)).2 (Or.inr ⟨b, hb, hxrange⟩)
  have hNoBoundary : ¬ (dcylDBoundaryComplex v).S
      (eraseDV a.val (DV.bot (botPivot v a.val))) := by
    intro h
    have hfull : DV.mid (Finset.univ : Finset (Fin (n + 1))) ∈
        eraseDV a.val (DV.bot (botPivot v a.val)) := by
      apply Finset.mem_erase.mpr
      exact ⟨by simp, a.property.2.1⟩
    rcases h.2 with hbot | ⟨i, hi, hside⟩
    · obtain ⟨c, hc⟩ := hbot _ hfull
      cases hc
    · exact hside _ hfull (Finset.mem_univ i)
  have hinter : ∀ (X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ)
      (σ : (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk (r + 1))).obj X),
      η.app X σ ∈ S.obj X → σ ∈ (horn.{u} (r + 1) k).obj X := by
    intro X σ hσS
    by_contra hσ
    have hmissing : eraseDV a.val (DV.bot (botPivot v a.val)) ⊆
        dcylVertices (η.app X σ) := by
      simpa [η, mapCellSimplex, k, hPivotIndex] using
        (simplexOfVertexSet_nonhorn_facet_subset
          v a.val hcard a.property.1 X k σ hσ)
    rcases (mapStage_mem_iff v H X (η.app X σ)).1 hσS with hbnd | ⟨b, hb, hrange⟩
    · have hboundary := boundaryStage_vertices v X (η.app X σ) hbnd
      exact hNoBoundary ((dcylDBoundaryComplex v).down hmissing hboundary)
    · have hverts := mapCellRange_vertices_subset v b X (η.app X σ) hrange
      have hcoface : a.val.erase (DV.bot (botPivot v a.val)) ⊆ b.val := by
        exact Finset.Subset.trans hmissing hverts
      have hba : a ≠ b := by
        intro hab
        subst b
        exact (lt_irrefl _ (hUpper a hb))
      have hrank := mapCell_missingFacet_coface_rank v a b hba hcoface
      have htotal := mapCellOrderRank_lt_of_rank_lt hrank
      exact (lt_asymm htotal (hUpper b hb))
  have hT : T = S ⊔ Subfunctor.range η := by
    simpa [T, S, η] using mapStage_insert v H a
  have hle : S ≤ T := by rw [hT]; exact le_sup_left
  exact anodyne_subfunctor_hornStep k S T η hfaces hinter hT hle

/-- Each prism cell attaches along the horn opposite its distinguished middle vertex. -/
private theorem prismCell_hornStep {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) (H : Finset (PrismCell v)) (a : PrismCell v)
    (hDown : ∀ b : PrismCell v, prismCellOrderRank b < prismCellOrderRank a → b ∈ H)
    (hUpper : ∀ b : PrismCell v, b ∈ H → prismCellOrderRank b < prismCellOrderRank a) :
    anodyne.{u} (Subfunctor.homOfLe
      (show prismStage v H ≤ prismStage v (insert a H) from by
        rw [prismStage_insert]
        exact le_sup_left)) := by
  classical
  let S := prismStage v H
  let T := prismStage v (insert a H)
  let η := prismCellSimplex v a
  let r := a.val.card - 2
  have hge := prismCell_card_ge_two a
  have hcard : a.val.card = r + 2 := by dsimp [r]; omega
  let k : Fin (r + 2) := prismCellPivotIndex (v := v) a
  have hPivotIndex : (a.val.orderEmbOfFin hcard) k = DV.mid (topSet a.val) := by
    simpa [k] using prismCellPivotIndex_apply a hcard
  have hmono : Mono η := by
    dsimp [η, prismCellSimplex]
    exact simplexOfVertexSet_mono v a.val hcard a.property.1
  letI : Mono η := hmono
  have hfaces : Subfunctor.range ((horn.{u} (r + 1) k).ι ≫ η) ≤ S := by
    intro X x hx
    rcases hx with ⟨τ, rfl⟩
    rcases τ with ⟨σ, hσ⟩
    change η.app X σ ∈ S.obj X
    obtain ⟨j, hjk, hverts⟩ := simplexOfVertexSet_horn_facet_subset
      v a.val hcard a.property.1 X k σ hσ
    have hverts' : dcylVertices (η.app X σ) ⊆
        eraseDV a.val (a.val.orderEmbOfFin hcard j) := by
      simpa [η, prismCellSimplex] using hverts
    let z := (a.val.orderEmbOfFin hcard) j
    have hz : z ∈ a.val := Finset.orderEmbOfFin_mem a.val hcard j
    have hzk : z ≠ DV.mid (topSet a.val) := by
      intro h
      apply hjk
      apply (a.val.orderEmbOfFin hcard).injective
      calc
        (a.val.orderEmbOfFin hcard) j = z := rfl
        _ = DV.mid (topSet a.val) := h
        _ = (a.val.orderEmbOfFin hcard) k := hPivotIndex.symm
    rcases prismCell_otherFacet v a z hz hzk with hboundary | hnoTop | ⟨b, hfacet, hbrank⟩
    · have hboundary' : (dcylDBoundaryComplex v).S (dcylVertices (η.app X σ)) :=
        (dcylDBoundaryComplex v).down hverts' hboundary
      have hbase : η.app X σ ∈ (mapStage v Finset.univ).obj X :=
        (mapStage_mem_iff v Finset.univ X (η.app X σ)).2
          (Or.inl (boundaryStage_of_vertices v X (η.app X σ) hboundary'))
      exact (prismStage_mem_iff v H X (η.app X σ)).2 (Or.inl hbase)
    · have hNoTopX : ∀ i, DV.top i ∉ dcylVertices (η.app X σ) := by
        intro i hi
        exact hnoTop i (hverts' hi)
      exact (prismStage_mem_iff v H X (η.app X σ)).2
        (Or.inl (mapStage_contains_noTop v X (η.app X σ) hNoTopX))
    · have hb : b ∈ H := hDown b (prismCellOrderRank_lt_of_rank_lt hbrank)
      have hxrange : η.app X σ ∈ (Subfunctor.range (prismCellSimplex v b)).obj X :=
        mem_prismCellRange_of_vertices_subset v b X (η.app X σ)
          (Finset.Subset.trans hverts' hfacet)
      exact (prismStage_mem_iff v H X (η.app X σ)).2 (Or.inr ⟨b, hb, hxrange⟩)
  have hNoBoundary := prismMissingFacet_notBoundary v a
  have hinter : ∀ (X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ)
      (σ : (HomotopyHypothesis.Henry.SemiSSet.stdSimplex.{u}.obj
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk (r + 1))).obj X),
      η.app X σ ∈ S.obj X → σ ∈ (horn.{u} (r + 1) k).obj X := by
    intro X σ hσS
    by_contra hσ
    have hmissing : eraseDV a.val (DV.mid (topSet a.val)) ⊆
        dcylVertices (η.app X σ) := by
      simpa [η, prismCellSimplex, k, hPivotIndex] using
        (simplexOfVertexSet_nonhorn_facet_subset
          v a.val hcard a.property.1 X k σ hσ)
    rcases (prismStage_mem_iff v H X (η.app X σ)).1 hσS with hbase | ⟨b, hb, hrange⟩
    · rcases (mapStage_mem_iff v Finset.univ X (η.app X σ)).1 hbase with hbnd | ⟨c, hc, hrangeC⟩
      · have hboundary := boundaryStage_vertices v X (η.app X σ) hbnd
        exact hNoBoundary ((dcylDBoundaryComplex v).down hmissing hboundary)
      · have hvertsC := mapCellRange_vertices_subset v c X (η.app X σ) hrangeC
        rcases a.property.2.2.1 with ⟨j, hj⟩
        have htopA : DV.top j ∈ a.val := (Finset.mem_filter.mp hj).2
        have htopF : DV.top j ∈ eraseDV a.val (DV.mid (topSet a.val)) := by
          exact Finset.mem_erase.mpr ⟨by simp, htopA⟩
        have htopX : DV.top j ∈ dcylVertices (η.app X σ) := hmissing htopF
        have htopC : DV.top j ∈ c.val := hvertsC htopX
        exact c.property.2.2.1 j htopC
    · have hvertsB := prismCellRange_vertices_subset v b X (η.app X σ) hrange
      have hcoface : a.val.erase (DV.mid (topSet a.val)) ⊆ b.val := by
        exact Finset.Subset.trans hmissing hvertsB
      have hba : a ≠ b := by
        intro hab
        subst b
        exact (lt_irrefl _ (hUpper a hb))
      have hrank := prismCell_missingFacet_coface_rank v a b hba hcoface
      have htotal := prismCellOrderRank_lt_of_rank_lt hrank
      exact (lt_asymm htotal (hUpper b hb))
  have hT : T = S ⊔ Subfunctor.range η := by
    simpa [T, S, η] using prismStage_insert v H a
  have hle : S ≤ T := by rw [hT]; exact le_sup_left
  exact anodyne_subfunctor_hornStep k S T η hfaces hinter hT hle


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

private def mapCellsDownClosed {n m : ℕ} {v : Fin (n + 1) → Fin (m + 1)}
    (H : Finset (MapCell v)) : Prop :=
  ∀ a ∈ H, ∀ b, mapCellOrderRank b < mapCellOrderRank a → b ∈ H

private theorem mapStage_downClosed_anodyne {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) (H : Finset (MapCell v))
    (hdown : mapCellsDownClosed H) :
    anodyne.{u} (Subfunctor.homOfLe
      (show boundaryStage v ≤ mapStage v H from le_sup_left)) := by
  classical
  induction H using Finset.induction_on_max_value (mapCellOrderRank (v := v)) with
  | empty =>
      let f : (boundaryStage v).toFunctor ⟶ (mapStage v ∅).toFunctor :=
        Subfunctor.homOfLe (show boundaryStage v ≤ mapStage v ∅ from le_sup_left)
      have hEq : mapStage v ∅ = boundaryStage v := by simp [mapStage]
      have hIso : IsIso.{u, u + 1} f := by
        rw [NatTrans.isIso_iff_isIso_app]
        intro X
        rw [isIso_iff_bijective]
        constructor
        · exact (mono_iff_injective _).1 inferInstance
        · intro y
          have hobj := congrArg (fun S : Subfunctor (dcylD.{u} v) => S.obj X) hEq
          have hy : y.val ∈ (boundaryStage v).obj X := by
            exact Eq.mp
              (congrArg (fun S : Set ((dcylD.{u} v).obj X) => y.val ∈ S) hobj) y.property
          refine ⟨⟨y.val, hy⟩, ?_⟩
          apply Subtype.ext
          rfl
      unfold anodyne
      exact MorphismProperty.multiplicativeClosure.of _
        (Or.inr (MorphismProperty.isomorphisms.infer_property f))
  | insert a H ha hmax ih =>
      have hdownH : mapCellsDownClosed H := by
        intro b hb c hcb
        have hc := hdown b (Finset.mem_insert_of_mem hb) c hcb
        rcases Finset.mem_insert.mp hc with hca | hcH
        · subst c
          have hle := hmax b hb
          exact False.elim ((not_lt_of_ge hle) hcb)
        · exact hcH
      have hLower : ∀ b : MapCell v, mapCellOrderRank b < mapCellOrderRank a → b ∈ H := by
        intro b hba
        have hb := hdown a (Finset.mem_insert_self a H) b hba
        rcases Finset.mem_insert.mp hb with hEq | hbH
        · subst b
          exact False.elim (lt_irrefl _ hba)
        · exact hbH
      have hUpper : ∀ b : MapCell v, b ∈ H → mapCellOrderRank b < mapCellOrderRank a := by
        intro b hb
        have hle := hmax b hb
        by_contra hnot
        have heq : mapCellOrderRank b = mapCellOrderRank a :=
          le_antisymm hle (le_of_not_gt hnot)
        have hba : b = a := mapCellOrderRank_injective heq
        subst b
        exact ha hb
      have hIH := ih hdownH
      have hstep := mapCell_hornStep v H a hLower hUpper
      have hle₁ : boundaryStage v ≤ mapStage v H := le_sup_left
      have hle₂ : mapStage v H ≤ mapStage v (insert a H) := by
        rw [mapStage_insert]
        exact le_sup_left
      have hcomp := anodyne_comp hIH hstep
      rw [subfunctor_homOfLe_comp hle₁ hle₂] at hcomp
      exact hcomp

private theorem boundary_to_mapStage_all_anodyne {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) :
    anodyne.{u} (Subfunctor.homOfLe
      (show boundaryStage v ≤ mapStage v Finset.univ from le_sup_left)) := by
  apply mapStage_downClosed_anodyne
  intro a ha b hba
  exact Finset.mem_univ b

private def prismCellsDownClosed {n m : ℕ} {v : Fin (n + 1) → Fin (m + 1)}
    (H : Finset (PrismCell v)) : Prop :=
  ∀ a ∈ H, ∀ b, prismCellOrderRank b < prismCellOrderRank a → b ∈ H

private theorem prismStage_downClosed_anodyne {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) (H : Finset (PrismCell v))
    (hdown : prismCellsDownClosed H) :
    anodyne.{u} (Subfunctor.homOfLe
      (show mapStage v Finset.univ ≤ prismStage v H from le_sup_left)) := by
  classical
  induction H using Finset.induction_on_max_value (prismCellOrderRank (v := v)) with
  | empty =>
      let f : (mapStage v Finset.univ).toFunctor ⟶ (prismStage v ∅).toFunctor :=
        Subfunctor.homOfLe (show mapStage v Finset.univ ≤ prismStage v ∅ from le_sup_left)
      have hEq : prismStage v ∅ = mapStage v Finset.univ := by simp [prismStage]
      have hIso : IsIso.{u, u + 1} f := by
        rw [NatTrans.isIso_iff_isIso_app]
        intro X
        rw [isIso_iff_bijective]
        constructor
        · exact (mono_iff_injective _).1 inferInstance
        · intro y
          have hobj := congrArg (fun S : Subfunctor (dcylD.{u} v) => S.obj X) hEq
          have hy : y.val ∈ (mapStage v Finset.univ).obj X := by
            exact Eq.mp
              (congrArg (fun S : Set ((dcylD.{u} v).obj X) => y.val ∈ S) hobj) y.property
          refine ⟨⟨y.val, hy⟩, ?_⟩
          apply Subtype.ext
          rfl
      unfold anodyne
      exact MorphismProperty.multiplicativeClosure.of _
        (Or.inr (MorphismProperty.isomorphisms.infer_property f))
  | insert a H ha hmax ih =>
      have hdownH : prismCellsDownClosed H := by
        intro b hb c hcb
        have hc := hdown b (Finset.mem_insert_of_mem hb) c hcb
        rcases Finset.mem_insert.mp hc with hca | hcH
        · subst c
          have hle := hmax b hb
          exact False.elim ((not_lt_of_ge hle) hcb)
        · exact hcH
      have hLower : ∀ b : PrismCell v, prismCellOrderRank b < prismCellOrderRank a → b ∈ H := by
        intro b hba
        have hb := hdown a (Finset.mem_insert_self a H) b hba
        rcases Finset.mem_insert.mp hb with hEq | hbH
        · subst b
          exact False.elim (lt_irrefl _ hba)
        · exact hbH
      have hUpper : ∀ b : PrismCell v, b ∈ H → prismCellOrderRank b < prismCellOrderRank a := by
        intro b hb
        have hle := hmax b hb
        by_contra hnot
        have heq : prismCellOrderRank b = prismCellOrderRank a :=
          le_antisymm hle (le_of_not_gt hnot)
        have hba : b = a := prismCellOrderRank_injective heq
        subst b
        exact ha hb
      have hIH := ih hdownH
      have hstep := prismCell_hornStep v H a hLower hUpper
      have hle₁ : mapStage v Finset.univ ≤ prismStage v H := le_sup_left
      have hle₂ : prismStage v H ≤ prismStage v (insert a H) := by
        rw [prismStage_insert]
        exact le_sup_left
      have hcomp := anodyne_comp hIH hstep
      rw [subfunctor_homOfLe_comp hle₁ hle₂] at hcomp
      exact hcomp

private theorem mapStage_all_to_prismStage_all_anodyne {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) :
    anodyne.{u} (Subfunctor.homOfLe
      (show mapStage v Finset.univ ≤ prismStage v Finset.univ from le_sup_left)) := by
  apply prismStage_downClosed_anodyne
  intro a ha b hba
  exact Finset.mem_univ b

private theorem dcylD_addFullMid_of_top {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) (A : Finset (DV n m))
    (hK : (dcylDComplex v).S A) (hT : (topSet A).Nonempty) :
    (dcylDComplex v).S (insert (DV.mid (Finset.univ : Finset (Fin (n + 1)))) A) := by
  classical
  obtain ⟨i, hiT⟩ := hT
  have htop : DV.top i ∈ A := (Finset.mem_filter.mp hiT).2
  have hNoBot : ∀ c, DV.bot c ∉ A := by
    intro c hc
    exact hK.2.2.1 i c htop hc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro S hS
    rcases Finset.mem_insert.mp hS with h | h
    · injection h with hEq
      subst S
      exact ⟨0, Finset.mem_univ _⟩
    · exact hK.1 S h
  · intro S S' hS hS'
    rcases Finset.mem_insert.mp hS with h | h
    · injection h with hEq
      subst S
      exact Or.inr (Finset.subset_univ _)
    · rcases Finset.mem_insert.mp hS' with h' | h'
      · injection h' with hEq
        subst S'
        exact Or.inl (Finset.subset_univ _)
      · exact hK.2.1 S S' h h'
  · intro j c hj hc
    have hcA : DV.bot c ∈ A := by
      rcases Finset.mem_insert.mp hc with h | h
      · cases h
      · exact h
    exact False.elim (hNoBot c hcA)
  · intro j S hj hS
    have hjA : DV.top j ∈ A := by
      rcases Finset.mem_insert.mp hj with h | h
      · cases h
      · exact h
    rcases Finset.mem_insert.mp hS with h | h
    · injection h with hEq
      subst S
      exact Finset.mem_univ j
    · exact hK.2.2.2.1 j S hjA h
  · intro c S hc hS
    have hcA : DV.bot c ∈ A := by
      rcases Finset.mem_insert.mp hc with h | h
      · cases h
      · exact h
    exact False.elim (hNoBot c hcA)

private theorem prismStage_contains_all {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1))
    (X : HomotopyHypothesis.Henry.SemiSimplexCategoryᵒᵖ)
    (x : (dcylD.{u} v).obj X) : x ∈ (prismStage v Finset.univ).obj X := by
  classical
  by_cases hNoTop : ∀ i, DV.top i ∉ dcylVertices x
  · exact (prismStage_mem_iff v Finset.univ X x).2
      (Or.inl (mapStage_contains_noTop v X x hNoTop))
  · obtain ⟨i, hi⟩ := Classical.not_forall.mp hNoTop
    have hiV : DV.top i ∈ dcylVertices x := by
      by_contra h
      exact hi h
    let A := dcylVertices x
    have hK : (dcylDComplex v).S A := x.down.2.2
    have hT : (topSet A).Nonempty :=
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiV⟩⟩
    let F := insert (DV.mid (Finset.univ : Finset (Fin (n + 1)))) A
    have hKF : (dcylDComplex v).S F := by
      simpa [F] using dcylD_addFullMid_of_top v A hK hT
    have htopSetF : topSet F = topSet A := by
      ext j
      simp [topSet, F]
    have hTF : (topSet F).Nonempty := by rw [htopSetF]; exact hT
    let B := insert (DV.mid (topSet F)) F
    have hKB : (dcylDComplex v).S B := by
      simpa [B] using dcylD_addTopPivot v F hKF hTF
    have htopSetB : topSet B = topSet F := by
      ext j
      simp [topSet, B]
    have hfullB : DV.mid Finset.univ ∈ B :=
      Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have hTB : (topSet B).Nonempty := by rw [htopSetB, htopSetF]; exact hT
    have hpivotB : DV.mid (topSet B) ∈ B := by
      rw [htopSetB]
      exact Finset.mem_insert_self _ _
    let b : PrismCell v := ⟨B, ⟨hKB, hfullB, hTB, hpivotB⟩⟩
    have hverts : dcylVertices x ⊆ b.val := by
      intro z hz
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz)
    have hrange := mem_prismCellRange_of_vertices_subset v b X x hverts
    exact (prismStage_mem_iff v Finset.univ X x).2
      (Or.inr ⟨b, Finset.mem_univ _, hrange⟩)

private theorem prismStage_all_eq_top {n m : ℕ}
    (v : Fin (n + 1) → Fin (m + 1)) : prismStage v Finset.univ = ⊤ := by
  apply le_antisymm
  · exact le_top
  · intro X x hx
    exact prismStage_contains_all v X x

/-- The derived double cylinder collapses onto its boundary by elementary horn attachments. -/
theorem anodyne_dcylDBoundaryι_proof {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1)) :
    anodyne (dcylDBoundaryι.{u} v) := by
  classical
  let η := dcylDBoundaryι.{u} v
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
  have hle₁ : boundaryStage v ≤ mapStage v Finset.univ := le_sup_left
  have hle₂ : mapStage v Finset.univ ≤ prismStage v Finset.univ := le_sup_left
  have hStage : anodyne (Subfunctor.homOfLe (hle₁.trans hle₂)) := by
    have hcomp := anodyne_comp
      (boundary_to_mapStage_all_anodyne v) (mapStage_all_to_prismStage_all_anodyne v)
    rw [subfunctor_homOfLe_comp hle₁ hle₂] at hcomp
    exact hcomp
  have hfull : prismStage v Finset.univ = ⊤ := prismStage_all_eq_top v
  haveI : IsIso (Subfunctor.ι (prismStage v Finset.univ)) := by
    rw [hfull]
    infer_instance
  have hstageι : anodyne (Subfunctor.ι (prismStage v Finset.univ)) := by
    unfold anodyne
    apply MorphismProperty.multiplicativeClosure.of
    exact Or.inr (MorphismProperty.isomorphisms.infer_property _)
  have hboundaryStageι : anodyne (Subfunctor.ι (boundaryStage v)) := by
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

#print axioms anodyne_dcylDBoundaryι_proof

end HomotopyHypothesis.Cylinder.DoubleBoundaryCollapse
