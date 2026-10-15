import HomotopyHypothesis.Cylinder.SimplicialCategory.Cofibrations
import HomotopyHypothesis.Cylinder.SimplicialCategory.FreeAlgKan
import HomotopyHypothesis.Blueprint.Henry.Packages.Simplicial.CDeltaHornWeakEquivalence
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Cylinder.SemisimplicialCategory.WeakEquivalences
/-!
# Subfunctors of standard simplices and cellularity of free algebraic Kan complexes

This file proves:
1. For any `N : ℕ` and `S ≤ T : Subfunctor (SemiSSet.stdSimplex.obj (SemiSimplexCategory.mk N))`,
   the induced map `freeAlgKanMap (Subfunctor.homOfLe hST)` is in `AlgKan.cellularMaps`.
2. For any `S : Subfunctor (SemiSSet.stdSimplex.obj (SemiSimplexCategory.mk N))`,
   `freeAlgKan S.toFunctor` is finitely cellular (`CDelta.{u}`), and so is
   `freeAlgKan (SemiSSet.stdSimplex.obj (SemiSimplexCategory.mk N))`.
3. Inside `Δ_{n+1}`, the union of the `(n+1)`-th face `missingLastSubfunctor n ≅ Δ_n` and the
   horn `Λ^{n+1}_{n+1}` is `∂Δ_{n+1}`, and their intersection is isomorphic to `∂Δ_n`, inducing
   a pushout square of cofibrations in `CDelta.{u}`.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra Opposite ConcreteCategory

namespace HomotopyHypothesis.Cylinder.SimplicialCategory

open HomotopyHypothesis.Henry

/-!
## Combinatorics of `Henry.SemiSimplexCategory` and `SemiSSet.boundary`
-/

lemma strictMono_id_le {n : ℕ} {f : Fin n → Fin n} (hf : StrictMono f) :
    ∀ i : Fin n, i ≤ f i := by
  have haux : ∀ (k : ℕ) (hk : k < n), k ≤ (f ⟨k, hk⟩).1 := by
    intro k
    induction k with
    | zero =>
      intro _
      exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have hk' : k < n := Nat.lt_of_succ_lt hk
      have h1 : k ≤ (f ⟨k, hk'⟩).1 := ih hk'
      have h2 : f ⟨k, hk'⟩ < f ⟨k + 1, hk⟩ := hf (Fin.mk_lt_mk.mpr (Nat.lt_succ_self k))
      exact Nat.succ_le_of_lt (lt_of_le_of_lt h1 h2)
  intro i
  exact Fin.le_def.mpr (haux i.1 i.2)

lemma strictMono_eq_id {n : ℕ} {f : Fin n → Fin n} (hf : StrictMono f) (i : Fin n) :
    f i = i := by
  have h1 : i ≤ f i := strictMono_id_le hf i
  let g : Fin n → Fin n := fun j => (f j.rev).rev
  have hg : StrictMono g := by
    intro a b hab
    exact Fin.rev_lt_rev.mpr (hf (Fin.rev_lt_rev.mpr hab))
  have h2 := strictMono_id_le hg i.rev
  dsimp [g] at h2
  rw [Fin.rev_rev, Fin.rev_le_rev] at h2
  exact le_antisymm h2 h1

lemma strictMono_toOrderHom {Δ₁ Δ₂ : Henry.SemiSimplexCategory} (f : Δ₁ ⟶ Δ₂) :
    StrictMono f.hom.toOrderHom :=
  f.hom.toOrderHom.monotone.strictMono_of_injective
    (SimplexCategory.mono_iff_injective.mp f.property)

lemma len_le_of_hom {Δ₁ Δ₂ : Henry.SemiSimplexCategory} (f : Δ₁ ⟶ Δ₂) :
    Δ₁.obj.len ≤ Δ₂.obj.len := by
  have : Mono f.hom := f.property
  exact SimplexCategory.le_of_mono f.hom

lemma hom_eq_id_of_end {Δ : Henry.SemiSimplexCategory} (f : Δ ⟶ Δ) :
    f = 𝟙 Δ := by
  apply Henry.SemiSimplexCategory.incl.map_injective
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  exact strictMono_eq_id (strictMono_toOrderHom f) i

lemma cancel_mono_semiSimplex {Δ₁ Δ₂ Δ₃ : Henry.SemiSimplexCategory}
    (σ : Δ₂ ⟶ Δ₃) {g₁ g₂ : Δ₁ ⟶ Δ₂} (h : g₁ ≫ σ = g₂ ≫ σ) :
    g₁ = g₂ := by
  have hhom : g₁.hom ≫ σ.hom = g₂.hom ≫ σ.hom :=
    congrArg Henry.SemiSimplexCategory.incl.map h
  have : Mono σ.hom := σ.property
  exact Henry.SemiSimplexCategory.incl.map_injective ((cancel_mono σ.hom).mp hhom)

noncomputable instance fintypeSemiSimplexHom (Δ₁ Δ₂ : Henry.SemiSimplexCategory) :
    Fintype (Δ₁ ⟶ Δ₂) :=
  Fintype.ofInjective
    (fun (f : Δ₁ ⟶ Δ₂) => (f.hom.toOrderHom : Fin (Δ₁.obj.len + 1) → Fin (Δ₂.obj.len + 1)))
    (fun f g h => by
      apply Henry.SemiSimplexCategory.incl.map_injective
      apply SimplexCategory.Hom.ext
      apply OrderHom.ext
      funext i
      exact congrFun h i)

noncomputable instance decidableEqSemiSimplexHom (Δ₁ Δ₂ : Henry.SemiSimplexCategory) :
    DecidableEq (Δ₁ ⟶ Δ₂) :=
  Classical.decEq _

lemma mem_boundary_iff {m : ℕ} {Δ : Henry.SemiSimplexCategoryᵒᵖ}
    (x : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m)).obj Δ) :
    x ∈ (SemiSSet.boundary.{u} m).obj Δ ↔ (unop Δ).obj.len < m := by
  constructor
  · rintro ⟨j, hj⟩
    have hle : (unop Δ).obj.len ≤ m := len_le_of_hom (ULift.down x)
    by_contra hnotlt
    have heq_len : (unop Δ).obj.len = m := le_antisymm hle (not_lt.mp hnotlt)
    cases Δ with | op Δ₀ =>
    cases Δ₀ with | mk obj =>
    cases obj with | mk len =>
    dsimp at heq_len
    subst heq_len
    rcases x with ⟨g⟩
    have hg : g = 𝟙 (Henry.SemiSimplexCategory.mk len) := hom_eq_id_of_end g
    subst hg
    exact hj ⟨j, rfl⟩
  · intro hlt
    by_contra hnot
    have hsurj : Function.Surjective (ULift.down x).hom.toOrderHom := by
      intro j
      by_contra hj
      exact hnot ⟨j, hj⟩
    have hcard := Fintype.card_le_of_surjective _ hsurj
    simp only [Fintype.card_fin] at hcard
    omega

lemma eq_mk_and_eq_id_of_not_mem_boundary {m : ℕ} {Δ : Henry.SemiSimplexCategoryᵒᵖ}
    {x : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m)).obj Δ}
    (hx : x ∉ (SemiSSet.boundary.{u} m).obj Δ) :
    ∃ hΔ : unop Δ = Henry.SemiSimplexCategory.mk m,
      ULift.down x = eqToHom hΔ := by
  have hle : (unop Δ).obj.len ≤ m := len_le_of_hom (ULift.down x)
  have hnotlt : ¬ (unop Δ).obj.len < m := fun hlt => hx ((mem_boundary_iff x).mpr hlt)
  have heq_len : (unop Δ).obj.len = m := le_antisymm hle (not_lt.mp hnotlt)
  cases Δ with | op Δ₀ =>
  cases Δ₀ with | mk obj =>
  cases obj with | mk len =>
  dsimp at heq_len
  subst heq_len
  refine ⟨rfl, ?_⟩
  simpa using hom_eq_id_of_end (ULift.down x)

/-!
## Single-simplex subfunctor attachments and cellular maps
-/

lemma cellularMaps_freeAlgKanMap_trans {B : SemiSSet.{u}} {S₁ S₂ S₃ : Subfunctor B}
    (h₁₂ : S₁ ≤ S₂) (h₂₃ : S₂ ≤ S₃)
    (hc₁₂ : AlgKan.cellularMaps (freeAlgKanMap (Subfunctor.homOfLe h₁₂)))
    (hc₂₃ : AlgKan.cellularMaps (freeAlgKanMap (Subfunctor.homOfLe h₂₃))) :
    AlgKan.cellularMaps (freeAlgKanMap (Subfunctor.homOfLe (h₁₂.trans h₂₃))) := by
  have hcomp : Subfunctor.homOfLe (h₁₂.trans h₂₃) =
      Subfunctor.homOfLe h₁₂ ≫ Subfunctor.homOfLe h₂₃ := by
    ext Δ x
    rfl
  rw [hcomp, freeAlgKanMap_comp]
  exact MorphismProperty.comp_mem _ _ _ hc₁₂ hc₂₃

lemma isIso_freeAlgKanMap_of_le_antisymm {B : SemiSSet.{u}} {S₁ S₂ : Subfunctor B}
    (h₁₂ : S₁ ≤ S₂) (h₂₁ : S₂ ≤ S₁) :
    IsIso (freeAlgKanMap (Subfunctor.homOfLe h₁₂)) := by
  refine ⟨⟨freeAlgKanMap (Subfunctor.homOfLe h₂₁), ?_, ?_⟩⟩
  · rw [← freeAlgKanMap_comp]
    have heq : Subfunctor.homOfLe h₁₂ ≫ Subfunctor.homOfLe h₂₁ = 𝟙 S₁.toFunctor := by
      ext Δ x
      rfl
    rw [heq, freeAlgKanMap_id]
  · rw [← freeAlgKanMap_comp]
    have heq : Subfunctor.homOfLe h₂₁ ≫ Subfunctor.homOfLe h₁₂ = 𝟙 S₂.toFunctor := by
      ext Δ x
      rfl
    rw [heq, freeAlgKanMap_id]

lemma cellularMaps_freeAlgKanMap_of_le_antisymm {B : SemiSSet.{u}} {S₁ S₂ : Subfunctor B}
    (h₁₂ : S₁ ≤ S₂) (h₂₁ : S₂ ≤ S₁) :
    AlgKan.cellularMaps (freeAlgKanMap (Subfunctor.homOfLe h₁₂)) := by
  have : IsIso (freeAlgKanMap (Subfunctor.homOfLe h₁₂)) :=
    isIso_freeAlgKanMap_of_le_antisymm h₁₂ h₂₁
  exact cellularMaps_of_isIso _

/-- The subfunctor of `Δ_N` generated by a single `m`-simplex `σ : [m] ⟶ [N]`. -/
def simplexSubfunctor {m N : ℕ}
    (σ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk N) :
    Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)) where
  obj Δ x := ∃ g : unop Δ ⟶ Henry.SemiSimplexCategory.mk m, x = ULift.up (g ≫ σ)
  map {Δ Δ'} f {x} := by
    rintro ⟨g, rfl⟩
    exact ⟨unop f ≫ g, by
      change ULift.up (unop f ≫ g ≫ σ) = ULift.up ((unop f ≫ g) ≫ σ)
      rw [Category.assoc]⟩

noncomputable def simplexSubfunctorInvApp {m N : ℕ}
    (σ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk N)
    (Δ : Henry.SemiSimplexCategoryᵒᵖ)
    (y : (simplexSubfunctor.{u} σ).toFunctor.obj Δ) :
    (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m)).obj Δ :=
  ULift.up (Classical.choose y.2)

lemma simplexSubfunctorInvApp_spec {m N : ℕ}
    (σ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk N)
    (Δ : Henry.SemiSimplexCategoryᵒᵖ)
    (y : (simplexSubfunctor.{u} σ).toFunctor.obj Δ) :
    ULift.up ((simplexSubfunctorInvApp.{u} σ Δ y).down ≫ σ) = y.1 :=
  (Classical.choose_spec y.2).symm

lemma simplexSubfunctorHomApp_injective {m N : ℕ}
    (σ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk N)
    {Δ : Henry.SemiSimplexCategoryᵒᵖ}
    {x₁ x₂ : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m)).obj Δ}
    (h : ULift.up (x₁.down ≫ σ) = ULift.up (x₂.down ≫ σ)) :
    x₁ = x₂ :=
  ULift.ext _ _ (cancel_mono_semiSimplex σ (ULift.up.inj h))

/-- The canonical isomorphism `Δ_m ≅ (simplexSubfunctor σ).toFunctor`. -/
noncomputable def simplexSubfunctorIso {m N : ℕ}
    (σ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk N) :
    SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m) ≅
      (simplexSubfunctor.{u} σ).toFunctor where
  hom :=
    { app Δ := ↾(fun x => ⟨ULift.up (ULift.down x ≫ σ), ⟨ULift.down x, rfl⟩⟩)
      naturality {Δ Δ'} f := by
        ext x
        apply Subtype.ext
        change ULift.up ((unop f ≫ ULift.down x) ≫ σ) = ULift.up (unop f ≫ ULift.down x ≫ σ)
        rw [Category.assoc] }
  inv :=
    { app Δ := ↾(simplexSubfunctorInvApp.{u} σ Δ)
      naturality {Δ Δ'} f := by
        ext y
        apply simplexSubfunctorHomApp_injective σ
        have h1 := simplexSubfunctorInvApp_spec σ Δ' ((simplexSubfunctor.{u} σ).toFunctor.map f y)
        have h2 := congrArg
          (fun z : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)).obj Δ =>
            ULift.up (unop f ≫ z.down))
          (simplexSubfunctorInvApp_spec σ Δ y)
        change ULift.up ((simplexSubfunctorInvApp.{u} σ Δ'
            ((simplexSubfunctor.{u} σ).toFunctor.map f y)).down ≫ σ) =
          ULift.up ((unop f ≫ (simplexSubfunctorInvApp.{u} σ Δ y).down) ≫ σ)
        rw [h1, Category.assoc]
        exact h2.symm }
  hom_inv_id := by
    ext Δ x
    apply simplexSubfunctorHomApp_injective σ
    exact simplexSubfunctorInvApp_spec σ Δ ⟨ULift.up (x.down ≫ σ), ⟨x.down, rfl⟩⟩
  inv_hom_id := by
    ext Δ y
    apply Subtype.ext
    exact simplexSubfunctorInvApp_spec σ Δ y

/-- Boundary attachment map `(∂Δ_m).toFunctor ⟶ S.toFunctor` when all proper faces of `σ` lie
in `S`. -/
@[simps]
def simplexBoundaryToSubfunctor {m N : ℕ}
    {S : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N))}
    (σ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk N)
    (hσ_bd : ∀ ⦃Δ : Henry.SemiSimplexCategoryᵒᵖ⦄ (g : unop Δ ⟶ Henry.SemiSimplexCategory.mk m),
      (unop Δ).obj.len < m → ULift.up (g ≫ σ) ∈ S.obj Δ) :
    (SemiSSet.boundary.{u} m).toFunctor ⟶ S.toFunctor where
  app Δ := ↾(fun x =>
    ⟨ULift.up (ULift.down x.1 ≫ σ), hσ_bd (ULift.down x.1) ((mem_boundary_iff x.1).mp x.2)⟩)
  naturality {Δ Δ'} f := by
    ext x
    apply Subtype.ext
    change ULift.up ((unop f ≫ ULift.down x.1) ≫ σ) = ULift.up (unop f ≫ ULift.down x.1 ≫ σ)
    rw [Category.assoc]

/-- Adding a single `m`-simplex `σ` not in `S` whose proper faces lie in `S` induces a single cell
attachment on `freeAlgKan`. -/
theorem isCellAttachment_freeAlgKanMap_sup_simplexSubfunctor {m N : ℕ}
    (S : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)))
    (σ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk N)
    (hσ_not_mem : ULift.up σ ∉ S.obj (op (Henry.SemiSimplexCategory.mk m)))
    (hσ_bd : ∀ ⦃Δ : Henry.SemiSimplexCategoryᵒᵖ⦄ (g : unop Δ ⟶ Henry.SemiSimplexCategory.mk m),
      (unop Δ).obj.len < m → ULift.up (g ≫ σ) ∈ S.obj Δ) :
    AlgKan.IsCellAttachment
      (freeAlgKanMap (Subfunctor.homOfLe (le_sup_left : S ≤ S ⊔ simplexSubfunctor.{u} σ))) := by
  let j := freeAlgKanMap (Subfunctor.homOfLe (le_sup_left : S ≤ S ⊔ simplexSubfunctor.{u} σ))
  let a₀ : (SemiSSet.boundary.{u} m).toFunctor ⟶ S.toFunctor :=
    simplexBoundaryToSubfunctor σ hσ_bd
  let y₀ : SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m) ⟶
      (S ⊔ simplexSubfunctor.{u} σ).toFunctor :=
    (simplexSubfunctorIso.{u} σ).hom ≫
      Subfunctor.homOfLe (le_sup_right : simplexSubfunctor.{u} σ ≤ S ⊔ simplexSubfunctor.{u} σ)
  refine ⟨m, a₀ ≫ freeAlgKanUnit S.toFunctor,
    y₀ ≫ freeAlgKanUnit (S ⊔ simplexSubfunctor.{u} σ).toFunctor, ?_, ?_⟩
  · have hcomm₀ : (SemiSSet.boundary.{u} m).ι ≫ y₀ =
        a₀ ≫ Subfunctor.homOfLe (le_sup_left : S ≤ S ⊔ simplexSubfunctor.{u} σ) := by
      ext Δ x
      rfl
    calc (SemiSSet.boundary.{u} m).ι ≫ y₀ ≫ freeAlgKanUnit (S ⊔ simplexSubfunctor.{u} σ).toFunctor
      _ = ((SemiSSet.boundary.{u} m).ι ≫ y₀) ≫
            freeAlgKanUnit (S ⊔ simplexSubfunctor.{u} σ).toFunctor :=
          (Category.assoc _ _ _).symm
      _ = (a₀ ≫ Subfunctor.homOfLe (le_sup_left : S ≤ S ⊔ simplexSubfunctor.{u} σ)) ≫
            freeAlgKanUnit (S ⊔ simplexSubfunctor.{u} σ).toFunctor := by rw [hcomm₀]
      _ = a₀ ≫ Subfunctor.homOfLe (le_sup_left : S ≤ S ⊔ simplexSubfunctor.{u} σ) ≫
            freeAlgKanUnit (S ⊔ simplexSubfunctor.{u} σ).toFunctor := Category.assoc _ _ _
      _ = a₀ ≫ freeAlgKanUnit S.toFunctor ≫ j.hom := by
          rw [← freeAlgKanUnit_comp_freeAlgKanMap]
      _ = (a₀ ≫ freeAlgKanUnit S.toFunctor) ≫ j.hom := (Category.assoc _ _ _).symm
  · intro Z g z hz
    let u₁ : S.toFunctor ⟶ Z.X := freeAlgKanUnit S.toFunctor ≫ g.hom
    let u₂ : (simplexSubfunctor.{u} σ).toFunctor ⟶ Z.X :=
      (simplexSubfunctorIso.{u} σ).inv ≫ z
    have hu :
        Subfunctor.homOfLe (inf_le_left : S ⊓ simplexSubfunctor.{u} σ ≤ S) ≫ u₁ =
          Subfunctor.homOfLe
            (inf_le_right : S ⊓ simplexSubfunctor.{u} σ ≤ simplexSubfunctor.{u} σ) ≫ u₂ := by
      ext Δ ⟨x, hxS, hxσ⟩
      let g₀ : unop Δ ⟶ Henry.SemiSimplexCategory.mk m := Classical.choose hxσ
      have hg₀ : x = ULift.up (g₀ ≫ σ) := Classical.choose_spec hxσ
      have hbd_g₀ : ULift.up g₀ ∈ (SemiSSet.boundary.{u} m).obj Δ := by
        by_contra hnot
        obtain ⟨hΔ, hg₀_eq⟩ := eq_mk_and_eq_id_of_not_mem_boundary hnot
        cases Δ with | op Δ₀ =>
        dsimp at hΔ
        subst hΔ
        dsimp at hg₀_eq
        have hx_eq : x = ULift.up σ := by
          rw [hg₀, hg₀_eq, Category.id_comp]
        rw [hx_eq] at hxS
        exact hσ_not_mem hxS
      have hz_app := ConcreteCategory.congr_hom (congr_app hz Δ) ⟨ULift.up g₀, hbd_g₀⟩
      change z.app Δ (ULift.up g₀) = u₁.app Δ ⟨ULift.up (g₀ ≫ σ), _⟩ at hz_app
      have hinv_g₀ : simplexSubfunctorInvApp.{u} σ Δ ⟨x, hxσ⟩ = ULift.up g₀ := by
        apply simplexSubfunctorHomApp_injective σ
        rw [simplexSubfunctorInvApp_spec]
        exact hg₀
      change u₁.app Δ ⟨x, hxS⟩ = z.app Δ (simplexSubfunctorInvApp.{u} σ Δ ⟨x, hxσ⟩)
      rw [hinv_g₀, hz_app]
      congr 1
      exact Subtype.ext hg₀
    let u : (S ⊔ simplexSubfunctor.{u} σ).toFunctor ⟶ Z.X :=
      subfunctorSupDesc S (simplexSubfunctor.{u} σ) u₁ u₂ hu
    obtain ⟨g', hg', hg'uniq⟩ :=
      freeAlgKan_isFreeOn (S ⊔ simplexSubfunctor.{u} σ).toFunctor Z u
    refine ⟨g', ⟨?_, ?_⟩, ?_⟩
    · apply freeAlgKan_hom_ext
      calc freeAlgKanUnit S.toFunctor ≫ (j ≫ g').hom
        _ = (freeAlgKanUnit S.toFunctor ≫ j.hom) ≫ g'.hom := (Category.assoc _ _ _).symm
        _ = (Subfunctor.homOfLe (le_sup_left : S ≤ S ⊔ simplexSubfunctor.{u} σ) ≫
              freeAlgKanUnit (S ⊔ simplexSubfunctor.{u} σ).toFunctor) ≫ g'.hom := by
            rw [freeAlgKanUnit_comp_freeAlgKanMap]
        _ = Subfunctor.homOfLe (le_sup_left : S ≤ S ⊔ simplexSubfunctor.{u} σ) ≫
              (freeAlgKanUnit (S ⊔ simplexSubfunctor.{u} σ).toFunctor ≫ g'.hom) :=
            Category.assoc _ _ _
        _ = Subfunctor.homOfLe (le_sup_left : S ≤ S ⊔ simplexSubfunctor.{u} σ) ≫ u := by
            rw [hg']
        _ = u₁ := homOfLe_left_comp_subfunctorSupDesc S (simplexSubfunctor.{u} σ) u₁ u₂ hu
    · calc (y₀ ≫ freeAlgKanUnit (S ⊔ simplexSubfunctor.{u} σ).toFunctor) ≫ g'.hom
        _ = y₀ ≫ (freeAlgKanUnit (S ⊔ simplexSubfunctor.{u} σ).toFunctor ≫ g'.hom) :=
            Category.assoc _ _ _
        _ = y₀ ≫ u := by rw [hg']
        _ = (simplexSubfunctorIso.{u} σ).hom ≫
              (Subfunctor.homOfLe
                (le_sup_right : simplexSubfunctor.{u} σ ≤ S ⊔ simplexSubfunctor.{u} σ) ≫ u) :=
            Category.assoc _ _ _
        _ = (simplexSubfunctorIso.{u} σ).hom ≫ u₂ := by
            rw [homOfLe_right_comp_subfunctorSupDesc]
        _ = z := Iso.hom_inv_id_assoc (simplexSubfunctorIso.{u} σ) z
    · rintro g'' ⟨hg''l, hg''r⟩
      apply hg'uniq
      apply subfunctorSup_hom_ext S (simplexSubfunctor.{u} σ)
      · rw [homOfLe_left_comp_subfunctorSupDesc]
        calc Subfunctor.homOfLe (le_sup_left : S ≤ S ⊔ simplexSubfunctor.{u} σ) ≫
              (freeAlgKanUnit (S ⊔ simplexSubfunctor.{u} σ).toFunctor ≫ g''.hom)
          _ = (Subfunctor.homOfLe (le_sup_left : S ≤ S ⊔ simplexSubfunctor.{u} σ) ≫
                freeAlgKanUnit (S ⊔ simplexSubfunctor.{u} σ).toFunctor) ≫ g''.hom :=
              (Category.assoc _ _ _).symm
          _ = (freeAlgKanUnit S.toFunctor ≫ j.hom) ≫ g''.hom := by
              rw [freeAlgKanUnit_comp_freeAlgKanMap]
          _ = freeAlgKanUnit S.toFunctor ≫ (j ≫ g'').hom := Category.assoc _ _ _
          _ = u₁ := by rw [hg''l]
      · rw [homOfLe_right_comp_subfunctorSupDesc]
        rw [← cancel_epi (simplexSubfunctorIso.{u} σ).hom]
        calc (simplexSubfunctorIso.{u} σ).hom ≫
              Subfunctor.homOfLe
                (le_sup_right : simplexSubfunctor.{u} σ ≤ S ⊔ simplexSubfunctor.{u} σ) ≫
              (freeAlgKanUnit (S ⊔ simplexSubfunctor.{u} σ).toFunctor ≫ g''.hom)
          _ = (y₀ ≫ freeAlgKanUnit (S ⊔ simplexSubfunctor.{u} σ).toFunctor) ≫ g''.hom := by
              simp only [y₀, Category.assoc]
          _ = z := hg''r
          _ = (simplexSubfunctorIso.{u} σ).hom ≫ u₂ :=
              (Iso.hom_inv_id_assoc (simplexSubfunctorIso.{u} σ) z).symm

/-!
## Skeletal filtration of subfunctors of `Δ_N`
-/

/-- The `d`-skeleton of `T` relative to `S`. -/
def skelSubfunctor {N : ℕ}
    (S T : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N))) (d : ℕ) :
    Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)) where
  obj Δ x := x ∈ S.obj Δ ∨ (x ∈ T.obj Δ ∧ (unop Δ).obj.len < d)
  map {Δ Δ'} f {x} hx := by
    rcases hx with hxS | ⟨hxT, hlt⟩
    · exact Or.inl (S.map f hxS)
    · exact Or.inr ⟨T.map f hxT, lt_of_le_of_lt (len_le_of_hom (unop f)) hlt⟩

/-- Subfunctor obtained from `S'` by adding the `m`-simplices in `F`. -/
def addCellsAt {N : ℕ} (m : ℕ)
    (S' : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)))
    (F : Finset (Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk N)) :
    Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)) where
  obj Δ x :=
    x ∈ S'.obj Δ ∨ ∃ σ ∈ F, x ∈ (simplexSubfunctor.{u} σ).obj Δ
  map {Δ Δ'} f {x} hx := by
    rcases hx with hxS | ⟨σ, hσF, hxσ⟩
    · exact Or.inl (S'.map f hxS)
    · exact Or.inr ⟨σ, hσF, (simplexSubfunctor.{u} σ).map f hxσ⟩

lemma le_addCellsAt_empty {N : ℕ} (m : ℕ)
    (S' : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N))) :
    S' ≤ addCellsAt m S' ∅ :=
  fun _ _ hx => Or.inl hx

lemma addCellsAt_empty_le {N : ℕ} (m : ℕ)
    (S' : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N))) :
    addCellsAt m S' ∅ ≤ S' := by
  intro Δ x hx
  rcases hx with hxS | ⟨σ, hσ, _⟩
  · exact hxS
  · simp at hσ

lemma addCellsAt_mono {N : ℕ} (m : ℕ)
    (S' : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)))
    {F₁ F₂ : Finset (Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk N)}
    (hF : F₁ ⊆ F₂) :
    addCellsAt m S' F₁ ≤ addCellsAt m S' F₂ := by
  intro Δ x hx
  rcases hx with hxS | ⟨σ, hσ, hxσ⟩
  · exact Or.inl hxS
  · exact Or.inr ⟨σ, hF hσ, hxσ⟩

lemma addCellsAt_insert_le_sup {N : ℕ} (m : ℕ)
    (S' : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)))
    (F : Finset (Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk N))
    (σ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk N) :
    addCellsAt m S' (insert σ F) ≤ addCellsAt m S' F ⊔ simplexSubfunctor.{u} σ := by
  intro Δ x hx
  rcases hx with hxS | ⟨τ, hτ, hxτ⟩
  · exact Or.inl (Or.inl hxS)
  · rcases Finset.mem_insert.mp hτ with rfl | hτF
    · exact Or.inr hxτ
    · exact Or.inl (Or.inr ⟨τ, hτF, hxτ⟩)

lemma sup_le_addCellsAt_insert {N : ℕ} (m : ℕ)
    (S' : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)))
    (F : Finset (Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk N))
    (σ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk N) :
    addCellsAt m S' F ⊔ simplexSubfunctor.{u} σ ≤ addCellsAt m S' (insert σ F) := by
  intro Δ x hx
  rcases hx with (hxS | ⟨τ, hτF, hxτ⟩) | hxσ
  · exact Or.inl hxS
  · exact Or.inr ⟨τ, Finset.mem_insert_of_mem hτF, hxτ⟩
  · exact Or.inr ⟨σ, Finset.mem_insert_self σ F, hxσ⟩

lemma cellularMaps_addCellsAt {N : ℕ} (m : ℕ)
    (S' : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)))
    (F : Finset (Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk N))
    (hF_bd : ∀ σ ∈ F, ∀ ⦃Δ : Henry.SemiSimplexCategoryᵒᵖ⦄ (g : unop Δ ⟶ Henry.SemiSimplexCategory.mk m),
      (unop Δ).obj.len < m → ULift.up (g ≫ σ) ∈ S'.obj Δ) :
    AlgKan.cellularMaps (freeAlgKanMap (Subfunctor.homOfLe (le_addCellsAt_empty m S' |>.trans
      (addCellsAt_mono m S' (Finset.empty_subset F))))) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    exact cellularMaps_freeAlgKanMap_of_le_antisymm _ (addCellsAt_empty_le m S')
  | @insert σ F hσnot ih =>
    have hF_bd' : ∀ τ ∈ F, ∀ ⦃Δ : Henry.SemiSimplexCategoryᵒᵖ⦄ (g : unop Δ ⟶ Henry.SemiSimplexCategory.mk m),
        (unop Δ).obj.len < m → ULift.up (g ≫ τ) ∈ S'.obj Δ :=
      fun τ hτ => hF_bd τ (Finset.mem_insert_of_mem hτ)
    have hc₁ := ih hF_bd'
    have hstep : AlgKan.cellularMaps
        (freeAlgKanMap (Subfunctor.homOfLe
          (addCellsAt_mono m S' (Finset.subset_insert σ F)))) := by
      by_cases hσ_mem : ULift.up σ ∈ (addCellsAt m S' F).obj (op (Henry.SemiSimplexCategory.mk m))
      · refine cellularMaps_freeAlgKanMap_of_le_antisymm _ ?_
        intro Δ x hx
        rcases addCellsAt_insert_le_sup m S' F σ Δ hx with hxF | ⟨g, rfl⟩
        · exact hxF
        · exact (addCellsAt m S' F).map g.op hσ_mem
      · have hσ_bd' : ∀ ⦃Δ : Henry.SemiSimplexCategoryᵒᵖ⦄ (g : unop Δ ⟶ Henry.SemiSimplexCategory.mk m),
            (unop Δ).obj.len < m → ULift.up (g ≫ σ) ∈ (addCellsAt m S' F).obj Δ :=
          fun Δ g hlt => Or.inl (hF_bd σ (Finset.mem_insert_self σ F) g hlt)
        have hattach := isCellAttachment_freeAlgKanMap_sup_simplexSubfunctor
          (addCellsAt m S' F) σ hσ_mem hσ_bd'
        have hc_sup := cellularMaps_of_isCellAttachment hattach
        have hc_iso := cellularMaps_freeAlgKanMap_of_le_antisymm
          (sup_le_addCellsAt_insert m S' F σ) (addCellsAt_insert_le_sup m S' F σ)
        exact cellularMaps_freeAlgKanMap_trans
          (le_sup_left : addCellsAt m S' F ≤ addCellsAt m S' F ⊔ simplexSubfunctor.{u} σ)
          (sup_le_addCellsAt_insert m S' F σ) hc_sup hc_iso
    exact cellularMaps_freeAlgKanMap_trans _ _ hc₁ hstep

lemma skelSubfunctor_step_cellularMaps {N : ℕ}
    (S T : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N))) (m : ℕ) :
    AlgKan.cellularMaps
      (freeAlgKanMap (Subfunctor.homOfLe
        (show skelSubfunctor S T m ≤ skelSubfunctor S T (m + 1) from
          fun _ _ hx => hx.imp id (fun ⟨hxT, hlt⟩ => ⟨hxT, Nat.lt_succ_of_lt hlt⟩)))) := by
  classical
  let S_m := skelSubfunctor S T m
  let F : Finset (Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk N) :=
    Finset.univ.filter (fun σ => ULift.up σ ∈ T.obj (op (Henry.SemiSimplexCategory.mk m)))
  have hF_bd : ∀ σ ∈ F, ∀ ⦃Δ : Henry.SemiSimplexCategoryᵒᵖ⦄ (g : unop Δ ⟶ Henry.SemiSimplexCategory.mk m),
      (unop Δ).obj.len < m → ULift.up (g ≫ σ) ∈ S_m.obj Δ := by
    intro σ hσ Δ g hlt
    have hσT : ULift.up σ ∈ T.obj (op (Henry.SemiSimplexCategory.mk m)) :=
      (Finset.mem_filter.mp hσ).2
    exact Or.inr ⟨T.map g.op hσT, hlt⟩
  have hc_add := cellularMaps_addCellsAt m S_m F hF_bd
  have hle₁ : addCellsAt m S_m F ≤ skelSubfunctor S T (m + 1) := by
    intro Δ x hx
    rcases hx with (hxS | ⟨hxT, hlt⟩) | ⟨σ, hσ, g, rfl⟩
    · exact Or.inl hxS
    · exact Or.inr ⟨hxT, Nat.lt_succ_of_lt hlt⟩
    · have hσT : ULift.up σ ∈ T.obj (op (Henry.SemiSimplexCategory.mk m)) :=
        (Finset.mem_filter.mp hσ).2
      exact Or.inr ⟨T.map g.op hσT, Nat.lt_succ_of_le (len_le_of_hom g)⟩
  have hle₂ : skelSubfunctor S T (m + 1) ≤ addCellsAt m S_m F := by
    intro Δ x hx
    rcases hx with hxS | ⟨hxT, hlt⟩
    · exact Or.inl (Or.inl hxS)
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | heq_len
      · exact Or.inl (Or.inr ⟨hxT, hlt'⟩)
      · cases Δ with | op Δ₀ =>
        cases Δ₀ with | mk obj =>
        cases obj with | mk len =>
        dsimp at heq_len
        revert x hxT
        rw [heq_len]
        rintro ⟨(σ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk N)⟩ hxT
        refine Or.inr ⟨σ, Finset.mem_filter.mpr ⟨Finset.mem_univ σ, hxT⟩,
          𝟙 (Henry.SemiSimplexCategory.mk m), ?_⟩
        rw [Category.id_comp]
  exact cellularMaps_freeAlgKanMap_trans _ hle₁ hc_add
    (cellularMaps_freeAlgKanMap_of_le_antisymm hle₁ hle₂)

lemma skelSubfunctor_zero_le_cellularMaps {N : ℕ}
    (S T : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N))) :
    ∀ d : ℕ, AlgKan.cellularMaps
      (freeAlgKanMap (Subfunctor.homOfLe
        (show skelSubfunctor S T 0 ≤ skelSubfunctor S T d from
          fun _ _ hx => hx.imp id (fun ⟨_hxT, hlt⟩ => (Nat.not_lt_zero _ hlt).elim)))) := by
  intro d
  induction d with
  | zero =>
    exact cellularMaps_freeAlgKanMap_of_le_antisymm _ (le_refl _)
  | succ d ih =>
    exact cellularMaps_freeAlgKanMap_trans _ _ ih (skelSubfunctor_step_cellularMaps S T d)

/-- For any two subfunctors `S ≤ T` of `Δ_N`, `freeAlgKanMap (Subfunctor.homOfLe hST)` is in
`AlgKan.cellularMaps`. -/
theorem cellularMaps_freeAlgKanMap_of_le {N : ℕ}
    {S T : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N))}
    (hST : S ≤ T) :
    AlgKan.cellularMaps (freeAlgKanMap (Subfunctor.homOfLe hST)) := by
  have hle_zero₁ : S ≤ skelSubfunctor S T 0 := fun _ _ hx => Or.inl hx
  have hle_zero₂ : skelSubfunctor S T 0 ≤ S := by
    intro Δ x hx
    rcases hx with hxS | ⟨_, hlt⟩
    · exact hxS
    · exact (Nat.not_lt_zero _ hlt).elim
  have hle_top₁ : skelSubfunctor S T (N + 1) ≤ T := by
    intro Δ x hx
    rcases hx with hxS | ⟨hxT, _⟩
    · exact hST Δ hxS
    · exact hxT
  have hle_top₂ : T ≤ skelSubfunctor S T (N + 1) := by
    intro Δ x hxT
    exact Or.inr ⟨hxT, Nat.lt_succ_of_le (len_le_of_hom (ULift.down x))⟩
  have hc₀ := cellularMaps_freeAlgKanMap_of_le_antisymm hle_zero₁ hle_zero₂
  have hc₁ := skelSubfunctor_zero_le_cellularMaps S T (N + 1)
  have hc₂ := cellularMaps_freeAlgKanMap_of_le_antisymm hle_top₁ hle_top₂
  exact cellularMaps_freeAlgKanMap_trans hle_zero₁ _ hc₀
    (cellularMaps_freeAlgKanMap_trans _ hle_top₁ hc₁ hc₂)

/-- The free algebraic Kan complex on `⊥ : Subfunctor B` is initial, hence finitely cellular. -/
lemma isFinitelyCellular_freeAlgKan_bot (B : SemiSSet.{u}) :
    AlgKan.IsFinitelyCellular (freeAlgKan (⊥ : Subfunctor B).toFunctor) := by
  have hInit : IsInitial (freeAlgKan (⊥ : Subfunctor B).toFunctor) :=
    IsInitial.ofUniqueHom
      (fun Z => (freeAlgKan_isFreeOn (⊥ : Subfunctor B).toFunctor Z
        { app _ := ↾(fun x => x.2.elim)
          naturality _ _ _ := by ext x; exact x.2.elim }).choose)
      (fun Z g => by
        apply freeAlgKan_hom_ext
        ext _ x
        exact x.2.elim)
  exact AlgKan.IsFinitelyCellular.initial _ ⟨hInit⟩

/-- For any subfunctor `S` of `Δ_N`, `freeAlgKan S.toFunctor` is finitely cellular. -/
theorem isFinitelyCellular_freeAlgKan_subfunctor {N : ℕ}
    (S : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N))) :
    AlgKan.IsFinitelyCellular (freeAlgKan S.toFunctor) :=
  isFinitelyCellular_of_cellularMaps
    (cellularMaps_freeAlgKanMap_of_le (bot_le : ⊥ ≤ S))
    (isFinitelyCellular_freeAlgKan_bot _)

/-- The canonical isomorphism `(⊤ : Subfunctor B).toFunctor ≅ B`. -/
@[simps]
def topSubfunctorIso (B : SemiSSet.{u}) : (⊤ : Subfunctor B).toFunctor ≅ B where
  hom := (⊤ : Subfunctor B).ι
  inv :=
    { app _ := ↾(fun x => ⟨x, trivial⟩)
      naturality _ _ _ := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

lemma isIso_freeAlgKanMap_of_isIso {A B : SemiSSet.{u}} (f : A ⟶ B) [IsIso f] :
    IsIso (freeAlgKanMap f) := by
  refine ⟨⟨freeAlgKanMap (inv f), ?_, ?_⟩⟩
  · rw [← freeAlgKanMap_comp, IsIso.hom_inv_id, freeAlgKanMap_id]
  · rw [← freeAlgKanMap_comp, IsIso.inv_hom_id, freeAlgKanMap_id]

/-- For every `N : ℕ`, `freeAlgKan (Δ_N)` is finitely cellular. -/
theorem isFinitelyCellular_freeAlgKan_stdSimplex (N : ℕ) :
    AlgKan.IsFinitelyCellular
      (freeAlgKan (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N))) := by
  let B := SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)
  have : IsIso (freeAlgKanMap (topSubfunctorIso B).hom) :=
    isIso_freeAlgKanMap_of_isIso (topSubfunctorIso B).hom
  exact isFinitelyCellular_of_isIso (freeAlgKanMap (topSubfunctorIso B).hom)
    (isFinitelyCellular_freeAlgKan_subfunctor (⊤ : Subfunctor B))

/-!
## Objects `stdSimplexCDelta`, `boundaryCDelta`, `hornCDelta` and the boundary-horn pushout square
-/

/-- The free `n`-simplex in `CDelta`. -/
noncomputable def stdSimplexCDelta (n : ℕ) : CDelta.{u} :=
  ⟨freeAlgKan (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk n)),
    isFinitelyCellular_freeAlgKan_stdSimplex n⟩

/-- The free boundary `∂Δ_n` in `CDelta`. -/
noncomputable def boundaryCDelta (n : ℕ) : CDelta.{u} :=
  ⟨freeAlgKan (SemiSSet.boundary.{u} n).toFunctor,
    isFinitelyCellular_freeAlgKan_subfunctor (SemiSSet.boundary.{u} n)⟩

/-- The free horn `Λ^{n+1}_k` in `CDelta`. -/
noncomputable def hornCDelta (n : ℕ) (k : Fin (n + 2)) : CDelta.{u} :=
  ⟨freeAlgKan (SemiSSet.horn.{u} (n + 1) k).toFunctor,
    isFinitelyCellular_freeAlgKan_subfunctor (SemiSSet.horn.{u} (n + 1) k)⟩

/-- The boundary inclusion `∂Δ_n ⟶ Δ_n` in `CDelta`. -/
noncomputable def boundaryCDeltaInclusion (n : ℕ) :
    boundaryCDelta.{u} n ⟶ stdSimplexCDelta.{u} n :=
  ObjectProperty.homMk (freeAlgKanMap (SemiSSet.boundary.{u} n).ι)

lemma boundaryCDeltaInclusion_cofibration (n : ℕ) :
    cofibrations CDelta.{u} (boundaryCDeltaInclusion.{u} n) := by
  let B := SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk n)
  have heq : (SemiSSet.boundary.{u} n).ι =
      Subfunctor.homOfLe (le_top : SemiSSet.boundary.{u} n ≤ ⊤) ≫ (topSubfunctorIso B).hom :=
    rfl
  change AlgKan.cellularMaps (freeAlgKanMap (SemiSSet.boundary.{u} n).ι)
  rw [heq, freeAlgKanMap_comp]
  have : IsIso (freeAlgKanMap (topSubfunctorIso B).hom) :=
    isIso_freeAlgKanMap_of_isIso (topSubfunctorIso B).hom
  exact MorphismProperty.comp_mem _ _ _
    (cellularMaps_freeAlgKanMap_of_le le_top)
    (cellularMaps_of_isIso _)

/-- The `(n+1)`-th face map `[n] ⟶ [n + 1]` in `Henry.SemiSimplexCategory`. -/
def faceLast (n : ℕ) : Henry.SemiSimplexCategory.mk n ⟶ Henry.SemiSimplexCategory.mk (n + 1) :=
  ⟨SimplexCategory.δ (Fin.last (n + 1)), inferInstance⟩

@[simp]
lemma faceLast_toOrderHom_apply (n : ℕ) (i : Fin (n + 1)) :
    (faceLast n).hom.toOrderHom i = i.castSucc :=
  congrFun Fin.succAbove_last i

lemma simplexSubfunctor_faceLast_mem_iff (n : ℕ) {Δ : Henry.SemiSimplexCategoryᵒᵖ}
    (x : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk (n + 1))).obj Δ) :
    x ∈ (simplexSubfunctor.{u} (faceLast n)).obj Δ ↔
      Fin.last (n + 1) ∉ Set.range (ULift.down x).hom.toOrderHom := by
  constructor
  · rintro ⟨g, rfl⟩ ⟨k, hk⟩
    change (faceLast n).hom.toOrderHom (g.hom.toOrderHom k) = Fin.last (n + 1) at hk
    rw [faceLast_toOrderHom_apply] at hk
    exact Fin.castSucc_ne_last (g.hom.toOrderHom k) hk
  · intro hnot
    have hlt : ∀ k : Fin ((unop Δ).obj.len + 1),
        ((ULift.down x).hom.toOrderHom k).1 < n + 1 := by
      intro k
      have hne : (ULift.down x).hom.toOrderHom k ≠ Fin.last (n + 1) :=
        fun h => hnot ⟨k, h⟩
      exact Fin.val_lt_last hne
    let φ : Fin ((unop Δ).obj.len + 1) →o Fin (n + 1) :=
      { toFun := fun k => ⟨((ULift.down x).hom.toOrderHom k).1, hlt k⟩
        monotone' := fun a b hab => Fin.le_def.mpr ((ULift.down x).hom.toOrderHom.monotone hab) }
    have hinj : Function.Injective φ := by
      intro a b hab
      have hab' : (ULift.down x).hom.toOrderHom a = (ULift.down x).hom.toOrderHom b :=
        Fin.ext (congrArg (@Fin.val (n + 1)) hab)
      exact SimplexCategory.mono_iff_injective.mp (ULift.down x).property hab'
    let g : unop Δ ⟶ Henry.SemiSimplexCategory.mk n :=
      ⟨SimplexCategory.Hom.mk φ, SimplexCategory.mono_iff_injective.mpr hinj⟩
    refine ⟨g, ?_⟩
    apply congrArg ULift.up
    apply Henry.SemiSimplexCategory.incl.map_injective
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext k
    change (ULift.down x).hom.toOrderHom k = (faceLast n).hom.toOrderHom (φ k)
    rw [faceLast_toOrderHom_apply]
    rfl

lemma sup_simplexSubfunctor_faceLast_horn_le_boundary (n : ℕ) :
    simplexSubfunctor.{u} (faceLast n) ⊔ SemiSSet.horn.{u} (n + 1) (Fin.last (n + 1)) ≤
      SemiSSet.boundary.{u} (n + 1) := by
  intro Δ x hx
  rcases hx with hxFace | ⟨j, _, hj⟩
  · exact ⟨Fin.last (n + 1), (simplexSubfunctor_faceLast_mem_iff n x).mp hxFace⟩
  · exact ⟨j, hj⟩

lemma boundary_le_sup_simplexSubfunctor_faceLast_horn (n : ℕ) :
    SemiSSet.boundary.{u} (n + 1) ≤
      simplexSubfunctor.{u} (faceLast n) ⊔ SemiSSet.horn.{u} (n + 1) (Fin.last (n + 1)) := by
  intro Δ x ⟨j, hj⟩
  by_cases hjl : j = Fin.last (n + 1)
  · subst hjl
    exact Or.inl ((simplexSubfunctor_faceLast_mem_iff n x).mpr hj)
  · exact Or.inr ⟨j, hjl, hj⟩

lemma mem_inf_simplexSubfunctor_faceLast_horn_iff (n : ℕ) {Δ : Henry.SemiSimplexCategoryᵒᵖ}
    (x : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk n)).obj Δ) :
    ((simplexSubfunctorIso.{u} (faceLast n)).hom.app Δ x).1 ∈
      (simplexSubfunctor.{u} (faceLast n) ⊓ SemiSSet.horn.{u} (n + 1) (Fin.last (n + 1))).obj Δ ↔
      x ∈ (SemiSSet.boundary.{u} n).obj Δ := by
  constructor
  · rintro ⟨_, j, hjl, hj⟩
    have hjlt : j.1 < n + 1 := Fin.val_lt_last hjl
    refine ⟨⟨j.1, hjlt⟩, ?_⟩
    rintro ⟨k, hk⟩
    apply hj
    refine ⟨k, ?_⟩
    change (faceLast n).hom.toOrderHom ((ULift.down x).hom.toOrderHom k) = j
    rw [faceLast_toOrderHom_apply]
    exact Fin.ext (congrArg (@Fin.val (n + 1)) hk)
  · rintro ⟨i, hi⟩
    refine ⟨⟨ULift.down x, rfl⟩, i.castSucc, Fin.castSucc_ne_last i, ?_⟩
    rintro ⟨k, hk⟩
    apply hi
    refine ⟨k, ?_⟩
    change (faceLast n).hom.toOrderHom ((ULift.down x).hom.toOrderHom k) = i.castSucc at hk
    rw [faceLast_toOrderHom_apply] at hk
    exact Fin.castSucc_inj.mp hk

/-- The canonical isomorphism `(∂Δ_n).toFunctor ≅ (simplexSubfunctor (faceLast n) ⊓ Λ^{n+1}_{n+1}).toFunctor`. -/
noncomputable def boundaryIsoInfFaceLastHorn (n : ℕ) :
    (SemiSSet.boundary.{u} n).toFunctor ≅
      (simplexSubfunctor.{u} (faceLast n) ⊓
        SemiSSet.horn.{u} (n + 1) (Fin.last (n + 1))).toFunctor where
  hom :=
    { app Δ := ↾(fun x =>
        ⟨((simplexSubfunctorIso.{u} (faceLast n)).hom.app Δ x.1).1,
          (mem_inf_simplexSubfunctor_faceLast_horn_iff n x.1).mpr x.2⟩)
      naturality {Δ Δ'} f := by
        ext x
        apply Subtype.ext
        change ULift.up ((unop f ≫ ULift.down x.1) ≫ faceLast n) =
          ULift.up (unop f ≫ ULift.down x.1 ≫ faceLast n)
        rw [Category.assoc] }
  inv :=
    { app Δ := ↾(fun y =>
        ⟨simplexSubfunctorInvApp.{u} (faceLast n) Δ ⟨y.1, y.2.1⟩, by
          refine (mem_inf_simplexSubfunctor_faceLast_horn_iff n _).mp ?_
          change ULift.up ((simplexSubfunctorInvApp.{u} (faceLast n) Δ ⟨y.1, y.2.1⟩).down ≫
              faceLast n) ∈
            (simplexSubfunctor.{u} (faceLast n) ⊓
              SemiSSet.horn.{u} (n + 1) (Fin.last (n + 1))).obj Δ
          rw [simplexSubfunctorInvApp_spec]
          exact y.2⟩)
      naturality {Δ Δ'} f := by
        ext y
        apply Subtype.ext
        exact ConcreteCategory.congr_hom
          ((simplexSubfunctorIso.{u} (faceLast n)).inv.naturality f) ⟨y.1, y.2.1⟩ }
  hom_inv_id := by
    ext Δ x
    apply Subtype.ext
    apply simplexSubfunctorHomApp_injective (faceLast n)
    exact simplexSubfunctorInvApp_spec (faceLast n) Δ
      ⟨ULift.up (x.1.down ≫ faceLast n), ⟨x.1.down, rfl⟩⟩
  inv_hom_id := by
    ext Δ y
    apply Subtype.ext
    exact simplexSubfunctorInvApp_spec (faceLast n) Δ ⟨y.1, y.2.1⟩

/-- Inclusion `∂Δ_n ⟶ Λ^{n+1}_{n+1}` in `CDelta`. -/
noncomputable def boundaryToHornLast (n : ℕ) :
    boundaryCDelta.{u} n ⟶ hornCDelta.{u} n (Fin.last (n + 1)) :=
  ObjectProperty.homMk (freeAlgKanMap
    ((boundaryIsoInfFaceLastHorn.{u} n).hom ≫
      Subfunctor.homOfLe
        (inf_le_right :
          simplexSubfunctor.{u} (faceLast n) ⊓
            SemiSSet.horn.{u} (n + 1) (Fin.last (n + 1)) ≤
            SemiSSet.horn.{u} (n + 1) (Fin.last (n + 1)))))

/-- Inclusion `Δ_n ⟶ ∂Δ_{n+1}` in `CDelta` via `faceLast n`. -/
noncomputable def stdSimplexToBoundarySucc (n : ℕ) :
    stdSimplexCDelta.{u} n ⟶ boundaryCDelta.{u} (n + 1) :=
  ObjectProperty.homMk (freeAlgKanMap
    ((simplexSubfunctorIso.{u} (faceLast n)).hom ≫
      Subfunctor.homOfLe
        ((le_sup_left :
          simplexSubfunctor.{u} (faceLast n) ≤
            simplexSubfunctor.{u} (faceLast n) ⊔
              SemiSSet.horn.{u} (n + 1) (Fin.last (n + 1))).trans
          (sup_simplexSubfunctor_faceLast_horn_le_boundary n))))

/-- Inclusion `Λ^{n+1}_{n+1} ⟶ ∂Δ_{n+1}` in `CDelta`. -/
noncomputable def hornLastToBoundarySucc (n : ℕ) :
    hornCDelta.{u} n (Fin.last (n + 1)) ⟶ boundaryCDelta.{u} (n + 1) :=
  ObjectProperty.homMk (freeAlgKanMap
    (Subfunctor.homOfLe
      ((le_sup_right :
        SemiSSet.horn.{u} (n + 1) (Fin.last (n + 1)) ≤
          simplexSubfunctor.{u} (faceLast n) ⊔
            SemiSSet.horn.{u} (n + 1) (Fin.last (n + 1))).trans
        (sup_simplexSubfunctor_faceLast_horn_le_boundary n))))

lemma boundaryToHornLast_cofibration (n : ℕ) :
    cofibrations CDelta.{u} (boundaryToHornLast.{u} n) := by
  change AlgKan.cellularMaps (freeAlgKanMap _)
  rw [freeAlgKanMap_comp]
  have : IsIso (freeAlgKanMap (boundaryIsoInfFaceLastHorn.{u} n).hom) :=
    isIso_freeAlgKanMap_of_isIso (boundaryIsoInfFaceLastHorn.{u} n).hom
  exact MorphismProperty.comp_mem _ _ _
    (cellularMaps_of_isIso _)
    (cellularMaps_freeAlgKanMap_of_le inf_le_right)

lemma stdSimplexToBoundarySucc_cofibration (n : ℕ) :
    cofibrations CDelta.{u} (stdSimplexToBoundarySucc.{u} n) := by
  change AlgKan.cellularMaps (freeAlgKanMap _)
  rw [freeAlgKanMap_comp]
  have : IsIso (freeAlgKanMap (simplexSubfunctorIso.{u} (faceLast n)).hom) :=
    isIso_freeAlgKanMap_of_isIso (simplexSubfunctorIso.{u} (faceLast n)).hom
  exact MorphismProperty.comp_mem _ _ _
    (cellularMaps_of_isIso _)
    (cellularMaps_freeAlgKanMap_of_le _)

lemma hornLastToBoundarySucc_cofibration (n : ℕ) :
    cofibrations CDelta.{u} (hornLastToBoundarySucc.{u} n) :=
  cellularMaps_freeAlgKanMap_of_le _

/-- In `CDelta`, `∂Δ_{n+1}` is the pushout of `Δ_n` and `Λ^{n+1}_{n+1}` over `∂Δ_n`. -/
theorem isPushout_boundary_horn (n : ℕ) :
    IsPushout
      (boundaryCDeltaInclusion.{u} n)
      (boundaryToHornLast.{u} n)
      (stdSimplexToBoundarySucc.{u} n)
      (hornLastToBoundarySucc.{u} n) := by
  apply isPushout_cDelta_of_algKan
  dsimp [boundaryCDelta, stdSimplexCDelta, hornCDelta, boundaryCDeltaInclusion,
    boundaryToHornLast, stdSimplexToBoundarySucc, hornLastToBoundarySucc]
  let S₁ := simplexSubfunctor.{u} (faceLast n)
  let S₂ := SemiSSet.horn.{u} (n + 1) (Fin.last (n + 1))
  have hpo_sup := isPushout_freeAlgKan_sup S₁ S₂
  let e_tl : freeAlgKan (SemiSSet.boundary.{u} n).toFunctor ≅ freeAlgKan (S₁ ⊓ S₂).toFunctor :=
    { hom := freeAlgKanMap (boundaryIsoInfFaceLastHorn.{u} n).hom
      inv := freeAlgKanMap (boundaryIsoInfFaceLastHorn.{u} n).inv
      hom_inv_id := by rw [← freeAlgKanMap_comp, Iso.hom_inv_id, freeAlgKanMap_id]
      inv_hom_id := by rw [← freeAlgKanMap_comp, Iso.inv_hom_id, freeAlgKanMap_id] }
  let e_tr : freeAlgKan (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk n)) ≅
      freeAlgKan S₁.toFunctor :=
    { hom := freeAlgKanMap (simplexSubfunctorIso.{u} (faceLast n)).hom
      inv := freeAlgKanMap (simplexSubfunctorIso.{u} (faceLast n)).inv
      hom_inv_id := by rw [← freeAlgKanMap_comp, Iso.hom_inv_id, freeAlgKanMap_id]
      inv_hom_id := by rw [← freeAlgKanMap_comp, Iso.inv_hom_id, freeAlgKanMap_id] }
  let e_br : freeAlgKan (S₁ ⊔ S₂).toFunctor ≅
      freeAlgKan (SemiSSet.boundary.{u} (n + 1)).toFunctor :=
    { hom := freeAlgKanMap (Subfunctor.homOfLe (sup_simplexSubfunctor_faceLast_horn_le_boundary n))
      inv := freeAlgKanMap (Subfunctor.homOfLe (boundary_le_sup_simplexSubfunctor_faceLast_horn n))
      hom_inv_id := by
        rw [← freeAlgKanMap_comp]
        have heq : Subfunctor.homOfLe (sup_simplexSubfunctor_faceLast_horn_le_boundary n) ≫
            Subfunctor.homOfLe (boundary_le_sup_simplexSubfunctor_faceLast_horn n) = 𝟙 _ := by
          ext Δ x; rfl
        rw [heq, freeAlgKanMap_id]
      inv_hom_id := by
        rw [← freeAlgKanMap_comp]
        have heq : Subfunctor.homOfLe (boundary_le_sup_simplexSubfunctor_faceLast_horn n) ≫
            Subfunctor.homOfLe (sup_simplexSubfunctor_faceLast_horn_le_boundary n) = 𝟙 _ := by
          ext Δ x; rfl
        rw [heq, freeAlgKanMap_id] }
  refine (IsPushout.of_iso hpo_sup e_tl.symm e_tr.symm (Iso.refl _) e_br ?_ ?_ ?_ ?_)
  · dsimp [e_tl, e_tr]
    rw [← freeAlgKanMap_comp, ← freeAlgKanMap_comp]
    congr 1
  · dsimp [e_tl]
    rw [Category.comp_id, ← freeAlgKanMap_comp, Iso.inv_hom_id_assoc]
  · dsimp [e_tr, e_br]
    rw [← freeAlgKanMap_comp, ← freeAlgKanMap_comp]
    congr 1
    ext Δ x
    apply Subtype.ext
    exact (simplexSubfunctorInvApp_spec (faceLast n) Δ x).symm
  · dsimp [e_br]
    rw [Category.id_comp, ← freeAlgKanMap_comp]
    rfl

lemma stdSimplexToBoundarySucc_comp_inclusion_weakEquivalence (n : ℕ) :
    weakEquivalences CDelta.{u}
      (stdSimplexToBoundarySucc.{u} n ≫ boundaryCDeltaInclusion.{u} (n + 1)) := by
  apply Cylinder.SemisimplicialCategory.cDelta_simplexMaps_weakEquivalence
  refine ⟨n, n + 1, faceLast n,
    freeAlgKanUnit (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk n)),
    freeAlgKanUnit (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk (n + 1))),
    freeAlgKan_isFreeOn _, freeAlgKan_isFreeOn _, ?_⟩
  change freeAlgKanUnit _ ≫
    (freeAlgKanMap _ ≫ freeAlgKanMap (SemiSSet.boundary.{u} (n + 1)).ι).hom = _
  rw [← freeAlgKanMap_comp, freeAlgKanUnit_comp_freeAlgKanMap]
  congr 1

lemma hornLastToBoundarySucc_comp_inclusion_weakEquivalence (n : ℕ) :
    weakEquivalences CDelta.{u}
      (hornLastToBoundarySucc.{u} n ≫ boundaryCDeltaInclusion.{u} (n + 1)) := by
  refine Packages.cDelta_horn_weakEquivalence n (Fin.last (n + 1))
    (freeAlgKanUnit (SemiSSet.horn.{u} (n + 1) (Fin.last (n + 1))).toFunctor)
    (freeAlgKanUnit (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk (n + 1))))
    (freeAlgKan_isFreeOn _) (freeAlgKan_isFreeOn _)
    (hornLastToBoundarySucc.{u} n ≫ boundaryCDeltaInclusion.{u} (n + 1)) ?_
  change freeAlgKanUnit _ ≫
    (freeAlgKanMap _ ≫ freeAlgKanMap (SemiSSet.boundary.{u} (n + 1)).ι).hom = _
  rw [← freeAlgKanMap_comp, freeAlgKanUnit_comp_freeAlgKanMap]
  rfl

end HomotopyHypothesis.Cylinder.SimplicialCategory
