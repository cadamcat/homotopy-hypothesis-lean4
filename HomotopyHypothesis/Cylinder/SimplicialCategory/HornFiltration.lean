import HomotopyHypothesis.Cylinder.SimplicialCategory.FreeAlgKan
import HomotopyHypothesis.Cylinder.SimplicialCategory.SimplexContractions
import HomotopyHypothesis.Cylinder.SimplicialCategory.SimplexSubfunctors
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
/-!
# Dimension bounds and the skeletal filtration of horns in `Δ_{n+1}`

This file establishes:
1. The dimension bound predicate `HasDimLe M F` on semi-simplicial sets `F : SemiSSet.{u}` and its
   closure properties under subfunctor operations.
2. A general isomorphism `subfunctorIsoInf S σ K hK : K.toFunctor ≅ (S ⊓ simplexSubfunctor σ).toFunctor`
   identifying the intersection of a subfunctor `S` with the image of an `m`-simplex `σ`.
3. The skeletal filtration `hornSkelSubfunctor n k d` of the horn `Λ^{n+1}_k` by simplices whose
   range contains the vertex `k`, showing that `hornSkelSubfunctor n k 0` is the `0`-simplex `k`,
   `hornSkelSubfunctor n k n = Λ^{n+1}_k`, and each `(d + 1)`-simplex attachment for `d < n`
   intersects along a lower-dimensional horn `Λ^{d+1}_{j_k}`.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra Opposite ConcreteCategory

namespace HomotopyHypothesis.Cylinder.SimplicialCategory

open HomotopyHypothesis.Henry

/-!
## Dimension bounds on semi-simplicial sets
-/

/-- A semi-simplicial set `F` has dimension at most `M` if every simplex of `F` has length `≤ M`. -/
def HasDimLe (M : ℕ) (F : SemiSSet.{u}) : Prop :=
  ∀ ⦃Δ : Henry.SemiSimplexCategoryᵒᵖ⦄, F.obj Δ → (unop Δ).obj.len ≤ M

lemma hasDimLe_mono {M M' : ℕ} (hMM' : M ≤ M') {F : SemiSSet.{u}} (hF : HasDimLe M F) :
    HasDimLe M' F :=
  fun _ x => (hF x).trans hMM'

lemma hasDimLe_of_hom {M : ℕ} {F₁ F₂ : SemiSSet.{u}} (f : F₁ ⟶ F₂) (hF₂ : HasDimLe M F₂) :
    HasDimLe M F₁ :=
  fun Δ x => hF₂ (f.app Δ x)

lemma hasDimLe_bot (M : ℕ) (B : SemiSSet.{u}) :
    HasDimLe M (⊥ : Subfunctor B).toFunctor :=
  fun _ x => x.2.elim

lemma hasDimLe_of_le {M : ℕ} {B : SemiSSet.{u}} {S T : Subfunctor B} (hST : S ≤ T)
    (hT : HasDimLe M T.toFunctor) :
    HasDimLe M S.toFunctor :=
  hasDimLe_of_hom (Subfunctor.homOfLe hST) hT

lemma hasDimLe_sup {M : ℕ} {B : SemiSSet.{u}} {S₁ S₂ : Subfunctor B}
    (h₁ : HasDimLe M S₁.toFunctor) (h₂ : HasDimLe M S₂.toFunctor) :
    HasDimLe M (S₁ ⊔ S₂).toFunctor := by
  intro Δ x
  rcases x.2 with hx₁ | hx₂
  · exact h₁ ⟨x.1, hx₁⟩
  · exact h₂ ⟨x.1, hx₂⟩

lemma hasDimLe_stdSimplex {m M : ℕ} (hm : m ≤ M) :
    HasDimLe M (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m)) :=
  fun _ x => (len_le_of_hom (ULift.down x)).trans hm

lemma hasDimLe_simplexSubfunctor {m N M : ℕ} (hm : m ≤ M)
    (σ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk N) :
    HasDimLe M (simplexSubfunctor.{u} σ).toFunctor :=
  hasDimLe_of_hom (simplexSubfunctorIso.{u} σ).inv (hasDimLe_stdSimplex hm)

lemma hasDimLe_subfunctor_stdSimplex {N M : ℕ} (hNM : N ≤ M)
    (S : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N))) :
    HasDimLe M S.toFunctor :=
  hasDimLe_of_hom S.ι (hasDimLe_stdSimplex hNM)

lemma hasDimLe_boundary (M : ℕ) :
    HasDimLe M (SemiSSet.boundary.{u} (M + 1)).toFunctor :=
  fun _ x => Nat.le_of_lt_succ ((mem_boundary_iff x.1).mp x.2)

lemma hasDimLe_horn (M : ℕ) (k : Fin (M + 2)) :
    HasDimLe M (SemiSSet.horn.{u} (M + 1) k).toFunctor :=
  hasDimLe_of_le
    (show SemiSSet.horn.{u} (M + 1) k ≤ SemiSSet.boundary.{u} (M + 1) from
      fun _ _ ⟨j, _, hj⟩ => ⟨j, hj⟩)
    (hasDimLe_boundary M)

lemma hasDimLe_skelSubfunctor {N M d : ℕ}
    {S T : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N))}
    (hS : HasDimLe M S.toFunctor) (hd : d ≤ M + 1) :
    HasDimLe M (skelSubfunctor S T d).toFunctor := by
  intro Δ x
  rcases x.2 with hxS | ⟨_, hlt⟩
  · exact hS ⟨x.1, hxS⟩
  · exact Nat.le_of_lt_succ (lt_of_lt_of_le hlt hd)

lemma hasDimLe_addCellsAt {N M m : ℕ} (hm : m ≤ M)
    {S' : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N))}
    (hS' : HasDimLe M S'.toFunctor)
    (F : Finset (Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk N)) :
    HasDimLe M (addCellsAt m S' F).toFunctor := by
  intro Δ x
  rcases x.2 with hxS' | ⟨σ, _, hxσ⟩
  · exact hS' ⟨x.1, hxS'⟩
  · exact hasDimLe_simplexSubfunctor hm σ ⟨x.1, hxσ⟩

/-!
## General intersection isomorphism `K.toFunctor ≅ (S ⊓ simplexSubfunctor σ).toFunctor`
-/

/-- Given `S : Subfunctor Δ_N`, `σ : [m] ⟶ [N]`, and `K : Subfunctor Δ_m` characterizing the
pullback of `S` along `σ`, there is a canonical isomorphism
`K.toFunctor ≅ (S ⊓ simplexSubfunctor σ).toFunctor`. -/
noncomputable def subfunctorIsoInf {m N : ℕ}
    (S : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)))
    (σ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk N)
    (K : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m)))
    (hK : ∀ ⦃Δ : Henry.SemiSimplexCategoryᵒᵖ⦄
      (x : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m)).obj Δ),
      ULift.up (ULift.down x ≫ σ) ∈ S.obj Δ ↔ x ∈ K.obj Δ) :
    K.toFunctor ≅ (S ⊓ simplexSubfunctor.{u} σ).toFunctor where
  hom :=
    { app Δ := ↾(fun x =>
        ⟨ULift.up (ULift.down x.1 ≫ σ), (hK x.1).mpr x.2, ⟨ULift.down x.1, rfl⟩⟩)
      naturality {Δ Δ'} f := by
        ext x
        apply Subtype.ext
        change ULift.up ((unop f ≫ ULift.down x.1) ≫ σ) =
          ULift.up (unop f ≫ ULift.down x.1 ≫ σ)
        rw [Category.assoc] }
  inv :=
    { app Δ := ↾(fun y =>
        ⟨simplexSubfunctorInvApp.{u} σ Δ ⟨y.1, y.2.2⟩, by
          refine (hK _).mp ?_
          rw [simplexSubfunctorInvApp_spec]
          exact y.2.1⟩)
      naturality {Δ Δ'} f := by
        ext y
        apply Subtype.ext
        exact ConcreteCategory.congr_hom
          ((simplexSubfunctorIso.{u} σ).inv.naturality f) ⟨y.1, y.2.2⟩ }
  hom_inv_id := by
    ext Δ x
    apply Subtype.ext
    apply simplexSubfunctorHomApp_injective σ
    exact simplexSubfunctorInvApp_spec σ Δ
      ⟨ULift.up (x.1.down ≫ σ), ⟨x.1.down, rfl⟩⟩
  inv_hom_id := by
    ext Δ y
    apply Subtype.ext
    exact simplexSubfunctorInvApp_spec σ Δ ⟨y.1, y.2.2⟩

@[simp]
lemma subfunctorIsoInf_hom_comp_right {m N : ℕ}
    (S : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)))
    (σ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk N)
    (K : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m)))
    (hK : ∀ ⦃Δ : Henry.SemiSimplexCategoryᵒᵖ⦄
      (x : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m)).obj Δ),
      ULift.up (ULift.down x ≫ σ) ∈ S.obj Δ ↔ x ∈ K.obj Δ) :
    (subfunctorIsoInf S σ K hK).hom ≫
      Subfunctor.homOfLe
        (inf_le_right : S ⊓ simplexSubfunctor.{u} σ ≤ simplexSubfunctor.{u} σ) =
      K.ι ≫ (simplexSubfunctorIso.{u} σ).hom := by
  ext Δ x
  rfl

/-- Characterization of `S ⊓ simplexSubfunctor σ` as `SemiSSet.boundary m` when `σ ∉ S` and all
proper faces of `σ` lie in `S`. -/
lemma mem_subfunctor_iff_mem_boundary {m N : ℕ}
    (S : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)))
    (σ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk N)
    (hσ_not_mem : ULift.up σ ∉ S.obj (op (Henry.SemiSimplexCategory.mk m)))
    (hσ_bd : ∀ ⦃Δ : Henry.SemiSimplexCategoryᵒᵖ⦄ (g : unop Δ ⟶ Henry.SemiSimplexCategory.mk m),
      (unop Δ).obj.len < m → ULift.up (g ≫ σ) ∈ S.obj Δ)
    {Δ : Henry.SemiSimplexCategoryᵒᵖ}
    (x : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m)).obj Δ) :
    ULift.up (ULift.down x ≫ σ) ∈ S.obj Δ ↔ x ∈ (SemiSSet.boundary.{u} m).obj Δ := by
  constructor
  · intro hxS
    by_contra hnot
    obtain ⟨hΔ, hx_eq⟩ := eq_mk_and_eq_id_of_not_mem_boundary hnot
    cases Δ with | op Δ₀ =>
    dsimp at hΔ
    subst hΔ
    dsimp at hx_eq
    rw [hx_eq, Category.id_comp] at hxS
    exact hσ_not_mem hxS
  · intro hxbd
    exact hσ_bd (ULift.down x) ((mem_boundary_iff x).mp hxbd)

/-!
## Skeletal filtration of `SemiSSet.horn (n + 1) k`
-/

/-- The `k`-th vertex map `[0] ⟶ [N]` in `SemiSimplexCategory`. -/
def vertexSimplex {N : ℕ} (k : Fin (N + 1)) :
    Henry.SemiSimplexCategory.mk 0 ⟶ Henry.SemiSimplexCategory.mk N :=
  ⟨SimplexCategory.Hom.mk ⟨fun _ => k, fun _ _ _ => le_refl k⟩,
    SimplexCategory.mono_iff_injective.mpr (fun (a b : Fin 1) _ => Subsingleton.elim a b)⟩

@[simp]
lemma vertexSimplex_toOrderHom_apply {N : ℕ} (k : Fin (N + 1)) (i : Fin 1) :
    (vertexSimplex k).hom.toOrderHom i = k := rfl

lemma eq_vertexSimplex_of_mem_range {N : ℕ} (k : Fin (N + 1))
    (σ : Henry.SemiSimplexCategory.mk 0 ⟶ Henry.SemiSimplexCategory.mk N)
    (hk : k ∈ Set.range σ.hom.toOrderHom) :
    σ = vertexSimplex k := by
  rcases hk with ⟨i₀, hi₀⟩
  apply Henry.SemiSimplexCategory.incl.map_injective
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext (i : Fin 1)
  exact (congrArg σ.hom.toOrderHom (@Subsingleton.elim (Fin 1) inferInstance i i₀)).trans hi₀

/-- The `d`-skeleton of `Λ^{n+1}_k` consisting of simplices factoring through some `σ : [m] ⟶ [n + 1]`
with `m ≤ d` and `k ∈ Set.range σ`. -/
def hornSkelSubfunctor (n : ℕ) (k : Fin (n + 2)) (d : ℕ) :
    Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk (n + 1))) where
  obj Δ x :=
    ∃ (m : ℕ) (_ : m ≤ d) (σ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk (n + 1)),
      k ∈ Set.range σ.hom.toOrderHom ∧ x ∈ (simplexSubfunctor.{u} σ).obj Δ
  map {Δ Δ'} f {x} := by
    rintro ⟨m, hmd, σ, hkσ, hxσ⟩
    exact ⟨m, hmd, σ, hkσ, (simplexSubfunctor.{u} σ).map f hxσ⟩

lemma hasDimLe_hornSkelSubfunctor (n : ℕ) (k : Fin (n + 2)) {d M : ℕ} (hdM : d ≤ M) :
    HasDimLe M (hornSkelSubfunctor.{u} n k d).toFunctor := by
  rintro Δ ⟨x, m, hmd, σ, _, hxσ⟩
  exact hasDimLe_simplexSubfunctor (hmd.trans hdM) σ ⟨x, hxσ⟩

lemma hornSkelSubfunctor_zero_le (n : ℕ) (k : Fin (n + 2)) :
    hornSkelSubfunctor.{u} n k 0 ≤ simplexSubfunctor.{u} (vertexSimplex k) := by
  rintro Δ x ⟨m, hm0, σ, hkσ, hxσ⟩
  have hm_eq : m = 0 := Nat.le_zero.mp hm0
  subst hm_eq
  rw [eq_vertexSimplex_of_mem_range k σ hkσ] at hxσ
  exact hxσ

lemma le_hornSkelSubfunctor_zero (n : ℕ) (k : Fin (n + 2)) :
    simplexSubfunctor.{u} (vertexSimplex k) ≤ hornSkelSubfunctor.{u} n k 0 := by
  intro Δ x hx
  exact ⟨0, le_refl 0, vertexSimplex k, ⟨0, rfl⟩, hx⟩

lemma hornSkelSubfunctor_le_horn (n : ℕ) (k : Fin (n + 2)) :
    hornSkelSubfunctor.{u} n k n ≤ SemiSSet.horn.{u} (n + 1) k := by
  rintro Δ x ⟨m, hmn, σ, hkσ, g, rfl⟩
  have hbd : ULift.up.{u} σ ∈
      (SemiSSet.boundary.{u} (n + 1)).obj (op (Henry.SemiSimplexCategory.mk m)) :=
    (mem_boundary_iff.{u} (ULift.up.{u} σ)).mpr (Nat.lt_succ_of_le hmn)
  rcases hbd with ⟨j, hj⟩
  have hjk : j ≠ k := by
    rintro rfl
    exact hj hkσ
  refine ⟨j, hjk, ?_⟩
  rintro ⟨i, hi⟩
  exact hj ⟨g.hom.toOrderHom i, hi⟩

lemma horn_le_hornSkelSubfunctor (n : ℕ) (k : Fin (n + 2)) :
    SemiSSet.horn.{u} (n + 1) k ≤ hornSkelSubfunctor.{u} n k n := by
  intro Δ x hx
  obtain ⟨j, hjk, g, hg⟩ := horn_eq_map_hornFace n k ⟨x, hx⟩
  have hx_eq : x = ULift.up (g ≫ semiDelta j) := congrArg Subtype.val hg
  refine ⟨n, le_refl n, semiDelta j, ?_, g, hx_eq⟩
  exact Fin.exists_succAbove_eq hjk.symm

/-- The `(d + 1)`-simplices of `Δ_{n+1}` whose range contains `k`. -/
noncomputable def hornCellsAt (n : ℕ) (k : Fin (n + 2)) (d : ℕ) :
    Finset (Henry.SemiSimplexCategory.mk (d + 1) ⟶ Henry.SemiSimplexCategory.mk (n + 1)) :=
  Finset.univ.filter (fun σ => k ∈ Set.range σ.hom.toOrderHom)

lemma mem_hornCellsAt_iff {n : ℕ} {k : Fin (n + 2)} {d : ℕ}
    (σ : Henry.SemiSimplexCategory.mk (d + 1) ⟶ Henry.SemiSimplexCategory.mk (n + 1)) :
    σ ∈ hornCellsAt n k d ↔ k ∈ Set.range σ.hom.toOrderHom := by
  simp [hornCellsAt]

lemma hornSkelSubfunctor_succ_le_addCellsAt (n : ℕ) (k : Fin (n + 2)) (d : ℕ) :
    hornSkelSubfunctor.{u} n k (d + 1) ≤
      addCellsAt (d + 1) (hornSkelSubfunctor.{u} n k d) (hornCellsAt n k d) := by
  rintro Δ x ⟨m, hmd, σ, hkσ, hxσ⟩
  rcases Nat.of_le_succ hmd with hle | rfl
  · exact Or.inl ⟨m, hle, σ, hkσ, hxσ⟩
  · exact Or.inr ⟨σ, (mem_hornCellsAt_iff σ).mpr hkσ, hxσ⟩

lemma addCellsAt_le_hornSkelSubfunctor_succ (n : ℕ) (k : Fin (n + 2)) (d : ℕ) :
    addCellsAt (d + 1) (hornSkelSubfunctor.{u} n k d) (hornCellsAt n k d) ≤
      hornSkelSubfunctor.{u} n k (d + 1) := by
  intro Δ x hx
  rcases hx with ⟨m, hmd, σ, hkσ, hxσ⟩ | ⟨σ, hσ, hxσ⟩
  · exact ⟨m, Nat.le_succ_of_le hmd, σ, hkσ, hxσ⟩
  · exact ⟨d + 1, le_refl (d + 1), σ, (mem_hornCellsAt_iff σ).mp hσ, hxσ⟩

/-- If `Set.range σ.hom.toOrderHom ⊆ Set.range τ.hom.toOrderHom`, then `σ` factors through `τ`
in `SemiSimplexCategory`. -/
lemma factor_of_range_subset {a b N : ℕ}
    (σ : Henry.SemiSimplexCategory.mk a ⟶ Henry.SemiSimplexCategory.mk N)
    (τ : Henry.SemiSimplexCategory.mk b ⟶ Henry.SemiSimplexCategory.mk N)
    (hsub : ∀ j : Fin (a + 1), ∃ i : Fin (b + 1), τ.hom.toOrderHom i = σ.hom.toOrderHom j) :
    ∃ h : Henry.SemiSimplexCategory.mk a ⟶ Henry.SemiSimplexCategory.mk b, h ≫ τ = σ := by
  let φ : Fin (a + 1) → Fin (b + 1) := fun j => Classical.choose (hsub j)
  have hφ : ∀ j : Fin (a + 1), τ.hom.toOrderHom (φ j) = σ.hom.toOrderHom j :=
    fun j => Classical.choose_spec (hsub j)
  have hmono_τ : StrictMono τ.hom.toOrderHom := strictMono_toOrderHom τ
  have hmono_φ : Monotone φ := by
    intro j₁ j₂ hj
    rw [← hmono_τ.le_iff_le, hφ j₁, hφ j₂]
    exact σ.hom.toOrderHom.monotone hj
  have hinj_φ : Function.Injective φ := by
    intro j₁ j₂ hj
    have h1 : σ.hom.toOrderHom j₁ = σ.hom.toOrderHom j₂ := by
      rw [← hφ j₁, ← hφ j₂, hj]
    exact SimplexCategory.mono_iff_injective.mp σ.property h1
  let h : Henry.SemiSimplexCategory.mk a ⟶ Henry.SemiSimplexCategory.mk b :=
    ⟨SimplexCategory.Hom.mk ⟨φ, hmono_φ⟩, SimplexCategory.mono_iff_injective.mpr hinj_φ⟩
  refine ⟨h, ?_⟩
  apply Henry.SemiSimplexCategory.incl.map_injective
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  exact hφ j

/-- When attaching a `(d + 1)`-simplex `σ` with `σ(j_k) = k` (`σ ∉ F`) to
`addCellsAt (d + 1) (hornSkelSubfunctor n k d) F`, the pullback along `σ` is `Λ^{d+1}_{j_k}`. -/
lemma mem_addCellsAt_hornSkelSubfunctor_iff_mem_horn {n d : ℕ} {k : Fin (n + 2)}
    (F : Finset (Henry.SemiSimplexCategory.mk (d + 1) ⟶ Henry.SemiSimplexCategory.mk (n + 1)))
    (hF : F ⊆ hornCellsAt n k d)
    (σ : Henry.SemiSimplexCategory.mk (d + 1) ⟶ Henry.SemiSimplexCategory.mk (n + 1))
    (hσ_not_mem : σ ∉ F)
    (j_k : Fin (d + 2)) (hj_k : σ.hom.toOrderHom j_k = k)
    {Δ : Henry.SemiSimplexCategoryᵒᵖ}
    (y : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk (d + 1))).obj Δ) :
    ULift.up (ULift.down y ≫ σ) ∈
      (addCellsAt (d + 1) (hornSkelSubfunctor.{u} n k d) F).obj Δ ↔
      y ∈ (SemiSSet.horn.{u} (d + 1) j_k).obj Δ := by
  constructor
  · intro hy_mem
    by_contra hnot_horn
    have hsurj_other : ∀ j : Fin (d + 2), j ≠ j_k → j ∈ Set.range (ULift.down y).hom.toOrderHom := by
      intro j hjj
      by_contra hnot_range
      exact hnot_horn ⟨j, hjj, hnot_range⟩
    have hsub_of_factor : ∀ {m : ℕ}
        (τ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk (n + 1)),
        k ∈ Set.range τ.hom.toOrderHom →
        (∃ g : unop Δ ⟶ Henry.SemiSimplexCategory.mk m, ULift.up (ULift.down y ≫ σ) = ULift.up (g ≫ τ)) →
        ∃ h : Henry.SemiSimplexCategory.mk (d + 1) ⟶ Henry.SemiSimplexCategory.mk m, h ≫ τ = σ := by
      intro m τ hkτ ⟨g, hg⟩
      have hg' : ULift.down y ≫ σ = g ≫ τ := ULift.up.inj hg
      apply factor_of_range_subset σ τ
      intro j
      by_cases hjj : j = j_k
      · subst hjj
        rw [hj_k]
        exact hkτ
      · obtain ⟨i, hi⟩ := hsurj_other j hjj
        refine ⟨g.hom.toOrderHom i, ?_⟩
        have h_eq := congrFun (congrArg (fun f : unop Δ ⟶ Henry.SemiSimplexCategory.mk (n + 1) =>
          (f.hom.toOrderHom : Fin ((unop Δ).obj.len + 1) → Fin (n + 2))) hg') i
        change σ.hom.toOrderHom ((ULift.down y).hom.toOrderHom i) =
          τ.hom.toOrderHom (g.hom.toOrderHom i) at h_eq
        rw [hi] at h_eq
        exact h_eq.symm
    rcases hy_mem with ⟨m, hmd, τ, hkτ, hxτ⟩ | ⟨τ, hτF, hxτ⟩
    · obtain ⟨h, _⟩ := hsub_of_factor τ hkτ hxτ
      have hle : d + 1 ≤ m := len_le_of_hom h
      omega
    · have hkτ : k ∈ Set.range τ.hom.toOrderHom := (mem_hornCellsAt_iff τ).mp (hF hτF)
      obtain ⟨h, hh⟩ := hsub_of_factor τ hkτ hxτ
      have hh_id : h = 𝟙 (Henry.SemiSimplexCategory.mk (d + 1)) := hom_eq_id_of_end h
      rw [hh_id, Category.id_comp] at hh
      subst hh
      exact hσ_not_mem hτF
  · intro hy_horn
    obtain ⟨j, hjj_k, g, hg⟩ := horn_eq_map_hornFace d j_k ⟨y, hy_horn⟩
    have hy_eq : ULift.down y = g ≫ semiDelta j := ULift.up.inj (congrArg Subtype.val hg)
    left
    refine ⟨d, le_refl d, semiDelta j ≫ σ, ?_, g, ?_⟩
    · obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hjj_k.symm
      refine ⟨i, ?_⟩
      change σ.hom.toOrderHom (j.succAbove i) = k
      rw [hi, hj_k]
    · rw [hy_eq, Category.assoc]

end HomotopyHypothesis.Cylinder.SimplicialCategory
