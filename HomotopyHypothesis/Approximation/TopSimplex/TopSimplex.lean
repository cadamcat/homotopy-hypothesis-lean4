import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Anodyne.StdSimplex
import HomotopyHypothesis.Realization.SemisimplicialComparison.TopSimplex
/-!
# Attaching a top-dimensional simplex

Every nonempty semi-simplicial subset `S` of a standard simplex `Δ_N` is obtained from a smaller
one `S'` by attaching one simplex `σ` of top dimension along its boundary, by a pushout square
`∂Δ_m ⟶ S'`, `Δ_m ⟶ S` of semi-simplicial sets.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.TopSimplex

open HomotopyHypothesis.Henry

abbrev simplexCells (N : ℕ) (S : Subfunctor (SemiSSet.stdSimplex.{u}.obj
    (Henry.SemiSimplexCategory.mk N))) :=
  Σ p : Fin (N + 1), S.toFunctor.obj (op (Henry.SemiSimplexCategory.mk p.1))

theorem simplexCells_finite (N : ℕ)
    (S : Subfunctor (SemiSSet.stdSimplex.{u}.obj
      (Henry.SemiSimplexCategory.mk N))) :
    Finite (simplexCells N S) := by
  classical
  have hstd := Approximation.Anodyne.stdSimplex_isFinite_proof.{u} N
  have hfiber (p : Fin (N + 1)) :
      Finite (S.toFunctor.obj (op (Henry.SemiSimplexCategory.mk p.1))) := by
    haveI : Finite ((SemiSSet.stdSimplex.{u}.obj
        (Henry.SemiSimplexCategory.mk N)).obj
          (op (Henry.SemiSimplexCategory.mk p.1))) := hstd.1 p.1
    dsimp [Subfunctor.toFunctor]
    exact Subtype.finite
  letI : ∀ p : Fin (N + 1), Finite
      (S.toFunctor.obj (op (Henry.SemiSimplexCategory.mk p.1))) := hfiber
  infer_instance

theorem exists_maximal_simplex {N : ℕ}
    (S : Subfunctor (SemiSSet.stdSimplex.{u}.obj
      (Henry.SemiSimplexCategory.mk N)))
    (hS : ∃ d, (S.obj d).Nonempty) :
    ∃ (m : ℕ) (hm : m ≤ N) (σ : (SemiSSet.stdSimplex.{u}.obj
      (Henry.SemiSimplexCategory.mk N)).obj (op (Henry.SemiSimplexCategory.mk m))),
      σ ∈ S.obj (op (Henry.SemiSimplexCategory.mk m)) ∧
        ∀ p : ℕ, p ≤ N → (S.obj (op (Henry.SemiSimplexCategory.mk p))).Nonempty → p ≤ m := by
  classical
  obtain ⟨d, hd⟩ := hS
  obtain ⟨x, hx⟩ := hd
  let p := d.unop.obj.len
  have hpdim : d = op (Henry.SemiSimplexCategory.mk p) := by
    apply congrArg op
    apply WideSubcategory.ext
    exact (SimplexCategory.mk_len d.unop.obj).symm
  have hple : p ≤ N := by
    have hle := @SimplexCategory.len_le_of_mono _ _ x.down.hom x.down.property
    simpa [p, Henry.SemiSimplexCategory.mk] using hle
  have hcanon : (S.obj (op (Henry.SemiSimplexCategory.mk p))).Nonempty := by
    rw [← hpdim]
    exact ⟨x, hx⟩
  let dims : Finset (Fin (N + 1)) := Finset.univ.filter fun i =>
    (S.obj (op (Henry.SemiSimplexCategory.mk i.1))).Nonempty
  have hdims : dims.Nonempty := by
    refine ⟨⟨p, by omega⟩, ?_⟩
    simp [dims, hcanon]
  let m := dims.max' hdims
  have hm_mem : m ∈ dims := Finset.max'_mem dims hdims
  have hm_nonempty : (S.obj (op (Henry.SemiSimplexCategory.mk m.1))).Nonempty := by
    simpa [dims] using hm_mem
  obtain ⟨σ, hσ⟩ := hm_nonempty
  refine ⟨m.1, by omega, σ, hσ, ?_⟩
  intro q hq hqS
  have hq_mem : (⟨q, by omega⟩ : Fin (N + 1)) ∈ dims := by
    simp [dims, hqS]
  have hqle : (⟨q, by omega⟩ : Fin (N + 1)) ≤ m :=
    Finset.le_max' dims ⟨q, by omega⟩ hq_mem
  exact (Fin.le_iff_val_le_val).mp hqle

theorem simplex_dimension_le {N : ℕ} {d : Henry.SemiSimplexCategoryᵒᵖ}
    {x : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)).obj d} :
    d.unop.obj.len ≤ N := by
  have hle := @SimplexCategory.len_le_of_mono _ _ x.down.hom x.down.property
  simpa [Henry.SemiSimplexCategory.mk] using hle

theorem simplex_dimension_le_max {N m : ℕ}
    {S : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N))}
    (hmax : ∀ p : ℕ, p ≤ N → (S.obj
      (op (Henry.SemiSimplexCategory.mk p))).Nonempty → p ≤ m)
    {d : Henry.SemiSimplexCategoryᵒᵖ}
    {x : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)).obj d}
    (hx : x ∈ S.obj d) : d.unop.obj.len ≤ m := by
  let p := d.unop.obj.len
  have hp : p ≤ N := simplex_dimension_le (N := N) (d := d) (x := x)
  have hd : d = op (Henry.SemiSimplexCategory.mk p) := by
    apply congrArg op
    apply WideSubcategory.ext
    exact (SimplexCategory.mk_len d.unop.obj).symm
  have hsp : (S.obj (op (Henry.SemiSimplexCategory.mk p))).Nonempty := by
    rw [← hd]
    exact ⟨x, hx⟩
  exact hmax p hp hsp

def deleteTopSimplex {N m : ℕ}
    (S : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)))
    (σ : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)).obj
      (op (Henry.SemiSimplexCategory.mk m)))
    (hmax : ∀ p : ℕ, p ≤ N → (S.obj
      (op (Henry.SemiSimplexCategory.mk p))).Nonempty → p ≤ m) :
    Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)) where
  obj d := {x | x ∈ S.obj d ∧ ∀ h : d = op (Henry.SemiSimplexCategory.mk m), h ▸ x ≠ σ}
  map {U V} i := by
    classical
    intro x hx
    refine ⟨S.map i hx.1, ?_⟩
    intro hV
    subst V
    intro heq
    have hdim : m ≤ U.unop.obj.len := by
      have hle := @SimplexCategory.len_le_of_mono _ _ i.unop.hom i.unop.property
      simpa [Henry.SemiSimplexCategory.mk] using hle
    have huMax : U.unop.obj.len ≤ m :=
      simplex_dimension_le_max hmax hx.1
    have huLen : U.unop.obj.len = m := Nat.le_antisymm huMax hdim
    have hU : U = op (Henry.SemiSimplexCategory.mk m) := by
      apply congrArg op
      apply WideSubcategory.ext
      calc
        U.unop.obj = SimplexCategory.mk U.unop.obj.len :=
          (SimplexCategory.mk_len U.unop.obj).symm
        _ = SimplexCategory.mk m := by rw [huLen]
    subst U
    have hiUnop : i.unop = 𝟙 _ := by
      haveI : Mono i.unop.hom := i.unop.property
      apply WideSubcategory.hom_ext
      exact SimplexCategory.eq_id_of_mono i.unop.hom
    have hi : i = 𝟙 _ := by
      apply Quiver.Hom.unop_inj
      exact hiUnop
    have hxEq : x = σ := by simpa [hi] using heq
    exact hx.2 rfl hxEq

theorem deleteTopSimplex_le {N m : ℕ}
    (S : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)))
    (σ : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)).obj
      (op (Henry.SemiSimplexCategory.mk m)))
    (hmax : ∀ p : ℕ, p ≤ N → (S.obj
      (op (Henry.SemiSimplexCategory.mk p))).Nonempty → p ≤ m) :
    deleteTopSimplex S σ hmax ≤ S := by
  intro d x hx
  exact hx.1

noncomputable def simplexMapToSub {N m : ℕ}
    (S : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)))
    (σ : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)).obj
      (op (Henry.SemiSimplexCategory.mk m)))
    (hσ : σ ∈ S.obj (op (Henry.SemiSimplexCategory.mk m))) :
    SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m) ⟶ S.toFunctor :=
  uliftYonedaEquiv.symm (show S.toFunctor.obj
    (op (Henry.SemiSimplexCategory.mk m)) from ⟨σ, hσ⟩)

theorem simplexMapToSub_app_val {N m : ℕ}
    (S : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)))
    (σ : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)).obj
      (op (Henry.SemiSimplexCategory.mk m)))
    (hσ : σ ∈ S.obj (op (Henry.SemiSimplexCategory.mk m)))
    {d : Henry.SemiSimplexCategoryᵒᵖ}
    (f : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m)).obj d) :
    ((simplexMapToSub S σ hσ).app d f).1 =
      (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)).map
        (Quiver.Hom.op f.down) σ := by
  rfl

theorem semiArrow_mono {A B : Henry.SemiSimplexCategory} (f : A ⟶ B) : Mono f where
  right_cancellation g h hgh := by
    apply Henry.SemiSimplexCategory.incl.map_injective
    haveI : Mono (Henry.SemiSimplexCategory.incl.map f) := f.property
    apply (cancel_mono (Henry.SemiSimplexCategory.incl.map f)).1
    simpa only [Functor.map_comp] using congrArg
      (fun k => Henry.SemiSimplexCategory.incl.map k) hgh

theorem simplexMapToSub_app_injective {N m : ℕ}
    (S : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)))
    (σ : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)).obj
      (op (Henry.SemiSimplexCategory.mk m)))
    (hσ : σ ∈ S.obj (op (Henry.SemiSimplexCategory.mk m)))
    {d : Henry.SemiSimplexCategoryᵒᵖ} :
    Function.Injective ((simplexMapToSub S σ hσ).app d) := by
  intro f g h
  have hraw := congrArg Subtype.val h
  rw [simplexMapToSub_app_val, simplexMapToSub_app_val] at hraw
  have hcomp := congrArg ULift.down hraw
  change f.down ≫ σ.down = g.down ≫ σ.down at hcomp
  haveI : Mono σ.down := semiArrow_mono σ.down
  have hfg := (cancel_mono σ.down).1 hcomp
  exact ULift.ext f g hfg

theorem boundary_map_avoids_top {N m : ℕ}
    (S : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)))
    (σ : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)).obj
      (op (Henry.SemiSimplexCategory.mk m)))
    (hσ : σ ∈ S.obj (op (Henry.SemiSimplexCategory.mk m)))
    (z : (SemiSSet.boundary.{u} m).toFunctor.obj
      (op (Henry.SemiSimplexCategory.mk m))) :
    ((simplexMapToSub S σ hσ).app (op (Henry.SemiSimplexCategory.mk m))
      ((SemiSSet.boundary.{u} m).ι.app _ z)).1 ≠ σ := by
  intro heq
  have hcomp : ((SemiSSet.boundary.{u} m).ι.app
      (op (Henry.SemiSimplexCategory.mk m)) z).down ≫ σ.down = σ.down := by
    have h := heq
    rw [simplexMapToSub_app_val] at h
    change ULift.up (((SemiSSet.boundary.{u} m).ι.app
      (op (Henry.SemiSimplexCategory.mk m)) z).down ≫ σ.down) = σ at h
    exact ULift.ext_iff.mp h
  have hfid : ((SemiSSet.boundary.{u} m).ι.app
      (op (Henry.SemiSimplexCategory.mk m)) z).down = 𝟙 _ := by
    haveI : Mono σ.down := semiArrow_mono σ.down
    apply (cancel_mono σ.down).1
    simpa using hcomp
  rcases z.2 with ⟨j, hj⟩
  have hmem : j ∈ Set.range (ULift.down z.1).hom.toOrderHom := by
    refine ⟨j, ?_⟩
    have hfid' : z.1.down = 𝟙 _ := by simpa using hfid
    simp [hfid']
  exact hj hmem

noncomputable def boundaryMapToDeleted {N m : ℕ}
    (S : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)))
    (σ : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)).obj
      (op (Henry.SemiSimplexCategory.mk m)))
    (hσ : σ ∈ S.obj (op (Henry.SemiSimplexCategory.mk m)))
    (hmax : ∀ p : ℕ, p ≤ N → (S.obj
      (op (Henry.SemiSimplexCategory.mk p))).Nonempty → p ≤ m) :
    (SemiSSet.boundary.{u} m).toFunctor ⟶ (deleteTopSimplex S σ hmax).toFunctor := by
  let b₀ := (SemiSSet.boundary.{u} m).ι ≫ simplexMapToSub S σ hσ
  refine { app := fun d => ↾fun z => ?_, naturality := ?_ }
  · refine ⟨(b₀.app d z).1, ?_⟩
    refine ⟨(b₀.app d z).2, ?_⟩
    intro h
    subst d
    simpa [b₀] using boundary_map_avoids_top S σ hσ z
  · intro X Y f
    ext z
    apply Subtype.ext
    simpa [b₀, Subfunctor.toFunctor] using
      congrArg Subtype.val (b₀.naturality_apply f z)

theorem deleteTopSimplex_count_lt {N m : ℕ}
    (S : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)))
    (σ : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)).obj
      (op (Henry.SemiSimplexCategory.mk m)))
    (hσ : σ ∈ S.obj (op (Henry.SemiSimplexCategory.mk m)))
    (hm : m ≤ N)
    (hmax : ∀ p : ℕ, p ≤ N → (S.obj
      (op (Henry.SemiSimplexCategory.mk p))).Nonempty → p ≤ m) :
    HomotopyHypothesis.Realization.SemisimplicialComparison.simplexCount
      (deleteTopSimplex S σ hmax).toFunctor N <
    HomotopyHypothesis.Realization.SemisimplicialComparison.simplexCount S.toFunctor N := by
  classical
  let S' := deleteTopSimplex S σ hmax
  haveI : Finite (simplexCells N S') := simplexCells_finite N S'
  haveI : Finite (simplexCells N S) := simplexCells_finite N S
  letI : Fintype (simplexCells N S') := Fintype.ofFinite _
  letI : Fintype (simplexCells N S) := Fintype.ofFinite _
  let f : simplexCells N S' → simplexCells N S := fun z =>
    ⟨z.1, ⟨z.2.1, (show z.2.1 ∈ S.obj
      (op (Henry.SemiSimplexCategory.mk z.1.1)) from (z.2.2).1)⟩⟩
  have hf : Function.Injective f := by
    intro a b hab
    rcases a with ⟨p, x⟩
    rcases b with ⟨q, y⟩
    dsimp [f] at hab
    have hidx : (⟨p.1, by omega⟩ : Fin (N + 1)) = ⟨q.1, by omega⟩ :=
      congrArg Sigma.fst hab
    have hp : p.1 = q.1 := by
      simpa using congrArg (fun i : Fin (N + 1) => i.1) hidx
    have hp' : p = q := Fin.ext hp
    subst q
    have hsub := eq_of_heq (Sigma.ext_iff.mp hab).2
    have hval : x.1 = y.1 :=
      congrArg (fun z : S.toFunctor.obj
        (op (Henry.SemiSimplexCategory.mk p.1)) => z.1) hsub
    have hxy : x = y := Subtype.ext hval
    subst y
    rfl
  let p₀ : Fin (N + 1) := ⟨m, by omega⟩
  let top : simplexCells N S := ⟨p₀, ⟨σ, hσ⟩⟩
  have htop : top ∉ Set.range f := by
    rintro ⟨⟨p, x⟩, h⟩
    dsimp [f, top] at h
    have hp : p = p₀ := (Sigma.ext_iff.mp h).1
    have hsub := (Sigma.ext_iff.mp h).2
    subst p
    have hsub' : (⟨x.1, (show x.1 ∈ S.obj _ from x.2.1)⟩ :
        S.toFunctor.obj (op (Henry.SemiSimplexCategory.mk m))) = ⟨σ, hσ⟩ :=
      eq_of_heq hsub
    have hσx : x.1 = σ := congrArg (fun z : S.toFunctor.obj
      (op (Henry.SemiSimplexCategory.mk m)) => z.1) hsub'
    exact x.2.2 rfl hσx
  simp only [HomotopyHypothesis.Realization.SemisimplicialComparison.simplexCount, Nat.card_eq_fintype_card]
  exact Fintype.card_lt_of_injective_not_surjective f hf (by
    intro hsurj
    exact htop (hsurj top))

theorem boundary_count_lt {N m : ℕ}
    (S : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)))
    (σ : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)).obj
      (op (Henry.SemiSimplexCategory.mk m)))
    (hσ : σ ∈ S.obj (op (Henry.SemiSimplexCategory.mk m)))
    (hm : m ≤ N) :
    HomotopyHypothesis.Realization.SemisimplicialComparison.simplexCount
      (SemiSSet.boundary.{u} m).toFunctor m <
    HomotopyHypothesis.Realization.SemisimplicialComparison.simplexCount S.toFunctor N := by
  classical
  haveI : Finite (simplexCells m (SemiSSet.boundary.{u} m)) :=
    simplexCells_finite m (SemiSSet.boundary.{u} m)
  haveI : Finite (simplexCells N S) := simplexCells_finite N S
  letI : Fintype (simplexCells m (SemiSSet.boundary.{u} m)) := Fintype.ofFinite _
  letI : Fintype (simplexCells N S) := Fintype.ofFinite _
  let smap := simplexMapToSub S σ hσ
  let f : simplexCells m (SemiSSet.boundary.{u} m) → simplexCells N S := fun z =>
    ⟨⟨z.1.1, by omega⟩,
      smap.app (op (Henry.SemiSimplexCategory.mk z.1.1))
        ((SemiSSet.boundary.{u} m).ι.app _ z.2)⟩
  have hf : Function.Injective f := by
    intro a b hab
    rcases a with ⟨p, x⟩
    rcases b with ⟨q, y⟩
    dsimp [f] at hab
    have hidx : (⟨p.1, by omega⟩ : Fin (N + 1)) = ⟨q.1, by omega⟩ :=
      congrArg Sigma.fst hab
    have hp : p.1 = q.1 := by
      simpa using congrArg (fun i : Fin (N + 1) => i.1) hidx
    have hp' : p = q := Fin.ext hp
    subst q
    have hsub := eq_of_heq (Sigma.ext_iff.mp hab).2
    have hxy : (SemiSSet.boundary.{u} m).ι.app
        (op (Henry.SemiSimplexCategory.mk p.1)) x =
      (SemiSSet.boundary.{u} m).ι.app
        (op (Henry.SemiSimplexCategory.mk p.1)) y :=
      (simplexMapToSub_app_injective S σ hσ) hsub
    have hxy' : x = y := by
      apply Subtype.ext
      exact hxy
    subst y
    rfl
  let p₀ : Fin (N + 1) := ⟨m, by omega⟩
  let top : simplexCells N S := ⟨p₀, ⟨σ, hσ⟩⟩
  have htop : top ∉ Set.range f := by
    rintro ⟨⟨p, x⟩, h⟩
    dsimp [f, top] at h
    have hp : (⟨p.1, by omega⟩ : Fin (N + 1)) = p₀ := congrArg Sigma.fst h
    have hsub := (Sigma.ext_iff.mp h).2
    have hp' : p.1 = m := by
      simpa [p₀] using congrArg (fun i : Fin (N + 1) => i.1) hp
    have hpFin : p = Fin.last m := Fin.ext hp'
    subst p
    have hsub' : smap.app (op (Henry.SemiSimplexCategory.mk m))
        ((SemiSSet.boundary.{u} m).ι.app _ x) = ⟨σ, hσ⟩ := eq_of_heq hsub
    have hraw : (smap.app (op (Henry.SemiSimplexCategory.mk m))
        ((SemiSSet.boundary.{u} m).ι.app _ x)).1 = σ :=
      congrArg (fun z : S.toFunctor.obj
        (op (Henry.SemiSimplexCategory.mk m)) => z.1) hsub'
    exact boundary_map_avoids_top S σ hσ x hraw
  simp only [HomotopyHypothesis.Realization.SemisimplicialComparison.simplexCount, Nat.card_eq_fintype_card]
  exact Fintype.card_lt_of_injective_not_surjective f hf (by
    intro hsurj
    exact htop (hsurj top))

theorem topSimplex_attachment_isPushout {N m : ℕ}
    (S : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)))
    (σ : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)).obj
      (op (Henry.SemiSimplexCategory.mk m)))
    (hσ : σ ∈ S.obj (op (Henry.SemiSimplexCategory.mk m)))
    (hmax : ∀ p : ℕ, p ≤ N → (S.obj
      (op (Henry.SemiSimplexCategory.mk p))).Nonempty → p ≤ m) :
    IsPushout (boundaryMapToDeleted S σ hσ hmax) (SemiSSet.boundary.{u} m).ι
      (Subfunctor.homOfLe (deleteTopSimplex_le S σ hmax))
      (simplexMapToSub S σ hσ) := by
  classical
  let incl := Subfunctor.homOfLe (deleteTopSimplex_le S σ hmax)
  let b := boundaryMapToDeleted S σ hσ hmax
  let smap := simplexMapToSub S σ hσ
  let idM : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m)).obj
      (op (Henry.SemiSimplexCategory.mk m)) := ULift.up (𝟙 (Henry.SemiSimplexCategory.mk m))
  have hsid : (smap.app (op (Henry.SemiSimplexCategory.mk m)) idM).1 = σ := by
    change ((simplexMapToSub S σ hσ).app
      (op (Henry.SemiSimplexCategory.mk m)) idM).1 = σ
    rw [simplexMapToSub_app_val]
    simp [idM]
  have hcomm : b ≫ incl = (SemiSSet.boundary.{u} m).ι ≫ smap := by
    ext d z
    rfl
  apply IsPushout.of_forall_isPushout_app
  intro d
  have hpb : IsPullback (b.app d) ((SemiSSet.boundary.{u} m).ι.app d)
      (incl.app d) (smap.app d) := by
    apply (Types.isPullback_iff _ _ _ _).2
    refine ⟨?_, ?_⟩
    · simpa using congrArg (fun α => α.app d) hcomm
    · refine ⟨?_, ?_⟩
      · intro x y hxy
        apply Subtype.ext
        exact hxy.2
      · intro x y hxy
        by_cases hybd : y ∈ (SemiSSet.boundary.{u} m).obj d
        · let z : (SemiSSet.boundary.{u} m).toFunctor.obj d := ⟨y, hybd⟩
          refine ⟨z, ?_, ?_⟩
          · have hcommd := congrArg (fun α => α.app d) hcomm
            have hcommz : incl.app d (b.app d z) = smap.app d y := by
              simpa [z] using congrArg (fun f => f z) hcommd
            have hinj : Function.Injective (incl.app d) := by
              rw [← mono_iff_injective]
              infer_instance
            apply hinj
            calc
              incl.app d (b.app d z) = smap.app d y := hcommz
              _ = incl.app d x := hxy.symm
          · rfl
        · let p := d.unop.obj.len
          have hple : p ≤ m := by
            have hle := @SimplexCategory.len_le_of_mono _ _ y.down.hom y.down.property
            simpa [Henry.SemiSimplexCategory.mk] using hle
          by_cases hpm : p = m
          · have hd : d = op (Henry.SemiSimplexCategory.mk m) := by
              apply congrArg op
              apply WideSubcategory.ext
              calc
                d.unop.obj = SimplexCategory.mk d.unop.obj.len :=
                  (SimplexCategory.mk_len d.unop.obj).symm
                _ = SimplexCategory.mk m := by
                  simpa [p] using congrArg (fun n : ℕ => SimplexCategory.mk n) hpm
            subst d
            have hyId : y = ULift.up (𝟙 (Henry.SemiSimplexCategory.mk m)) := by
              apply ULift.ext
              haveI : Mono y.down.hom := y.down.property
              apply WideSubcategory.hom_ext
              exact SimplexCategory.eq_id_of_mono y.down.hom
            have hxσ : x.1 = σ := by
              have hval := congrArg (fun z : S.toFunctor.obj
                (op (Henry.SemiSimplexCategory.mk m)) => z.1) hxy
              have hval' : x.1 = (smap.app (op (Henry.SemiSimplexCategory.mk m))
                  idM).1 := by
                simpa [incl, Subfunctor.homOfLe, hyId] using hval
              exact hval'.trans hsid
            exact False.elim (x.2.2 rfl hxσ)
          · have hlt : p < m := lt_of_le_of_ne hple hpm
            have hySurj : ¬Function.Surjective y.down.hom.toOrderHom := by
              intro hs
              haveI : Mono y.down.hom := y.down.property
              have hinj := (SimplexCategory.mono_iff_injective).1 (inferInstance : Mono y.down.hom)
              have hcard₁ := Fintype.card_le_of_injective y.down.hom.toOrderHom hinj
              have hcard₂ := Fintype.card_le_of_surjective y.down.hom.toOrderHom hs
              simp only [Fintype.card_fin] at hcard₁ hcard₂
              omega
            have hmissing : ∃ j : Fin (m + 1),
                j ∉ Set.range y.down.hom.toOrderHom := by
              by_contra h
              push_neg at h
              exact hySurj h
            obtain ⟨j, hj⟩ := hmissing
            have hybd : y ∈ (SemiSSet.boundary.{u} m).obj d := ⟨j, hj⟩
            let z : (SemiSSet.boundary.{u} m).toFunctor.obj d := ⟨y, hybd⟩
            refine ⟨z, ?_, ?_⟩
            · have hcommd := congrArg (fun α => α.app d) hcomm
              have hcommz : incl.app d (b.app d z) = smap.app d y := by
                simpa [z] using congrArg (fun f => f z) hcommd
              have hinj : Function.Injective (incl.app d) := by
                rw [← mono_iff_injective]
                infer_instance
              apply hinj
              calc
                incl.app d (b.app d z) = smap.app d y := hcommz
                _ = incl.app d x := hxy.symm
            · rfl
  haveI : Mono (incl.app d) := by infer_instance
  apply Types.isPushout_of_isPullback_of_mono' hpb
  · change Set.range (incl.app d) ∪ Set.range (smap.app d) = Set.univ
    ext x
    simp only [Set.mem_union, Set.mem_range, Set.mem_univ]
    constructor
    · intro _
      trivial
    · intro _
      by_cases hx' : x.1 ∈ (deleteTopSimplex S σ hmax).obj d
      · left
        exact ⟨⟨x.1, hx'⟩, rfl⟩
      · right
        have htop : ∃ h : d = op (Henry.SemiSimplexCategory.mk m), h ▸ x.1 = σ := by
          by_contra hnot
          apply hx'
          refine ⟨x.2, ?_⟩
          intro h heq
          exact hnot ⟨h, heq⟩
        obtain ⟨hd, hσx⟩ := htop
        subst d
        refine ⟨idM, ?_⟩
        apply Subtype.ext
        calc
          (smap.app (op (Henry.SemiSimplexCategory.mk m)) idM).1 = σ := hsid
          _ = x.1 := hσx.symm
  · intro x y _ _ hxy
    exact (simplexMapToSub_app_injective S σ hσ) hxy

theorem exists_topSimplex_pushout_proof {N : ℕ}
    (S : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)))
    (hS : ∃ d, (S.obj d).Nonempty) :
    ∃ (m : ℕ) (S' : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)))
      (hle : S' ≤ S) (b : (SemiSSet.boundary.{u} m).toFunctor ⟶ S'.toFunctor)
      (σ : SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m) ⟶ S.toFunctor),
      IsPushout b (SemiSSet.boundary.{u} m).ι (Subfunctor.homOfLe hle) σ ∧
      HomotopyHypothesis.Realization.SemisimplicialComparison.simplexCount S'.toFunctor N <
        HomotopyHypothesis.Realization.SemisimplicialComparison.simplexCount S.toFunctor N ∧
      HomotopyHypothesis.Realization.SemisimplicialComparison.simplexCount
        (SemiSSet.boundary.{u} m).toFunctor m <
        HomotopyHypothesis.Realization.SemisimplicialComparison.simplexCount S.toFunctor N := by
  obtain ⟨m, hm, σ, hσ, hmax⟩ := exists_maximal_simplex S hS
  let S' := deleteTopSimplex S σ hmax
  have hle : S' ≤ S := deleteTopSimplex_le S σ hmax
  let b := boundaryMapToDeleted S σ hσ hmax
  let sigma := simplexMapToSub S σ hσ
  refine ⟨m, S', hle, b, sigma, ?_, ?_, ?_⟩
  · exact topSimplex_attachment_isPushout S σ hσ hmax
  · exact deleteTopSimplex_count_lt S σ hσ hm hmax
  · exact boundary_count_lt S σ hσ hm

#print axioms exists_topSimplex_pushout_proof

end HomotopyHypothesis.Approximation.TopSimplex
