import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
/-!
# Free algebraic Kan complexes and cell attachments

This file constructs the initial object, free algebraic Kan complexes on semi-simplicial sets, and
free cell attachments in `AlgKan` via an explicit countable stagewise horn-filling construction
without quotients.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra Opposite ConcreteCategory

namespace HomotopyHypothesis.Cylinder.SimplicialCategory

open HomotopyHypothesis.Henry

/-- The `j`-th face map `[n] ⟶ [n + 1]` in `SemiSimplexCategory`. -/
def semiDelta {n : ℕ} (j : Fin (n + 2)) :
    Henry.SemiSimplexCategory.mk n ⟶ Henry.SemiSimplexCategory.mk (n + 1) :=
  ⟨SimplexCategory.δ j, inferInstance⟩

@[simp]
lemma semiDelta_hom {n : ℕ} (j : Fin (n + 2)) :
    (semiDelta j).hom = SimplexCategory.δ j := rfl

lemma not_mem_range_semiDelta {n : ℕ} (j : Fin (n + 2)) :
    j ∉ Set.range (semiDelta j).hom.toOrderHom := by
  rintro ⟨x, hx⟩
  exact Fin.succAbove_ne j x hx

/-- The `j`-th face as an element of `horn (n + 1) k` for `j ≠ k`. -/
def hornFace (n : ℕ) (k : Fin (n + 2)) (j : Fin (n + 2)) (hjk : j ≠ k) :
    (SemiSSet.horn.{u} (n + 1) k).toFunctor.obj (op (Henry.SemiSimplexCategory.mk n)) :=
  ⟨ULift.up (semiDelta j), j, hjk, not_mem_range_semiDelta j⟩

/-- Every simplex of `horn (n + 1) k` is the restriction of `hornFace n k j hjk` for some `j ≠ k`. -/
lemma horn_eq_map_hornFace (n : ℕ) (k : Fin (n + 2)) {Δ : Henry.SemiSimplexCategoryᵒᵖ}
    (s : (SemiSSet.horn.{u} (n + 1) k).toFunctor.obj Δ) :
    ∃ (j : Fin (n + 2)) (hjk : j ≠ k) (g : unop Δ ⟶ Henry.SemiSimplexCategory.mk n),
      s = (SemiSSet.horn.{u} (n + 1) k).toFunctor.map g.op (hornFace n k j hjk) := by
  rcases s with ⟨⟨f⟩, j, hjk, hj⟩
  have hj' : ∀ x, f.hom.toOrderHom x ≠ j := fun x hx => hj ⟨x, hx⟩
  obtain ⟨θ, hθ⟩ := SimplexCategory.eq_comp_δ_of_not_surjective' f.hom j hj'
  have hmono : Mono (θ ≫ SimplexCategory.δ j) := by
    rw [← hθ]
    exact f.property
  have : Mono θ := CategoryTheory.mono_of_mono θ (SimplexCategory.δ j)
  let g : unop Δ ⟶ Henry.SemiSimplexCategory.mk n := ⟨θ, inferInstance⟩
  refine ⟨j, hjk, g, ?_⟩
  apply Subtype.ext
  apply ULift.ext
  apply WideSubcategory.hom_ext
  exact hθ

/-- The identity simplex is not in `horn (n + 1) k`. -/
lemma id_not_mem_horn (n : ℕ) (k : Fin (n + 2)) :
    ULift.up (𝟙 (Henry.SemiSimplexCategory.mk (n + 1))) ∉
      (SemiSSet.horn.{u} (n + 1) k).obj (op (Henry.SemiSimplexCategory.mk (n + 1))) := by
  rintro ⟨j, _, hj⟩
  exact hj ⟨j, rfl⟩

/-- Another element of `Fin (n + 2)` distinct from `k`. -/
def otherFin (n : ℕ) : Fin (n + 2) → Fin (n + 2)
  | ⟨0, _⟩ => ⟨1, by omega⟩
  | ⟨_ + 1, _⟩ => ⟨0, by omega⟩

lemma otherFin_ne (n : ℕ) (k : Fin (n + 2)) : otherFin n k ≠ k := by
  rcases k with ⟨_ | kval, hklt⟩ <;> intro h <;> injection h with h' <;> omega

/-- The empty semi-simplicial set. -/
abbrev emptySemiSSet : SemiSSet.{u} :=
  (Functor.const _).obj PEmpty.{u + 1}

/-- There is no natural transformation from `horn (n + 1) k` to `emptySemiSSet`. -/
theorem hornToEmptyElim {n : ℕ} {k : Fin (n + 2)}
    (h : (SemiSSet.horn.{u} (n + 1) k).toFunctor ⟶ emptySemiSSet.{u}) : False := by
  let s := hornFace.{u} n k (otherFin n k) (otherFin_ne n k)
  exact PEmpty.elim (h.app (op (Henry.SemiSimplexCategory.mk n)) s)

/-- The initial algebraic Kan complex, with empty underlying semi-simplicial set. -/
@[simps]
abbrev emptyAlgKan : AlgKan.{u} where
  X := emptySemiSSet.{u}
  fill _ _ h := (hornToEmptyElim h).elim
  fill_spec _ _ h := (hornToEmptyElim h).elim

/-- Morphism from `emptyAlgKan` to any algebraic Kan complex. -/
def emptyAlgKanTo (Z : AlgKan.{u}) : emptyAlgKan.{u} ⟶ Z where
  hom :=
    { app := fun _ => ↾fun (x : PEmpty.{u + 1}) => PEmpty.elim x
      naturality := fun _ _ _ => by ext (x : PEmpty.{u + 1}); exact PEmpty.elim x }
  fill_hom _ _ h := (hornToEmptyElim h).elim

/-- `emptyAlgKan` is initial in `AlgKan`. -/
def emptyAlgKanIsInitial : IsInitial emptyAlgKan.{u} :=
  IsInitial.ofUniqueHom emptyAlgKanTo (fun Z f => by
    apply AlgKan.Hom.ext
    ext m (x : PEmpty.{u + 1})
    exact PEmpty.elim x)

/-- The initial object of `CDelta`. -/
def initialCDelta : CDelta.{u} :=
  ⟨emptyAlgKan.{u}, AlgKan.IsFinitelyCellular.initial _ ⟨emptyAlgKanIsInitial.{u}⟩⟩

/-- `initialCDelta` is initial in `CDelta`. -/
def initialCDeltaIsInitial : IsInitial initialCDelta.{u} :=
  IsInitial.ofUniqueHom
    (fun Z => ObjectProperty.homMk (emptyAlgKanTo Z.obj))
    (fun Z f => by
      apply ObjectProperty.hom_ext
      apply AlgKan.Hom.ext
      ext m (x : PEmpty.{u + 1})
      exact PEmpty.elim x)

/-!
## Pushout of a subfunctor inclusion in `SemiSSet`
-/

/-- The levelwise pushout type of `S.ι : S.toFunctor ⟶ B` along `a : S.toFunctor ⟶ A`. -/
abbrev PushoutSubfunctorObj (A : SemiSSet.{u}) {B : SemiSSet.{u}} (S : Subfunctor B)
    (Δ : Henry.SemiSimplexCategoryᵒᵖ) : Type u :=
  A.obj Δ ⊕ { y : B.obj Δ // y ∉ S.obj Δ }

/-- The right map `B.obj Δ → PushoutSubfunctorObj A S Δ`. -/
noncomputable def pushoutSubfunctorInrApp (A : SemiSSet.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ A) (Δ : Henry.SemiSimplexCategoryᵒᵖ) (y : B.obj Δ) :
    PushoutSubfunctorObj A S Δ := by
  classical
  exact if hy : y ∈ S.obj Δ then Sum.inl (a.app Δ (⟨y, hy⟩ : S.toFunctor.obj Δ)) else Sum.inr ⟨y, hy⟩

lemma pushoutSubfunctorInrApp_of_mem (A : SemiSSet.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ A) {Δ : Henry.SemiSimplexCategoryᵒᵖ}
    {y : B.obj Δ} (hy : y ∈ S.obj Δ) :
    pushoutSubfunctorInrApp A S a Δ y = Sum.inl (a.app Δ (⟨y, hy⟩ : S.toFunctor.obj Δ)) := by
  dsimp [pushoutSubfunctorInrApp]
  rw [dite_eq_left_of_eq_true (eq_true hy)]

lemma pushoutSubfunctorInrApp_of_not_mem (A : SemiSSet.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ A) {Δ : Henry.SemiSimplexCategoryᵒᵖ}
    {y : B.obj Δ} (hy : y ∉ S.obj Δ) :
    pushoutSubfunctorInrApp A S a Δ y = Sum.inr ⟨y, hy⟩ := by
  dsimp [pushoutSubfunctorInrApp]
  rw [dite_eq_right_of_eq_false (eq_false hy)]

/-- Action on morphisms for `pushoutSubfunctor`. -/
noncomputable def pushoutSubfunctorMap (A : SemiSSet.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ A) {Δ Δ' : Henry.SemiSimplexCategoryᵒᵖ}
    (f : Δ ⟶ Δ') : PushoutSubfunctorObj A S Δ → PushoutSubfunctorObj A S Δ'
  | Sum.inl x₀ => Sum.inl (A.map f x₀)
  | Sum.inr ⟨y, _⟩ => pushoutSubfunctorInrApp A S a Δ' (B.map f y)

/-- The semi-simplicial pushout `A ⊔_S B`. -/
@[simps]
noncomputable abbrev pushoutSubfunctor (A : SemiSSet.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ A) : SemiSSet.{u} where
  obj Δ := PushoutSubfunctorObj A S Δ
  map f := ↾(pushoutSubfunctorMap A S a f)
  map_id Δ := by
    ext x
    rcases x with x₀ | ⟨y, hy⟩
    · change Sum.inl (A.map (𝟙 Δ) x₀) = Sum.inl x₀
      rw [A.map_id_apply]
    · change pushoutSubfunctorInrApp A S a Δ (B.map (𝟙 Δ) y) = Sum.inr ⟨y, hy⟩
      rw [B.map_id_apply, pushoutSubfunctorInrApp_of_not_mem A S a hy]
  map_comp {Δ Δ' Δ''} f g := by
    ext x
    rcases x with x₀ | ⟨y, hy⟩
    · change Sum.inl (A.map (f ≫ g) x₀) = Sum.inl (A.map g (A.map f x₀))
      rw [A.map_comp_apply]
    · change pushoutSubfunctorInrApp A S a Δ'' (B.map (f ≫ g) y) =
        pushoutSubfunctorMap A S a g (pushoutSubfunctorInrApp A S a Δ' (B.map f y))
      rw [B.map_comp_apply]
      by_cases hfy : B.map f y ∈ S.obj Δ'
      · have hgf : B.map g (B.map f y) ∈ S.obj Δ'' := S.map g hfy
        rw [pushoutSubfunctorInrApp_of_mem A S a hfy, pushoutSubfunctorInrApp_of_mem A S a hgf]
        change Sum.inl (a.app Δ'' (⟨B.map g (B.map f y), hgf⟩ : S.toFunctor.obj Δ'')) =
          Sum.inl (A.map g (a.app Δ' (⟨B.map f y, hfy⟩ : S.toFunctor.obj Δ')))
        congr 1
        exact NatTrans.naturality_apply a g (⟨B.map f y, hfy⟩ : S.toFunctor.obj Δ')
      · rw [pushoutSubfunctorInrApp_of_not_mem A S a hfy]
        rfl

/-- The left inclusion `A ⟶ pushoutSubfunctor A S a`. -/
@[simps]
noncomputable abbrev pushoutSubfunctorInl (A : SemiSSet.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ A) : A ⟶ pushoutSubfunctor A S a where
  app _ := ↾Sum.inl
  naturality _ _ _ := rfl

/-- The right morphism `B ⟶ pushoutSubfunctor A S a`. -/
@[simps]
noncomputable abbrev pushoutSubfunctorInr (A : SemiSSet.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ A) : B ⟶ pushoutSubfunctor A S a where
  app Δ := ↾(pushoutSubfunctorInrApp A S a Δ)
  naturality {Δ Δ'} f := by
    ext y
    change pushoutSubfunctorInrApp A S a Δ' (B.map f y) =
      pushoutSubfunctorMap A S a f (pushoutSubfunctorInrApp A S a Δ y)
    by_cases hy : y ∈ S.obj Δ
    · have hfy : B.map f y ∈ S.obj Δ' := S.map f hy
      rw [pushoutSubfunctorInrApp_of_mem A S a hy, pushoutSubfunctorInrApp_of_mem A S a hfy]
      change Sum.inl (a.app Δ' (⟨B.map f y, hfy⟩ : S.toFunctor.obj Δ')) =
        Sum.inl (A.map f (a.app Δ (⟨y, hy⟩ : S.toFunctor.obj Δ)))
      congr 1
      exact NatTrans.naturality_apply a f (⟨y, hy⟩ : S.toFunctor.obj Δ)
    · rw [pushoutSubfunctorInrApp_of_not_mem A S a hy]
      rfl

lemma pushoutSubfunctor_comm (A : SemiSSet.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ A) :
    S.ι ≫ pushoutSubfunctorInr A S a = a ≫ pushoutSubfunctorInl A S a := by
  ext Δ ⟨y, hy⟩
  exact pushoutSubfunctorInrApp_of_mem A S a hy

/-- Action of `pushoutSubfunctorDesc` at `Δ`. -/
def pushoutSubfunctorDescApp (A : SemiSSet.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) {Z : SemiSSet.{u}} (uA : A ⟶ Z) (uB : B ⟶ Z)
    (Δ : Henry.SemiSimplexCategoryᵒᵖ) : PushoutSubfunctorObj A S Δ → Z.obj Δ
  | Sum.inl x₀ => uA.app Δ x₀
  | Sum.inr ⟨y, _⟩ => uB.app Δ y

/-- Universal property of `pushoutSubfunctor`. -/
@[simps]
noncomputable def pushoutSubfunctorDesc (A : SemiSSet.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ A) {Z : SemiSSet.{u}} (uA : A ⟶ Z) (uB : B ⟶ Z)
    (hu : S.ι ≫ uB = a ≫ uA) : pushoutSubfunctor A S a ⟶ Z where
  app Δ := ↾(pushoutSubfunctorDescApp A S uA uB Δ)
  naturality {Δ Δ'} f := by
    ext x
    rcases x with x₀ | ⟨y, hy⟩
    · exact NatTrans.naturality_apply uA f x₀
    · change pushoutSubfunctorDescApp A S uA uB Δ' (pushoutSubfunctorInrApp A S a Δ' (B.map f y)) =
        Z.map f (uB.app Δ y)
      rw [← NatTrans.naturality_apply uB f y]
      by_cases hfy : B.map f y ∈ S.obj Δ'
      · rw [pushoutSubfunctorInrApp_of_mem A S a hfy]
        exact (ConcreteCategory.congr_hom (congr_app hu Δ')
          (⟨B.map f y, hfy⟩ : S.toFunctor.obj Δ')).symm
      · rw [pushoutSubfunctorInrApp_of_not_mem A S a hfy]
        rfl

@[simp]
lemma pushoutSubfunctorInl_desc (A : SemiSSet.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ A) {Z : SemiSSet.{u}} (uA : A ⟶ Z) (uB : B ⟶ Z)
    (hu : S.ι ≫ uB = a ≫ uA) :
    pushoutSubfunctorInl A S a ≫ pushoutSubfunctorDesc A S a uA uB hu = uA := rfl

@[simp]
lemma pushoutSubfunctorInr_desc (A : SemiSSet.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ A) {Z : SemiSSet.{u}} (uA : A ⟶ Z) (uB : B ⟶ Z)
    (hu : S.ι ≫ uB = a ≫ uA) :
    pushoutSubfunctorInr A S a ≫ pushoutSubfunctorDesc A S a uA uB hu = uB := by
  ext Δ y
  change pushoutSubfunctorDescApp A S uA uB Δ (pushoutSubfunctorInrApp A S a Δ y) =
    uB.app Δ y
  by_cases hy : y ∈ S.obj Δ
  · rw [pushoutSubfunctorInrApp_of_mem A S a hy]
    exact (ConcreteCategory.congr_hom (congr_app hu Δ) (⟨y, hy⟩ : S.toFunctor.obj Δ)).symm
  · rw [pushoutSubfunctorInrApp_of_not_mem A S a hy]
    rfl

lemma pushoutSubfunctor_hom_ext (A : SemiSSet.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ A) {Z : SemiSSet.{u}}
    {f₁ f₂ : pushoutSubfunctor A S a ⟶ Z}
    (hl : pushoutSubfunctorInl A S a ≫ f₁ = pushoutSubfunctorInl A S a ≫ f₂)
    (hr : pushoutSubfunctorInr A S a ≫ f₁ = pushoutSubfunctorInr A S a ≫ f₂) :
    f₁ = f₂ := by
  ext Δ x
  rcases x with x₀ | ⟨y, hy⟩
  · exact ConcreteCategory.congr_hom (congr_app hl Δ) x₀
  · have h := ConcreteCategory.congr_hom (congr_app hr Δ) y
    change f₁.app Δ (pushoutSubfunctorInrApp A S a Δ y) =
      f₂.app Δ (pushoutSubfunctorInrApp A S a Δ y) at h
    rwa [pushoutSubfunctorInrApp_of_not_mem A S a hy] at h

/-!
## Countable stagewise horn completion
-/

/-- A step in the stagewise horn completion, storing the previous stage, current stage,
and the inclusion between them. -/
structure StageStep where
  prev : SemiSSet.{u}
  curr : SemiSSet.{u}
  inc : prev ⟶ curr

/-- Horns in `st.curr` that do not factor through `st.inc : st.prev ⟶ st.curr`. -/
def NewHorn (st : StageStep.{u}) (n : ℕ) (k : Fin (n + 2)) : Type u :=
  { h : (SemiSSet.horn.{u} (n + 1) k).toFunctor ⟶ st.curr //
    ¬ ∃ h₀ : (SemiSSet.horn.{u} (n + 1) k).toFunctor ⟶ st.prev, h₀ ≫ st.inc = h }

/-- Simplices added to `st.curr` at `Δ` to fill all new horns of `st`. -/
structure AddedCell (st : StageStep.{u}) (Δ : Henry.SemiSimplexCategoryᵒᵖ) : Type u where
  n : ℕ
  k : Fin (n + 2)
  h : NewHorn st n k
  y : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk (n + 1))).obj Δ
  hy : y ∉ (SemiSSet.horn.{u} (n + 1) k).obj Δ

/-- Levelwise object of the next stage. -/
abbrev NextStageObj (st : StageStep.{u}) (Δ : Henry.SemiSimplexCategoryᵒᵖ) : Type u :=
  st.curr.obj Δ ⊕ AddedCell st Δ

/-- The filler map at `Δ` for a new horn `h : NewHorn st n k`. -/
noncomputable def nextStageFillApp (st : StageStep.{u}) {n : ℕ} {k : Fin (n + 2)}
    (h : NewHorn st n k) (Δ : Henry.SemiSimplexCategoryᵒᵖ)
    (y : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk (n + 1))).obj Δ) :
    NextStageObj st Δ := by
  classical
  exact if hy : y ∈ (SemiSSet.horn.{u} (n + 1) k).obj Δ then
    Sum.inl (h.val.app Δ (⟨y, hy⟩ : (SemiSSet.horn.{u} (n + 1) k).toFunctor.obj Δ))
  else
    Sum.inr ⟨n, k, h, y, hy⟩

lemma nextStageFillApp_of_mem (st : StageStep.{u}) {n : ℕ} {k : Fin (n + 2)}
    (h : NewHorn st n k) {Δ : Henry.SemiSimplexCategoryᵒᵖ}
    {y : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk (n + 1))).obj Δ}
    (hy : y ∈ (SemiSSet.horn.{u} (n + 1) k).obj Δ) :
    nextStageFillApp st h Δ y =
      Sum.inl (h.val.app Δ (⟨y, hy⟩ : (SemiSSet.horn.{u} (n + 1) k).toFunctor.obj Δ)) := by
  dsimp [nextStageFillApp]
  rw [dite_eq_left_of_eq_true (eq_true hy)]

lemma nextStageFillApp_of_not_mem (st : StageStep.{u}) {n : ℕ} {k : Fin (n + 2)}
    (h : NewHorn st n k) {Δ : Henry.SemiSimplexCategoryᵒᵖ}
    {y : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk (n + 1))).obj Δ}
    (hy : y ∉ (SemiSSet.horn.{u} (n + 1) k).obj Δ) :
    nextStageFillApp st h Δ y = Sum.inr ⟨n, k, h, y, hy⟩ := by
  dsimp [nextStageFillApp]
  rw [dite_eq_right_of_eq_false (eq_false hy)]

/-- Action of a morphism `f : Δ ⟶ Δ'` on an `AddedCell st Δ`. -/
noncomputable def addedCellMap (st : StageStep.{u}) {Δ Δ' : Henry.SemiSimplexCategoryᵒᵖ}
    (f : Δ ⟶ Δ') (c : AddedCell st Δ) : NextStageObj st Δ' :=
  nextStageFillApp st c.h Δ'
    ((SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk (c.n + 1))).map f c.y)

/-- Map on morphisms for the next stage. -/
noncomputable def nextStageMap (st : StageStep.{u}) {Δ Δ' : Henry.SemiSimplexCategoryᵒᵖ}
    (f : Δ ⟶ Δ') : NextStageObj st Δ → NextStageObj st Δ'
  | Sum.inl x => Sum.inl (st.curr.map f x)
  | Sum.inr c => addedCellMap st f c

/-- The next stage semi-simplicial set. -/
@[simps]
noncomputable abbrev nextStageCurr (st : StageStep.{u}) : SemiSSet.{u} where
  obj Δ := NextStageObj st Δ
  map f := ↾(nextStageMap st f)
  map_id Δ := by
    ext x
    rcases x with x₀ | ⟨n, k, h, y, hy⟩
    · change Sum.inl (st.curr.map (𝟙 Δ) x₀) = Sum.inl x₀
      rw [st.curr.map_id_apply]
    · change nextStageFillApp st h Δ
        ((SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk (n + 1))).map (𝟙 Δ) y) =
        Sum.inr ⟨n, k, h, y, hy⟩
      rw [(SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk (n + 1))).map_id_apply,
        nextStageFillApp_of_not_mem st h hy]
  map_comp {Δ Δ' Δ''} f g := by
    ext x
    rcases x with x₀ | ⟨n, k, h, y, hy⟩
    · change Sum.inl (st.curr.map (f ≫ g) x₀) = Sum.inl (st.curr.map g (st.curr.map f x₀))
      rw [st.curr.map_comp_apply]
    · let F := SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk (n + 1))
      let H := SemiSSet.horn.{u} (n + 1) k
      change nextStageFillApp st h Δ'' (F.map (f ≫ g) y) =
        nextStageMap st g (nextStageFillApp st h Δ' (F.map f y))
      rw [F.map_comp_apply]
      by_cases hfy : F.map f y ∈ H.obj Δ'
      · have hgf : F.map g (F.map f y) ∈ H.obj Δ'' := H.map g hfy
        rw [nextStageFillApp_of_mem st h hfy, nextStageFillApp_of_mem st h hgf]
        change Sum.inl (h.val.app Δ'' (⟨F.map g (F.map f y), hgf⟩ : H.toFunctor.obj Δ'')) =
          Sum.inl (st.curr.map g (h.val.app Δ' (⟨F.map f y, hfy⟩ : H.toFunctor.obj Δ')))
        congr 1
        exact NatTrans.naturality_apply h.val g (⟨F.map f y, hfy⟩ : H.toFunctor.obj Δ')
      · rw [nextStageFillApp_of_not_mem st h hfy]
        rfl

/-- The inclusion `st.curr ⟶ nextStageCurr st`. -/
@[simps]
noncomputable abbrev nextStageInc (st : StageStep.{u}) : st.curr ⟶ nextStageCurr st where
  app _ := ↾Sum.inl
  naturality _ _ _ := rfl

/-- The filler morphism `Δ_{n+1} ⟶ nextStageCurr st` for a new horn `h : NewHorn st n k`. -/
@[simps]
noncomputable def nextStageFill (st : StageStep.{u}) {n : ℕ} {k : Fin (n + 2)}
    (h : NewHorn st n k) :
    SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk (n + 1)) ⟶ nextStageCurr st where
  app Δ := ↾(nextStageFillApp st h Δ)
  naturality {Δ Δ'} f := by
    ext y
    let F := SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk (n + 1))
    let H := SemiSSet.horn.{u} (n + 1) k
    change nextStageFillApp st h Δ' (F.map f y) = nextStageMap st f (nextStageFillApp st h Δ y)
    by_cases hy : y ∈ H.obj Δ
    · have hfy : F.map f y ∈ H.obj Δ' := H.map f hy
      rw [nextStageFillApp_of_mem st h hy, nextStageFillApp_of_mem st h hfy]
      change Sum.inl (h.val.app Δ' (⟨F.map f y, hfy⟩ : H.toFunctor.obj Δ')) =
        Sum.inl (st.curr.map f (h.val.app Δ (⟨y, hy⟩ : H.toFunctor.obj Δ)))
      congr 1
      exact NatTrans.naturality_apply h.val f (⟨y, hy⟩ : H.toFunctor.obj Δ)
    · rw [nextStageFillApp_of_not_mem st h hy]
      rfl

@[simp]
lemma horn_ι_comp_nextStageFill (st : StageStep.{u}) {n : ℕ} {k : Fin (n + 2)}
    (h : NewHorn st n k) :
    (SemiSSet.horn.{u} (n + 1) k).ι ≫ nextStageFill st h = h.val ≫ nextStageInc st := by
  ext Δ ⟨y, hy⟩
  exact nextStageFillApp_of_mem st h hy

/-- Action at `Δ` of the induced map `nextStageCurr st ⟶ Z.X` extending `d : st.curr ⟶ Z.X`. -/
def nextStageDescApp (st : StageStep.{u}) {Z : AlgKan.{u}} (d : st.curr ⟶ Z.X)
    (Δ : Henry.SemiSimplexCategoryᵒᵖ) : NextStageObj st Δ → Z.X.obj Δ
  | Sum.inl x => d.app Δ x
  | Sum.inr c => (Z.fill c.n c.k (c.h.val ≫ d)).app Δ c.y

/-- Extension of `d : st.curr ⟶ Z.X` to `nextStageCurr st ⟶ Z.X` using the chosen fillers of `Z`. -/
@[simps]
noncomputable def nextStageDesc (st : StageStep.{u}) {Z : AlgKan.{u}} (d : st.curr ⟶ Z.X) :
    nextStageCurr st ⟶ Z.X where
  app Δ := ↾(nextStageDescApp st d Δ)
  naturality {Δ Δ'} f := by
    ext x
    rcases x with x₀ | ⟨n, k, h, y, hy⟩
    · exact NatTrans.naturality_apply d f x₀
    · let F := SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk (n + 1))
      let H := SemiSSet.horn.{u} (n + 1) k
      change nextStageDescApp st d Δ' (nextStageFillApp st h Δ' (F.map f y)) =
        Z.X.map f ((Z.fill n k (h.val ≫ d)).app Δ y)
      rw [← NatTrans.naturality_apply (Z.fill n k (h.val ≫ d)) f y]
      by_cases hfy : F.map f y ∈ H.obj Δ'
      · rw [nextStageFillApp_of_mem st h hfy]
        change (h.val ≫ d).app Δ' ⟨F.map f y, hfy⟩ =
          (Z.fill n k (h.val ≫ d)).app Δ' (F.map f y)
        exact (ConcreteCategory.congr_hom
          (congr_app (Z.fill_spec n k (h.val ≫ d)) Δ') ⟨F.map f y, hfy⟩).symm
      · rw [nextStageFillApp_of_not_mem st h hfy]
        rfl

@[simp]
lemma nextStageInc_comp_nextStageDesc (st : StageStep.{u}) {Z : AlgKan.{u}} (d : st.curr ⟶ Z.X) :
    nextStageInc st ≫ nextStageDesc st d = d := rfl

@[simp]
lemma nextStageFill_comp_nextStageDesc (st : StageStep.{u}) {Z : AlgKan.{u}} (d : st.curr ⟶ Z.X)
    {n : ℕ} {k : Fin (n + 2)} (h : NewHorn st n k) :
    nextStageFill st h ≫ nextStageDesc st d = Z.fill n k (h.val ≫ d) := by
  ext Δ y
  change nextStageDescApp st d Δ (nextStageFillApp st h Δ y) =
    (Z.fill n k (h.val ≫ d)).app Δ y
  by_cases hy : y ∈ (SemiSSet.horn.{u} (n + 1) k).obj Δ
  · rw [nextStageFillApp_of_mem st h hy]
    exact (ConcreteCategory.congr_hom
      (congr_app (Z.fill_spec n k (h.val ≫ d)) Δ) ⟨y, hy⟩).symm
  · rw [nextStageFillApp_of_not_mem st h hy]
    rfl

/-- The next `StageStep`. -/
@[simps]
noncomputable abbrev nextStageStep (st : StageStep.{u}) : StageStep.{u} where
  prev := st.curr
  curr := nextStageCurr st
  inc := nextStageInc st

/-!
## Iterated stages and colimit `stageInf`
-/

/-- The base step `(X.X, pushoutSubfunctor X.X S a, pushoutSubfunctorInl X.X S a)`. -/
@[simps]
noncomputable abbrev baseStageStep (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) : StageStep.{u} where
  prev := X.X
  curr := pushoutSubfunctor X.X S a
  inc := pushoutSubfunctorInl X.X S a

/-- The sequence of stages for attaching `B` along `S` to `X`. -/
noncomputable def stageSeq (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) : ℕ → StageStep.{u}
  | 0 => baseStageStep X S a
  | r + 1 => nextStageStep (stageSeq X S a r)

/-- The step inclusion `(stageSeq X S a r).curr ⟶ (stageSeq X S a (r + 1)).curr` with syntactically
aligned domain and codomain. -/
noncomputable def stageSeqInc (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) (r : ℕ) :
    (stageSeq X S a r).curr ⟶ (stageSeq X S a (r + 1)).curr :=
  (stageSeq X S a (r + 1)).inc

/-- The left inclusion `X.X ⟶ (stageSeq X S a 0).curr` with syntactically aligned codomain. -/
noncomputable def stageSeqInl (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) :
    X.X ⟶ (stageSeq X S a 0).curr :=
  pushoutSubfunctorInl X.X S a

/-- The right morphism `B ⟶ (stageSeq X S a 0).curr` with syntactically aligned codomain. -/
noncomputable def stageSeqInr (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) :
    B ⟶ (stageSeq X S a 0).curr :=
  pushoutSubfunctorInr X.X S a

/-- The filler morphism `Δ_{n+1} ⟶ (stageSeq X S a (r + 1)).curr` with syntactically aligned
codomain. -/
noncomputable def stageSeqFill (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) (r : ℕ) {n : ℕ} {k : Fin (n + 2)}
    (h : NewHorn (stageSeq X S a r) n k) :
    SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk (n + 1)) ⟶
      (stageSeq X S a (r + 1)).curr :=
  nextStageFill (stageSeq X S a r) h

@[simp]
lemma horn_ι_comp_stageSeqFill (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) (r : ℕ) {n : ℕ} {k : Fin (n + 2)}
    (h : NewHorn (stageSeq X S a r) n k) :
    (SemiSSet.horn.{u} (n + 1) k).ι ≫ stageSeqFill X S a r h = h.val ≫ stageSeqInc X S a r :=
  horn_ι_comp_nextStageFill (stageSeq X S a r) h

/-- Levelwise type of the colimit `stageInf X S a` at `Δ`. -/
abbrev StageInfObj (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) (Δ : Henry.SemiSimplexCategoryᵒᵖ) : Type u :=
  (stageSeq X S a 0).curr.obj Δ ⊕ Σ r : ℕ, AddedCell (stageSeq X S a r) Δ

/-- Levelwise inclusion `(stageSeq X S a r).curr.obj Δ → StageInfObj X S a Δ`. -/
def toInfApp (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) :
    ∀ (r : ℕ) (Δ : Henry.SemiSimplexCategoryᵒᵖ),
      (stageSeq X S a r).curr.obj Δ → StageInfObj X S a Δ
  | 0, _, x => Sum.inl x
  | r + 1, Δ, Sum.inl x => toInfApp X S a r Δ x
  | r + 1, _, Sum.inr c => Sum.inr ⟨r, c⟩

/-- Action on morphisms for `stageInf X S a`. -/
noncomputable def stageInfMap (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) {Δ Δ' : Henry.SemiSimplexCategoryᵒᵖ}
    (f : Δ ⟶ Δ') : StageInfObj X S a Δ → StageInfObj X S a Δ'
  | Sum.inl x => Sum.inl ((stageSeq X S a 0).curr.map f x)
  | Sum.inr ⟨r, c⟩ => toInfApp X S a (r + 1) Δ' (addedCellMap (stageSeq X S a r) f c)

lemma stageInfMap_toInfApp (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) (r : ℕ) {Δ Δ' : Henry.SemiSimplexCategoryᵒᵖ}
    (f : Δ ⟶ Δ') (x : (stageSeq X S a r).curr.obj Δ) :
    stageInfMap X S a f (toInfApp X S a r Δ x) =
      toInfApp X S a r Δ' ((stageSeq X S a r).curr.map f x) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rcases x with x₀ | c
    · exact ih x₀
    · rfl

/-- The colimit semi-simplicial set `stageInf X S a`. -/
@[simps]
noncomputable abbrev stageInf (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) : SemiSSet.{u} where
  obj Δ := StageInfObj X S a Δ
  map f := ↾(stageInfMap X S a f)
  map_id Δ := by
    ext z
    rcases z with x | ⟨r, c⟩
    · change stageInfMap X S a (𝟙 Δ) (toInfApp X S a 0 Δ x) = toInfApp X S a 0 Δ x
      rw [stageInfMap_toInfApp, (stageSeq X S a 0).curr.map_id_apply]
    · let c' : (stageSeq X S a (r + 1)).curr.obj Δ := Sum.inr c
      change stageInfMap X S a (𝟙 Δ) (toInfApp X S a (r + 1) Δ c') =
        toInfApp X S a (r + 1) Δ c'
      rw [stageInfMap_toInfApp, (stageSeq X S a (r + 1)).curr.map_id_apply]
  map_comp {Δ Δ' Δ''} f g := by
    ext z
    rcases z with x | ⟨r, c⟩
    · change stageInfMap X S a (f ≫ g) (toInfApp X S a 0 Δ x) =
        stageInfMap X S a g (stageInfMap X S a f (toInfApp X S a 0 Δ x))
      rw [stageInfMap_toInfApp, (stageSeq X S a 0).curr.map_comp_apply,
        stageInfMap_toInfApp, stageInfMap_toInfApp]
    · let c' : (stageSeq X S a (r + 1)).curr.obj Δ := Sum.inr c
      change stageInfMap X S a (f ≫ g) (toInfApp X S a (r + 1) Δ c') =
        stageInfMap X S a g (stageInfMap X S a f (toInfApp X S a (r + 1) Δ c'))
      rw [stageInfMap_toInfApp, (stageSeq X S a (r + 1)).curr.map_comp_apply,
        stageInfMap_toInfApp, stageInfMap_toInfApp]

/-- Canonical morphism `(stageSeq X S a r).curr ⟶ stageInf X S a`. -/
@[simps]
noncomputable def toInf (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) (r : ℕ) :
    (stageSeq X S a r).curr ⟶ stageInf X S a where
  app Δ := ↾(toInfApp X S a r Δ)
  naturality {_ _} f := by
    ext x
    exact (stageInfMap_toInfApp X S a r f x).symm

@[simp]
lemma stageSeqInc_comp_toInf (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) (r : ℕ) :
    stageSeqInc X S a r ≫ toInf X S a (r + 1) = toInf X S a r := rfl

/-- The stage at which a simplex of `stageInf X S a` is born. -/
def birthStage (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) {Δ : Henry.SemiSimplexCategoryᵒᵖ} :
    StageInfObj X S a Δ → ℕ
  | Sum.inl _ => 0
  | Sum.inr ⟨r, _⟩ => r + 1

lemma birthStage_toInfApp (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) (r : ℕ) {Δ : Henry.SemiSimplexCategoryᵒᵖ}
    (x : (stageSeq X S a r).curr.obj Δ) :
    birthStage X S a (toInfApp X S a r Δ x) ≤ r := by
  induction r with
  | zero => exact le_rfl
  | succ r ih =>
    rcases x with x₀ | c
    · exact le_trans (ih x₀) (Nat.le_succ r)
    · exact le_rfl

/-- Partial inverse of `toInfApp` on simplices of `birthStage ≤ r`. -/
def ofInfApp (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) :
    ∀ (r : ℕ) {Δ : Henry.SemiSimplexCategoryᵒᵖ} (z : StageInfObj X S a Δ),
      birthStage X S a z ≤ r → (stageSeq X S a r).curr.obj Δ
  | 0, _, Sum.inl x, _ => x
  | 0, _, Sum.inr ⟨r', _⟩, hz => by
      exfalso
      change r' + 1 ≤ 0 at hz
      omega
  | r + 1, _, Sum.inl x, _ =>
      Sum.inl (ofInfApp X S a r (Sum.inl x) (Nat.zero_le r))
  | r + 1, _, Sum.inr ⟨r', c⟩, hz =>
      if hr : r' = r then
        Sum.inr (hr ▸ c)
      else
        Sum.inl (ofInfApp X S a r (Sum.inr ⟨r', c⟩) (by
          change r' + 1 ≤ r + 1 at hz
          change r' + 1 ≤ r
          omega))

@[simp]
lemma toInfApp_ofInfApp (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) (r : ℕ) {Δ : Henry.SemiSimplexCategoryᵒᵖ}
    (z : StageInfObj X S a Δ) (hz : birthStage X S a z ≤ r) :
    toInfApp X S a r Δ (ofInfApp X S a r z hz) = z := by
  induction r generalizing z with
  | zero =>
    rcases z with x | ⟨r', c⟩
    · rfl
    · change r' + 1 ≤ 0 at hz; omega
  | succ r ih =>
    rcases z with x | ⟨r', c⟩
    · exact ih (Sum.inl x) (Nat.zero_le r)
    · by_cases hr : r' = r
      · subst hr
        have hite : ofInfApp X S a (r' + 1) (Sum.inr ⟨r', c⟩) hz =
            (Sum.inr c : (stageSeq X S a (r' + 1)).curr.obj Δ) := by
          dsimp [ofInfApp]
          exact dite_eq_left_of_eq_true (eq_true rfl)
        rw [hite]
        rfl
      · have hite : ofInfApp X S a (r + 1) (Sum.inr ⟨r', c⟩) hz =
            (Sum.inl (ofInfApp X S a r (Sum.inr ⟨r', c⟩) (by
              change r' + 1 ≤ r + 1 at hz
              change r' + 1 ≤ r
              omega)) : (stageSeq X S a (r + 1)).curr.obj Δ) := by
          dsimp [ofInfApp]
          exact dite_eq_right_of_eq_false (eq_false hr)
        rw [hite]
        exact ih (Sum.inr ⟨r', c⟩) _

lemma toInfApp_injective (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) (r : ℕ) (Δ : Henry.SemiSimplexCategoryᵒᵖ) :
    Function.Injective (toInfApp X S a r Δ) := by
  induction r with
  | zero =>
    intro x₁ x₂ h
    exact Sum.inl.inj h
  | succ r ih =>
    intro x₁ x₂ h
    rcases x₁ with x₁ | c₁ <;> rcases x₂ with x₂ | c₂
    · exact congrArg Sum.inl (ih h)
    · exfalso
      have hle := birthStage_toInfApp X S a r x₁
      change toInfApp X S a r Δ x₁ = Sum.inr ⟨r, c₂⟩ at h
      rw [h] at hle
      change r + 1 ≤ r at hle
      omega
    · exfalso
      have hle := birthStage_toInfApp X S a r x₂
      change Sum.inr ⟨r, c₁⟩ = toInfApp X S a r Δ x₂ at h
      rw [← h] at hle
      change r + 1 ≤ r at hle
      omega
    · have h' : (⟨r, c₁⟩ : Σ r', AddedCell (stageSeq X S a r') Δ) = ⟨r, c₂⟩ := Sum.inr.inj h
      exact congrArg Sum.inr (eq_of_heq (Sigma.mk.inj h').2)

lemma toInf_mono (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) (r : ℕ) {W : SemiSSet.{u}}
    {f₁ f₂ : W ⟶ (stageSeq X S a r).curr}
    (h : f₁ ≫ toInf X S a r = f₂ ≫ toInf X S a r) : f₁ = f₂ := by
  ext Δ w
  apply toInfApp_injective X S a r Δ
  exact ConcreteCategory.congr_hom (congr_app h Δ) w

lemma birthStage_stageInfMap_le (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) {Δ Δ' : Henry.SemiSimplexCategoryᵒᵖ}
    (f : Δ ⟶ Δ') (z : StageInfObj X S a Δ) :
    birthStage X S a (stageInfMap X S a f z) ≤ birthStage X S a z := by
  let r := birthStage X S a z
  have hz : toInfApp X S a r Δ (ofInfApp X S a r z le_rfl) = z :=
    toInfApp_ofInfApp X S a r z le_rfl
  conv_lhs => rw [← hz, stageInfMap_toInfApp]
  exact birthStage_toInfApp X S a r _

/-!
## Horn lifting and the algebraic Kan structure on `stageInf`
-/

/-- Canonical inclusion `(stageSeq X S a 0).curr ⟶ (stageSeq X S a r).curr`. -/
noncomputable def zeroToStage (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) :
    ∀ r : ℕ, (stageSeq X S a 0).curr ⟶ (stageSeq X S a r).curr
  | 0 => 𝟙 _
  | r + 1 => zeroToStage X S a r ≫ stageSeqInc X S a r

@[simp]
lemma zeroToStage_comp_toInf (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) (r : ℕ) :
    zeroToStage X S a r ≫ toInf X S a r = toInf X S a 0 := by
  induction r with
  | zero => exact Category.id_comp _
  | succ r ih =>
    dsimp [zeroToStage]
    rw [Category.assoc, stageSeqInc_comp_toInf, ih]

/-- The birth stage of a horn `h : Λ^{n+1}_k ⟶ stageInf X S a`, defined as the supremum of the
birth stages of its `n + 1` generating faces. -/
def hornStage (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) {n : ℕ} {k : Fin (n + 2)}
    (h : (SemiSSet.horn.{u} (n + 1) k).toFunctor ⟶ stageInf X S a) : ℕ :=
  Finset.univ.sup (fun j : { j : Fin (n + 2) // j ≠ k } =>
    birthStage X S a (h.app (op (Henry.SemiSimplexCategory.mk n)) (hornFace n k j.1 j.2)))

lemma birthStage_horn_le (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) {n : ℕ} {k : Fin (n + 2)}
    (h : (SemiSSet.horn.{u} (n + 1) k).toFunctor ⟶ stageInf X S a)
    {Δ : Henry.SemiSimplexCategoryᵒᵖ}
    (s : (SemiSSet.horn.{u} (n + 1) k).toFunctor.obj Δ) :
    birthStage X S a (h.app Δ s) ≤ hornStage X S a h := by
  obtain ⟨j, hjk, g, rfl⟩ := horn_eq_map_hornFace n k s
  have hnat := NatTrans.naturality_apply h g.op (hornFace n k j hjk)
  rw [hnat]
  exact le_trans (birthStage_stageInfMap_le X S a g.op _)
    (Finset.le_sup (f := fun j : { j : Fin (n + 2) // j ≠ k } =>
      birthStage X S a (h.app (op (Henry.SemiSimplexCategory.mk n)) (hornFace n k j.1 j.2)))
      (Finset.mem_univ (⟨j, hjk⟩ : { j : Fin (n + 2) // j ≠ k })))

/-- Lifting a horn `h : Λ^{n+1}_k ⟶ stageInf X S a` to `(stageSeq X S a r).curr` whenever
`hornStage X S a h ≤ r`. -/
@[simps]
noncomputable def liftHorn (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) (r : ℕ) {n : ℕ} {k : Fin (n + 2)}
    (h : (SemiSSet.horn.{u} (n + 1) k).toFunctor ⟶ stageInf X S a)
    (hr : hornStage X S a h ≤ r) :
    (SemiSSet.horn.{u} (n + 1) k).toFunctor ⟶ (stageSeq X S a r).curr where
  app Δ := ↾fun s => ofInfApp X S a r (h.app Δ s) (le_trans (birthStage_horn_le X S a h s) hr)
  naturality {Δ Δ'} f := by
    ext s
    apply toInfApp_injective X S a r Δ'
    let s' := (SemiSSet.horn.{u} (n + 1) k).toFunctor.map f s
    change toInfApp X S a r Δ' (ofInfApp X S a r (h.app Δ' s') _) =
      toInfApp X S a r Δ' ((stageSeq X S a r).curr.map f (ofInfApp X S a r (h.app Δ s) _))
    rw [toInfApp_ofInfApp, ← stageInfMap_toInfApp, toInfApp_ofInfApp]
    exact NatTrans.naturality_apply h f s

@[simp]
lemma liftHorn_comp_toInf (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) (r : ℕ) {n : ℕ} {k : Fin (n + 2)}
    (h : (SemiSSet.horn.{u} (n + 1) k).toFunctor ⟶ stageInf X S a)
    (hr : hornStage X S a h ≤ r) :
    liftHorn X S a r h hr ≫ toInf X S a r = h := by
  ext Δ s
  exact toInfApp_ofInfApp X S a r (h.app Δ s) _

/-- A horn in `stageInf X S a` is a base horn if it factors through `X.X`. -/
abbrev IsBaseHorn (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) {n : ℕ} {k : Fin (n + 2)}
    (h : (SemiSSet.horn.{u} (n + 1) k).toFunctor ⟶ stageInf X S a) : Prop :=
  ∃ hX : (SemiSSet.horn.{u} (n + 1) k).toFunctor ⟶ X.X,
    hX ≫ stageSeqInl X S a ≫ toInf X S a 0 = h

lemma baseHorn_unique (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) {n : ℕ} {k : Fin (n + 2)}
    {h₁ h₂ : (SemiSSet.horn.{u} (n + 1) k).toFunctor ⟶ X.X}
    (heq : h₁ ≫ stageSeqInl X S a ≫ toInf X S a 0 =
      h₂ ≫ stageSeqInl X S a ≫ toInf X S a 0) :
    h₁ = h₂ := by
  have heq' : h₁ ≫ stageSeqInl X S a = h₂ ≫ stageSeqInl X S a := by
    apply toInf_mono X S a 0
    rw [Category.assoc, Category.assoc]
    exact heq
  ext Δ s
  exact Sum.inl.inj (ConcreteCategory.congr_hom (congr_app heq' Δ) s)

lemma hornStage_comp_toInf_le (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) (r : ℕ) {n : ℕ} {k : Fin (n + 2)}
    (h₀ : (SemiSSet.horn.{u} (n + 1) k).toFunctor ⟶ (stageSeq X S a r).curr) :
    hornStage X S a (h₀ ≫ toInf X S a r) ≤ r := by
  apply Finset.sup_le
  intro j _
  exact birthStage_toInfApp X S a r _

lemma liftHorn_not_prev_of_not_isBaseHorn_aux (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) {n : ℕ} {k : Fin (n + 2)}
    (h : (SemiSSet.horn.{u} (n + 1) k).toFunctor ⟶ stageInf X S a)
    (hnot : ¬ IsBaseHorn X S a h) (r : ℕ) (hr : hornStage X S a h ≤ r)
    (heq : hornStage X S a h = r) :
    ¬ ∃ h₀ : (SemiSSet.horn.{u} (n + 1) k).toFunctor ⟶ (stageSeq X S a r).prev,
      h₀ ≫ (stageSeq X S a r).inc = liftHorn X S a r h hr := by
  rintro ⟨h₀, hh₀⟩
  cases r with
  | zero =>
    apply hnot
    let h₀_base : (SemiSSet.horn.{u} (n + 1) k).toFunctor ⟶ X.X := h₀
    refine ⟨h₀_base, ?_⟩
    have hh₀' : h₀_base ≫ stageSeqInl X S a = liftHorn X S a 0 h hr := hh₀
    calc
      h₀_base ≫ stageSeqInl X S a ≫ toInf X S a 0
        = (h₀_base ≫ stageSeqInl X S a) ≫ toInf X S a 0 := (Category.assoc _ _ _).symm
      _ = liftHorn X S a 0 h hr ≫ toInf X S a 0 := by rw [hh₀']
      _ = h := liftHorn_comp_toInf X S a 0 h hr
  | succ r =>
    let h₀_curr : (SemiSSet.horn.{u} (n + 1) k).toFunctor ⟶ (stageSeq X S a r).curr := h₀
    have hh₀' : h₀_curr ≫ stageSeqInc X S a r = liftHorn X S a (r + 1) h hr := hh₀
    have hh : h₀_curr ≫ toInf X S a r = h := by
      calc
        h₀_curr ≫ toInf X S a r
          = (h₀_curr ≫ stageSeqInc X S a r) ≫ toInf X S a (r + 1) := by
              rw [Category.assoc, stageSeqInc_comp_toInf]
        _ = liftHorn X S a (r + 1) h hr ≫ toInf X S a (r + 1) := by rw [hh₀']
        _ = h := liftHorn_comp_toInf X S a (r + 1) h hr
    have hle : hornStage X S a h ≤ r := by
      rw [← hh]
      exact hornStage_comp_toInf_le X S a r h₀_curr
    omega

lemma liftHorn_not_prev_of_not_isBaseHorn (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) {n : ℕ} {k : Fin (n + 2)}
    (h : (SemiSSet.horn.{u} (n + 1) k).toFunctor ⟶ stageInf X S a)
    (hnot : ¬ IsBaseHorn X S a h) :
    ¬ ∃ h₀ : (SemiSSet.horn.{u} (n + 1) k).toFunctor ⟶
        (stageSeq X S a (hornStage X S a h)).prev,
      h₀ ≫ (stageSeq X S a (hornStage X S a h)).inc =
        liftHorn X S a (hornStage X S a h) h le_rfl :=
  liftHorn_not_prev_of_not_isBaseHorn_aux X S a h hnot (hornStage X S a h) le_rfl rfl

/-- The new horn at stage `hornStage X S a h` associated to a non-base horn `h`. -/
noncomputable def toNewHorn (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) {n : ℕ} {k : Fin (n + 2)}
    (h : (SemiSSet.horn.{u} (n + 1) k).toFunctor ⟶ stageInf X S a)
    (hnot : ¬ IsBaseHorn X S a h) :
    NewHorn (stageSeq X S a (hornStage X S a h)) n k :=
  ⟨liftHorn X S a (hornStage X S a h) h le_rfl,
    liftHorn_not_prev_of_not_isBaseHorn X S a h hnot⟩

/-- Chosen horn fillers for `stageInf X S a`. -/
noncomputable def stageInfFill (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) (n : ℕ) (k : Fin (n + 2))
    (h : (SemiSSet.horn.{u} (n + 1) k).toFunctor ⟶ stageInf X S a) :
    SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk (n + 1)) ⟶ stageInf X S a := by
  classical
  exact if hbase : IsBaseHorn X S a h then
    X.fill n k hbase.choose ≫ stageSeqInl X S a ≫ toInf X S a 0
  else
    stageSeqFill X S a (hornStage X S a h) (toNewHorn X S a h hbase) ≫
      toInf X S a (hornStage X S a h + 1)

lemma stageInfFill_of_isBaseHorn (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) (n : ℕ) (k : Fin (n + 2))
    (h : (SemiSSet.horn.{u} (n + 1) k).toFunctor ⟶ stageInf X S a)
    (hbase : IsBaseHorn X S a h) :
    stageInfFill X S a n k h =
      X.fill n k hbase.choose ≫ stageSeqInl X S a ≫ toInf X S a 0 := by
  dsimp [stageInfFill]
  rw [dite_eq_left_of_eq_true (eq_true hbase)]

lemma stageInfFill_of_not_isBaseHorn (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) (n : ℕ) (k : Fin (n + 2))
    (h : (SemiSSet.horn.{u} (n + 1) k).toFunctor ⟶ stageInf X S a)
    (hnot : ¬ IsBaseHorn X S a h) :
    stageInfFill X S a n k h =
      stageSeqFill X S a (hornStage X S a h) (toNewHorn X S a h hnot) ≫
        toInf X S a (hornStage X S a h + 1) := by
  dsimp [stageInfFill]
  rw [dite_eq_right_of_eq_false (eq_false hnot)]

lemma stageInfFill_spec (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) (n : ℕ) (k : Fin (n + 2))
    (h : (SemiSSet.horn.{u} (n + 1) k).toFunctor ⟶ stageInf X S a) :
    (SemiSSet.horn.{u} (n + 1) k).ι ≫ stageInfFill X S a n k h = h := by
  by_cases hbase : IsBaseHorn X S a h
  · rw [stageInfFill_of_isBaseHorn X S a n k h hbase, ← Category.assoc, X.fill_spec]
    exact hbase.choose_spec
  · rw [stageInfFill_of_not_isBaseHorn X S a n k h hbase, ← Category.assoc,
      horn_ι_comp_stageSeqFill, Category.assoc, stageSeqInc_comp_toInf]
    exact liftHorn_comp_toInf X S a (hornStage X S a h) h le_rfl

/-- The algebraic Kan complex obtained by freely attaching `B` along `S.ι : S.toFunctor ⟶ B`
via `a : S.toFunctor ⟶ X.X`. -/
@[simps]
noncomputable abbrev attachSubfunctor (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) : AlgKan.{u} where
  X := stageInf X S a
  fill := stageInfFill X S a
  fill_spec := stageInfFill_spec X S a

/-- The left inclusion `X ⟶ attachSubfunctor X S a` in `AlgKan`. -/
@[simps]
noncomputable abbrev attachSubfunctorInl (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) : X ⟶ attachSubfunctor X S a where
  hom := stageSeqInl X S a ≫ toInf X S a 0
  fill_hom n k h := by
    have hbase : IsBaseHorn X S a (h ≫ stageSeqInl X S a ≫ toInf X S a 0) := ⟨h, rfl⟩
    change X.fill n k h ≫ stageSeqInl X S a ≫ toInf X S a 0 =
      stageInfFill X S a n k (h ≫ stageSeqInl X S a ≫ toInf X S a 0)
    rw [stageInfFill_of_isBaseHorn X S a n k _ hbase]
    have heq : hbase.choose = h := baseHorn_unique X S a hbase.choose_spec
    rw [heq]

/-- The right semi-simplicial morphism `B ⟶ (attachSubfunctor X S a).X`. -/
noncomputable abbrev attachSubfunctorInr (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) : B ⟶ (attachSubfunctor X S a).X :=
  stageSeqInr X S a ≫ toInf X S a 0

lemma stageSeq_comm (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) :
    S.ι ≫ stageSeqInr X S a = a ≫ stageSeqInl X S a :=
  pushoutSubfunctor_comm X.X S a

lemma attachSubfunctor_comm (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) :
    S.ι ≫ attachSubfunctorInr X S a = a ≫ (attachSubfunctorInl X S a).hom := by
  change S.ι ≫ stageSeqInr X S a ≫ toInf X S a 0 = a ≫ stageSeqInl X S a ≫ toInf X S a 0
  rw [← Category.assoc, stageSeq_comm, Category.assoc]

/-!
## Universal property of `attachSubfunctor`
-/

/-- Stagewise extension of `(uX, uB)` to `(stageSeq X S a r).curr ⟶ Z.X`. -/
noncomputable def descStage (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) {Z : AlgKan.{u}}
    (uX : X ⟶ Z) (uB : B ⟶ Z.X) (hu : S.ι ≫ uB = a ≫ uX.hom) :
    ∀ r : ℕ, (stageSeq X S a r).curr ⟶ Z.X
  | 0 => pushoutSubfunctorDesc X.X S a uX.hom uB hu
  | r + 1 => nextStageDesc (stageSeq X S a r) (descStage X S a uX uB hu r)

@[simp]
lemma stageSeqInc_comp_descStage (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) {Z : AlgKan.{u}}
    (uX : X ⟶ Z) (uB : B ⟶ Z.X) (hu : S.ι ≫ uB = a ≫ uX.hom) (r : ℕ) :
    stageSeqInc X S a r ≫ descStage X S a uX uB hu (r + 1) =
      descStage X S a uX uB hu r := rfl

@[simp]
lemma stageSeqFill_comp_descStage (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) {Z : AlgKan.{u}}
    (uX : X ⟶ Z) (uB : B ⟶ Z.X) (hu : S.ι ≫ uB = a ≫ uX.hom)
    (r : ℕ) {n : ℕ} {k : Fin (n + 2)} (h : NewHorn (stageSeq X S a r) n k) :
    stageSeqFill X S a r h ≫ descStage X S a uX uB hu (r + 1) =
      Z.fill n k (h.val ≫ descStage X S a uX uB hu r) :=
  nextStageFill_comp_nextStageDesc (stageSeq X S a r) (descStage X S a uX uB hu r) h

@[simp]
lemma stageSeqInl_comp_descStage_zero (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) {Z : AlgKan.{u}}
    (uX : X ⟶ Z) (uB : B ⟶ Z.X) (hu : S.ι ≫ uB = a ≫ uX.hom) :
    stageSeqInl X S a ≫ descStage X S a uX uB hu 0 = uX.hom := rfl

@[simp]
lemma stageSeqInr_comp_descStage_zero (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) {Z : AlgKan.{u}}
    (uX : X ⟶ Z) (uB : B ⟶ Z.X) (hu : S.ι ≫ uB = a ≫ uX.hom) :
    stageSeqInr X S a ≫ descStage X S a uX uB hu 0 = uB :=
  pushoutSubfunctorInr_desc X.X S a uX.hom uB hu

/-- Levelwise map `StageInfObj X S a Δ → Z.X.obj Δ`. -/
noncomputable def stageInfDescApp (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) {Z : AlgKan.{u}}
    (uX : X ⟶ Z) (uB : B ⟶ Z.X) (hu : S.ι ≫ uB = a ≫ uX.hom)
    (Δ : Henry.SemiSimplexCategoryᵒᵖ) : StageInfObj X S a Δ → Z.X.obj Δ
  | Sum.inl x => (descStage X S a uX uB hu 0).app Δ x
  | Sum.inr ⟨r, c⟩ =>
      let c' : (stageSeq X S a (r + 1)).curr.obj Δ := Sum.inr c
      (descStage X S a uX uB hu (r + 1)).app Δ c'

lemma stageInfDescApp_toInfApp (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) {Z : AlgKan.{u}}
    (uX : X ⟶ Z) (uB : B ⟶ Z.X) (hu : S.ι ≫ uB = a ≫ uX.hom)
    (r : ℕ) (Δ : Henry.SemiSimplexCategoryᵒᵖ) (x : (stageSeq X S a r).curr.obj Δ) :
    stageInfDescApp X S a uX uB hu Δ (toInfApp X S a r Δ x) =
      (descStage X S a uX uB hu r).app Δ x := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rcases x with x₀ | c
    · exact ih x₀
    · rfl

/-- The induced semi-simplicial morphism `stageInf X S a ⟶ Z.X`. -/
@[simps]
noncomputable def stageInfDescHom (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) {Z : AlgKan.{u}}
    (uX : X ⟶ Z) (uB : B ⟶ Z.X) (hu : S.ι ≫ uB = a ≫ uX.hom) :
    stageInf X S a ⟶ Z.X where
  app Δ := ↾(stageInfDescApp X S a uX uB hu Δ)
  naturality {Δ Δ'} f := by
    ext z
    rcases z with x | ⟨r, c⟩
    · change stageInfDescApp X S a uX uB hu Δ'
        (stageInfMap X S a f (toInfApp X S a 0 Δ x)) =
        Z.X.map f (stageInfDescApp X S a uX uB hu Δ (toInfApp X S a 0 Δ x))
      rw [stageInfMap_toInfApp, stageInfDescApp_toInfApp, stageInfDescApp_toInfApp]
      exact NatTrans.naturality_apply (descStage X S a uX uB hu 0) f x
    · let c' : (stageSeq X S a (r + 1)).curr.obj Δ := Sum.inr c
      change stageInfDescApp X S a uX uB hu Δ'
        (stageInfMap X S a f (toInfApp X S a (r + 1) Δ c')) =
        Z.X.map f (stageInfDescApp X S a uX uB hu Δ (toInfApp X S a (r + 1) Δ c'))
      rw [stageInfMap_toInfApp, stageInfDescApp_toInfApp, stageInfDescApp_toInfApp]
      exact NatTrans.naturality_apply (descStage X S a uX uB hu (r + 1)) f c'

@[simp]
lemma toInf_comp_stageInfDescHom (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) {Z : AlgKan.{u}}
    (uX : X ⟶ Z) (uB : B ⟶ Z.X) (hu : S.ι ≫ uB = a ≫ uX.hom) (r : ℕ) :
    toInf X S a r ≫ stageInfDescHom X S a uX uB hu = descStage X S a uX uB hu r := by
  ext Δ x
  exact stageInfDescApp_toInfApp X S a uX uB hu r Δ x

/-- Universal morphism `attachSubfunctor X S a ⟶ Z` in `AlgKan`. -/
@[simps]
noncomputable def attachSubfunctorDesc (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) {Z : AlgKan.{u}}
    (uX : X ⟶ Z) (uB : B ⟶ Z.X) (hu : S.ι ≫ uB = a ≫ uX.hom) :
    attachSubfunctor X S a ⟶ Z where
  hom := stageInfDescHom X S a uX uB hu
  fill_hom n k h := by
    change stageInfFill X S a n k h ≫ stageInfDescHom X S a uX uB hu =
      Z.fill n k (h ≫ stageInfDescHom X S a uX uB hu)
    by_cases hbase : IsBaseHorn X S a h
    · rw [stageInfFill_of_isBaseHorn X S a n k h hbase, Category.assoc, Category.assoc,
        toInf_comp_stageInfDescHom, stageSeqInl_comp_descStage_zero, uX.fill_hom]
      congr 1
      calc
        hbase.choose ≫ uX.hom
          = hbase.choose ≫ stageSeqInl X S a ≫ descStage X S a uX uB hu 0 := by
              rw [stageSeqInl_comp_descStage_zero]
        _ = (hbase.choose ≫ stageSeqInl X S a ≫ toInf X S a 0) ≫
              stageInfDescHom X S a uX uB hu := by
              rw [Category.assoc, Category.assoc, toInf_comp_stageInfDescHom]
        _ = h ≫ stageInfDescHom X S a uX uB hu := by rw [hbase.choose_spec]
    · rw [stageInfFill_of_not_isBaseHorn X S a n k h hbase, Category.assoc,
        toInf_comp_stageInfDescHom, stageSeqFill_comp_descStage]
      congr 1
      calc
        (toNewHorn X S a h hbase).val ≫ descStage X S a uX uB hu (hornStage X S a h)
          = (liftHorn X S a (hornStage X S a h) h le_rfl ≫ toInf X S a (hornStage X S a h)) ≫
              stageInfDescHom X S a uX uB hu := by
              rw [Category.assoc, toInf_comp_stageInfDescHom]; rfl
        _ = h ≫ stageInfDescHom X S a uX uB hu := by rw [liftHorn_comp_toInf]

@[simp]
lemma attachSubfunctorInl_desc (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) {Z : AlgKan.{u}}
    (uX : X ⟶ Z) (uB : B ⟶ Z.X) (hu : S.ι ≫ uB = a ≫ uX.hom) :
    attachSubfunctorInl X S a ≫ attachSubfunctorDesc X S a uX uB hu = uX := by
  apply AlgKan.Hom.ext
  change (stageSeqInl X S a ≫ toInf X S a 0) ≫ stageInfDescHom X S a uX uB hu = uX.hom
  rw [Category.assoc, toInf_comp_stageInfDescHom, stageSeqInl_comp_descStage_zero]

@[simp]
lemma attachSubfunctorInr_desc (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) {Z : AlgKan.{u}}
    (uX : X ⟶ Z) (uB : B ⟶ Z.X) (hu : S.ι ≫ uB = a ≫ uX.hom) :
    attachSubfunctorInr X S a ≫ (attachSubfunctorDesc X S a uX uB hu).hom = uB := by
  change (stageSeqInr X S a ≫ toInf X S a 0) ≫ stageInfDescHom X S a uX uB hu = uB
  rw [Category.assoc, toInf_comp_stageInfDescHom, stageSeqInr_comp_descStage_zero]

lemma newHorn_not_isBaseHorn (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) (r : ℕ) {n : ℕ} {k : Fin (n + 2)}
    (h' : NewHorn (stageSeq X S a r) n k) :
    ¬ IsBaseHorn X S a (h'.val ≫ toInf X S a r) := by
  rintro ⟨hX, hhX⟩
  cases r with
  | zero =>
    apply h'.property
    refine ⟨hX, ?_⟩
    apply toInf_mono X S a 0
    rw [← Category.assoc] at hhX
    exact hhX
  | succ r =>
    apply h'.property
    refine ⟨hX ≫ stageSeqInl X S a ≫ zeroToStage X S a r, ?_⟩
    apply toInf_mono X S a (r + 1)
    change ((hX ≫ stageSeqInl X S a ≫ zeroToStage X S a r) ≫ stageSeqInc X S a r) ≫
      toInf X S a (r + 1) = h'.val ≫ toInf X S a (r + 1)
    rw [Category.assoc, Category.assoc, Category.assoc, stageSeqInc_comp_toInf,
      zeroToStage_comp_toInf]
    exact hhX

lemma hornStage_newHorn_eq (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) (r : ℕ) {n : ℕ} {k : Fin (n + 2)}
    (h' : NewHorn (stageSeq X S a r) n k) :
    hornStage X S a (h'.val ≫ toInf X S a r) = r := by
  have hle : hornStage X S a (h'.val ≫ toInf X S a r) ≤ r :=
    hornStage_comp_toInf_le X S a r h'.val
  cases r with
  | zero => omega
  | succ r =>
    by_contra hne
    have hlt : hornStage X S a (h'.val ≫ toInf X S a (r + 1)) ≤ r := by omega
    apply h'.property
    refine ⟨liftHorn X S a r (h'.val ≫ toInf X S a (r + 1)) hlt, ?_⟩
    apply toInf_mono X S a (r + 1)
    change (liftHorn X S a r (h'.val ≫ toInf X S a (r + 1)) hlt ≫ stageSeqInc X S a r) ≫
      toInf X S a (r + 1) = h'.val ≫ toInf X S a (r + 1)
    rw [Category.assoc, stageSeqInc_comp_toInf, liftHorn_comp_toInf]

lemma stageSeqFill_liftHorn_eq (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) (r : ℕ) {n : ℕ} {k : Fin (n + 2)}
    (h' : NewHorn (stageSeq X S a r) n k)
    (m : ℕ) (hm_eq : m = r)
    (hm : hornStage X S a (h'.val ≫ toInf X S a r) ≤ m)
    (hnotm : ¬ ∃ h₀ : (SemiSSet.horn.{u} (n + 1) k).toFunctor ⟶ (stageSeq X S a m).prev,
      h₀ ≫ (stageSeq X S a m).inc = liftHorn X S a m (h'.val ≫ toInf X S a r) hm) :
    stageSeqFill X S a m ⟨liftHorn X S a m (h'.val ≫ toInf X S a r) hm, hnotm⟩ ≫
      toInf X S a (m + 1) =
    stageSeqFill X S a r h' ≫ toInf X S a (r + 1) := by
  subst hm_eq
  congr 1
  congr 1
  apply Subtype.ext
  apply toInf_mono X S a m
  exact liftHorn_comp_toInf X S a m (h'.val ≫ toInf X S a m) hm

lemma attachSubfunctor_hom_ext (X : AlgKan.{u}) {B : SemiSSet.{u}}
    (S : Subfunctor B) (a : S.toFunctor ⟶ X.X) {Z : AlgKan.{u}}
    {g₁ g₂ : attachSubfunctor X S a ⟶ Z}
    (hl : attachSubfunctorInl X S a ≫ g₁ = attachSubfunctorInl X S a ≫ g₂)
    (hr : attachSubfunctorInr X S a ≫ g₁.hom = attachSubfunctorInr X S a ≫ g₂.hom) :
    g₁ = g₂ := by
  suffices hstage : ∀ r : ℕ, toInf X S a r ≫ g₁.hom = toInf X S a r ≫ g₂.hom by
    apply AlgKan.Hom.ext
    ext Δ z
    rcases z with x | ⟨r, c⟩
    · exact ConcreteCategory.congr_hom (congr_app (hstage 0) Δ) x
    · let c' : (stageSeq X S a (r + 1)).curr.obj Δ := Sum.inr c
      exact ConcreteCategory.congr_hom (congr_app (hstage (r + 1)) Δ) c'
  intro r
  induction r with
  | zero =>
    apply pushoutSubfunctor_hom_ext X.X S a
    · have hl' : (stageSeqInl X S a ≫ toInf X S a 0) ≫ g₁.hom =
          (stageSeqInl X S a ≫ toInf X S a 0) ≫ g₂.hom := congrArg AlgKan.Hom.hom hl
      rw [Category.assoc, Category.assoc] at hl'
      exact hl'
    · have hr' : (stageSeqInr X S a ≫ toInf X S a 0) ≫ g₁.hom =
          (stageSeqInr X S a ≫ toInf X S a 0) ≫ g₂.hom := hr
      rw [Category.assoc, Category.assoc] at hr'
      exact hr'
  | succ r ih =>
    ext Δ x
    rcases x with x₀ | ⟨n, k, h', y, hy⟩
    · exact ConcreteCategory.congr_hom (congr_app ih Δ) x₀
    · let h := h'.val ≫ toInf X S a r
      have hnot : ¬ IsBaseHorn X S a h := newHorn_not_isBaseHorn X S a r h'
      have hst : hornStage X S a h = r := hornStage_newHorn_eq X S a r h'
      have hfill : (attachSubfunctor X S a).fill n k h =
          stageSeqFill X S a r h' ≫ toInf X S a (r + 1) := by
        change stageInfFill X S a n k h = _
        rw [stageInfFill_of_not_isBaseHorn X S a n k h hnot]
        exact stageSeqFill_liftHorn_eq X S a r h' (hornStage X S a h) hst le_rfl
          (liftHorn_not_prev_of_not_isBaseHorn X S a h hnot)
      let c' : (stageSeq X S a (r + 1)).curr.obj Δ := Sum.inr ⟨n, k, h', y, hy⟩
      have hcell : (toInf X S a (r + 1)).app Δ c' =
          ((attachSubfunctor X S a).fill n k h).app Δ y := by
        rw [hfill]
        change (toInf X S a (r + 1)).app Δ c' =
          (toInf X S a (r + 1)).app Δ (nextStageFillApp (stageSeq X S a r) h' Δ y)
        rw [nextStageFillApp_of_not_mem (stageSeq X S a r) h' hy]
      change g₁.hom.app Δ ((toInf X S a (r + 1)).app Δ c') =
        g₂.hom.app Δ ((toInf X S a (r + 1)).app Δ c')
      rw [hcell]
      change ((attachSubfunctor X S a).fill n k h ≫ g₁.hom).app Δ y =
        ((attachSubfunctor X S a).fill n k h ≫ g₂.hom).app Δ y
      rw [g₁.fill_hom, g₂.fill_hom]
      have hcomp : h ≫ g₁.hom = h ≫ g₂.hom := by
        dsimp [h]
        rw [Category.assoc, Category.assoc, ih]
      rw [hcomp]

/-- `attachSubfunctorInl X (boundary n) a` is a free cell attachment in `AlgKan`. -/
lemma attachSubfunctor_isCellAttachment (X : AlgKan.{u}) (n : ℕ)
    (a : (SemiSSet.boundary.{u} n).toFunctor ⟶ X.X) :
    AlgKan.IsCellAttachment (attachSubfunctorInl X (SemiSSet.boundary.{u} n) a) := by
  refine ⟨n, a, attachSubfunctorInr X (SemiSSet.boundary.{u} n) a,
    attachSubfunctor_comm X (SemiSSet.boundary.{u} n) a, ?_⟩
  intro Z g z hz
  refine ⟨attachSubfunctorDesc X (SemiSSet.boundary.{u} n) a g z hz,
    ⟨attachSubfunctorInl_desc X (SemiSSet.boundary.{u} n) a g z hz,
     attachSubfunctorInr_desc X (SemiSSet.boundary.{u} n) a g z hz⟩, ?_⟩
  rintro g' ⟨hgl, hgr⟩
  apply attachSubfunctor_hom_ext X (SemiSSet.boundary.{u} n) a
  · rw [hgl, attachSubfunctorInl_desc]
  · rw [hgr, attachSubfunctorInr_desc]

/-- Every boundary map `∂Δ_n ⟶ X.X` admits a free cell attachment in `AlgKan`. -/
theorem exists_cellAttachment (X : AlgKan.{u}) (n : ℕ)
    (a : (SemiSSet.boundary.{u} n).toFunctor ⟶ X.X) :
    ∃ (Y : AlgKan.{u}) (j : X ⟶ Y), AlgKan.IsCellAttachment j :=
  ⟨attachSubfunctor X (SemiSSet.boundary.{u} n) a,
   attachSubfunctorInl X (SemiSSet.boundary.{u} n) a,
   attachSubfunctor_isCellAttachment X n a⟩

/-!
## Free algebraic Kan complex on a semi-simplicial set
-/

/-- The empty subfunctor of a semi-simplicial set `B`. -/
def botSubfunctor (B : SemiSSet.{u}) : Subfunctor B where
  obj _ := ∅
  map _ _ h := False.elim h

/-- The unique morphism `(botSubfunctor B).toFunctor ⟶ emptyAlgKan.X`. -/
def botSubfunctorToEmpty (B : SemiSSet.{u}) :
    (botSubfunctor B).toFunctor ⟶ emptyAlgKan.{u}.X where
  app _ := ↾fun x => False.elim x.2
  naturality _ _ _ := by ext x; exact False.elim x.2

/-- The free algebraic Kan complex on a semi-simplicial set `B`. -/
noncomputable abbrev freeAlgKan (B : SemiSSet.{u}) : AlgKan.{u} :=
  attachSubfunctor emptyAlgKan.{u} (botSubfunctor B) (botSubfunctorToEmpty B)

/-- The universal semi-simplicial map `B ⟶ (freeAlgKan B).X`. -/
noncomputable abbrev freeAlgKanUnit (B : SemiSSet.{u}) : B ⟶ (freeAlgKan B).X :=
  attachSubfunctorInr emptyAlgKan.{u} (botSubfunctor B) (botSubfunctorToEmpty B)

/-- `freeAlgKan B` is freely generated by `freeAlgKanUnit B`. -/
theorem freeAlgKan_isFreeOn (B : SemiSSet.{u}) :
    (freeAlgKan B).IsFreeOn (freeAlgKanUnit B) := by
  intro Z z
  have hu : (botSubfunctor B).ι ≫ z = botSubfunctorToEmpty B ≫ (emptyAlgKanTo Z).hom := by
    ext Δ x
    exact False.elim x.2
  refine ⟨attachSubfunctorDesc emptyAlgKan.{u} (botSubfunctor B)
    (botSubfunctorToEmpty B) (emptyAlgKanTo Z) z hu,
    attachSubfunctorInr_desc emptyAlgKan.{u} (botSubfunctor B)
      (botSubfunctorToEmpty B) (emptyAlgKanTo Z) z hu, ?_⟩
  intro g hg
  apply attachSubfunctor_hom_ext emptyAlgKan.{u} (botSubfunctor B) (botSubfunctorToEmpty B)
  · exact emptyAlgKanIsInitial.hom_ext _ _
  · rw [hg, attachSubfunctorInr_desc]

/-!
## Pushouts of cell attachments in `AlgKan`
-/

/-- Pushing out a cell attachment `j : X ⟶ Y` along any morphism `f : X ⟶ X'` in `AlgKan`
yields a cell attachment `j' : X' ⟶ Y'` and a pushout square `IsPushout j f f' j'` in `AlgKan`. -/
theorem exists_pushout_of_isCellAttachment {X Y X' : AlgKan.{u}} (j : X ⟶ Y)
    (hj : AlgKan.IsCellAttachment j) (f : X ⟶ X') :
    ∃ (Y' : AlgKan.{u}) (j' : X' ⟶ Y') (f' : Y ⟶ Y'),
      AlgKan.IsCellAttachment j' ∧ IsPushout j f f' j' := by
  rcases hj with ⟨n, a, y, hcomm, huniv⟩
  let Y' := attachSubfunctor X' (SemiSSet.boundary.{u} n) (a ≫ f.hom)
  let j' : X' ⟶ Y' := attachSubfunctorInl X' (SemiSSet.boundary.{u} n) (a ≫ f.hom)
  let y' := attachSubfunctorInr X' (SemiSSet.boundary.{u} n) (a ≫ f.hom)
  have hcomm' : (SemiSSet.boundary.{u} n).ι ≫ y' = a ≫ (f ≫ j').hom := by
    rw [attachSubfunctor_comm]
    rfl
  obtain ⟨f', ⟨hf'l, hf'r⟩, hf'uniq⟩ := huniv Y' (f ≫ j') y' hcomm'
  refine ⟨Y', j', f', attachSubfunctor_isCellAttachment X' n (a ≫ f.hom), ?_⟩
  refine IsPushout.of_isColimit (PushoutCocone.IsColimit.mk hf'l
    (fun s => by
      have hs : (SemiSSet.boundary.{u} n).ι ≫ (y ≫ s.inl.hom) = (a ≫ f.hom) ≫ s.inr.hom := by
        rw [← Category.assoc, hcomm, Category.assoc, Category.assoc]
        change a ≫ (j ≫ s.inl).hom = a ≫ (f ≫ s.inr).hom
        rw [s.condition]
      exact attachSubfunctorDesc X' (SemiSSet.boundary.{u} n) (a ≫ f.hom) s.inr (y ≫ s.inl.hom) hs)
    (fun s => by
      let d := attachSubfunctorDesc X' (SemiSSet.boundary.{u} n) (a ≫ f.hom) s.inr (y ≫ s.inl.hom)
        (by
          rw [← Category.assoc, hcomm, Category.assoc, Category.assoc]
          change a ≫ (j ≫ s.inl).hom = a ≫ (f ≫ s.inr).hom
          rw [s.condition])
      obtain ⟨g₀, _, hg₀⟩ := huniv s.pt (j ≫ s.inl) (y ≫ s.inl.hom)
        (by rw [← Category.assoc, hcomm, Category.assoc]; rfl)
      have h1 : f' ≫ d = g₀ := by
        apply hg₀
        refine ⟨?_, ?_⟩
        · rw [← Category.assoc, hf'l, Category.assoc]
          rw [attachSubfunctorInl_desc, s.condition]
        · change (y ≫ f'.hom) ≫ d.hom = y ≫ s.inl.hom
          rw [hf'r]
          exact attachSubfunctorInr_desc _ _ _ _ _ _
      have h2 : s.inl = g₀ := hg₀ s.inl ⟨rfl, rfl⟩
      exact h1.trans h2.symm)
    (fun s => attachSubfunctorInl_desc _ _ _ _ _ _)
    (fun s m hml hmr => by
      apply attachSubfunctor_hom_ext X' (SemiSSet.boundary.{u} n) (a ≫ f.hom)
      · rw [hmr, attachSubfunctorInl_desc]
      · rw [attachSubfunctorInr_desc, ← hml]
        exact (congrArg (· ≫ m.hom) hf'r.symm).trans (Category.assoc y f'.hom m.hom)))

end HomotopyHypothesis.Cylinder.SimplicialCategory
