import HomotopyHypothesis.Cylinder.SimplicialCategory.Cofibrations
import HomotopyHypothesis.Cylinder.SimplicialCategory.FreeAlgKan
import HomotopyHypothesis.Cylinder.SimplicialCategory.HornFiltration
import HomotopyHypothesis.Cylinder.SimplicialCategory.HornRealization
import HomotopyHypothesis.Cylinder.SimplicialCategory.SimplexContractions
import HomotopyHypothesis.Cylinder.SimplicialCategory.SimplexRealization
import HomotopyHypothesis.Cylinder.SimplicialCategory.SimplexSubfunctors
import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
/-!
# Inductive simplex and horn retraction lifting along pre-fibrations

This file develops the inductive machinery to lift the standard cosimplicial diagram
`stdCosimplicialUpTo` and the canonical horn retractions `canonicalHornRetraction` from `CDelta`
along a lifting target `p : X ⥤ Y` (`IsLiftingTarget false X Y p`) over a cylinder morphism
`h : CDelta ⥤ Y`.

## Main definitions and results
* `CosimplicialUpTo.extend`: extends `D : CosimplicialUpTo C M` to `CosimplicialUpTo C (M + 1)`
  given a realization `Q_bd` of `∂Δ_{M+1}` along `D` and a morphism `i_succ : Q_bd.pt ⟶ X_succ`.
* `freeCDeltaRealization`: realizes any `F : SemiSSet` with `HasDimLe M F` and finitely cellular
  `freeAlgKan F` along `stdCosimplicialUpTo M` in `CDelta`.
* `stdCosimplicialBoundaryData`: boundary realization data for `stdCosimplicialUpTo M` in `CDelta`.
* `isUniversalCocone_mapFunctor_freeCDeltaCocone`: any cofibration morphism `G : CDelta ⥤ C'` into a
  cofibration category `C'` preserves all subfunctor realizations of `Δ_N`.
* `liftedCosimplicialUpTo`: inductively lifts `stdCosimplicialUpTo M` along `p : X ⥤ Y` together
  with `CosimplicialBoundaryData`, weak equivalence contractions `D.obj k ⟶ x₀`, and preservation
  of boundary realizations by `p`.
* `exists_liftedHornRetraction`: lifts the canonical horn retractions `Δ_{n+1} ⟶ Λ^{n+1}_k` along
  `p : X ⥤ Y` over `h : CDelta ⥤ Y`.
-/

universe v₃ u₃ v₂ u₂ u

open CategoryTheory Limits HomotopicalAlgebra Opposite ConcreteCategory

namespace HomotopyHypothesis.Cylinder.SimplicialCategory

open HomotopyHypothesis.Henry

/-!
## Diagram change helpers for `SimplicialRealization` and `IsUniversalCocone`
-/

section DiagramChangeHelpers

variable {C : Type u₂} [Category.{v₂} C]

/-- Push a `DiagramIsoOn` forward along a functor `G : C ⥤ C'`. -/
@[simps]
def DiagramIsoOn.mapFunctor {C' : Type u₃} [Category.{v₃} C'] (G : C ⥤ C')
    {M M₁ M₂ : ℕ} {h₁ : M ≤ M₁} {h₂ : M ≤ M₂}
    {D₁ : CosimplicialUpTo C M₁} {D₂ : CosimplicialUpTo C M₂}
    (Φ : DiagramIsoOn M h₁ h₂ D₁ D₂) :
    DiagramIsoOn M h₁ h₂ (D₁.mapFunctor G) (D₂.mapFunctor G) where
  iso k hk := G.mapIso (Φ.iso k hk)
  naturality hk hm g := by
    change G.map (D₁.map hk (hm.trans h₁) g) ≫ G.map (Φ.iso _ hm).hom =
      G.map (Φ.iso _ (hk.trans hm)).hom ≫ G.map (D₂.map hk (hm.trans h₂) g)
    rw [← G.map_comp, ← G.map_comp, Φ.naturality hk hm g]

/-- Preservation of `IsUniversalCocone` under `changeDiagram` and `mapFunctor`. -/
lemma isUniversalCocone_mapFunctor_changeDiagram
    {C' : Type u₃} [Category.{v₃} C'] (G : C ⥤ C')
    {M M₁ M₂ : ℕ} {h₁ : M ≤ M₁} {h₂ : M ≤ M₂}
    {D₁ : CosimplicialUpTo C M₁} {D₂ : CosimplicialUpTo C M₂}
    (Φ : DiagramIsoOn M h₁ h₂ D₁ D₂) {F : SemiSSet.{u}} (hF : HasDimLe M F)
    (Q₁ : SimplicialRealization D₁ F)
    (hG₁ : IsUniversalCocone (Q₁.cocone.mapFunctor G)) :
    IsUniversalCocone (((Q₁.changeDiagram Φ hF).cocone).mapFunctor G) := by
  let QG₁ : SimplicialRealization (D₁.mapFunctor G) F := hG₁.toRealization
  let QG₂ : SimplicialRealization (D₂.mapFunctor G) F :=
    QG₁.changeDiagram (Φ.mapFunctor G) hF
  have heq : ((Q₁.changeDiagram Φ hF).cocone).mapFunctor G = QG₂.cocone := by
    ext k hk x
    exact G.map_comp (Φ.iso k (hF x)).inv (Q₁.cocone.ι k ((hF x).trans h₁) x)
  rw [heq]
  exact QG₂.isUniversal

/-- Compatibility of `realizationMap` into `stdSimplexRealization` under `changeDiagram`. -/
lemma SimplicialRealization.realizationMap_changeDiagram_stdSimplex
    {M M₁ M₂ : ℕ} {h₁ : M ≤ M₁} {h₂ : M ≤ M₂}
    {D₁ : CosimplicialUpTo C M₁} {D₂ : CosimplicialUpTo C M₂}
    (Φ : DiagramIsoOn M h₁ h₂ D₁ D₂) {F : SemiSSet.{u}} (hF : HasDimLe M F)
    (Q₁ : SimplicialRealization D₁ F) {m : ℕ} (hm : m ≤ M)
    (α : F ⟶ SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m)) :
    SimplicialRealization.realizationMap (Q₁.changeDiagram Φ hF)
      (stdSimplexRealization D₂ m (hm.trans h₂)) α =
    SimplicialRealization.realizationMap Q₁
      (stdSimplexRealization D₁ m (hm.trans h₁)) α ≫ (Φ.iso m hm).hom := by
  apply (Q₁.changeDiagram Φ hF).hom_ext
  intro k hk₂ x
  have h1 := SimplicialRealization.ι_realizationMap (Q₁.changeDiagram Φ hF)
    (stdSimplexRealization D₂ m (hm.trans h₂)) α k hk₂ x
  have h2 := SimplicialRealization.ι_realizationMap Q₁
    (stdSimplexRealization D₁ m (hm.trans h₁)) α k ((hF x).trans h₁) x
  let a := (Φ.iso k (hF x)).inv
  let b := Q₁.cocone.ι k ((hF x).trans h₁) x
  let c := SimplicialRealization.realizationMap Q₁ (stdSimplexRealization D₁ m (hm.trans h₁)) α
  let d := (Φ.iso m hm).hom
  have h3 : (a ≫ b) ≫ (c ≫ d) = a ≫ (b ≫ c) ≫ d :=
    (Category.assoc a b (c ≫ d)).trans (congrArg (a ≫ ·) (Category.assoc b c d).symm)
  have h4 : a ≫ (b ≫ c) ≫ d =
      a ≫ (stdSimplexRealization D₁ m (hm.trans h₁)).cocone.ι k ((hF x).trans h₁)
        (α.app (op (Henry.SemiSimplexCategory.mk k)) x) ≫ d :=
    congrArg (fun u => a ≫ u ≫ d) h2
  refine h1.trans (Eq.symm ((h3.trans h4).trans ?_))
  have hk_le_m : k ≤ m := len_le_of_hom (ULift.down (α.app (op (Henry.SemiSimplexCategory.mk k)) x))
  change (Φ.iso k (hF x)).inv ≫
      D₁.map hk_le_m (hm.trans h₁) (ULift.down (α.app (op (Henry.SemiSimplexCategory.mk k)) x)) ≫
      (Φ.iso m hm).hom =
    D₂.map hk_le_m (hm.trans h₂) (ULift.down (α.app (op (Henry.SemiSimplexCategory.mk k)) x))
  rw [Φ.naturality hk_le_m hm (ULift.down (α.app (op (Henry.SemiSimplexCategory.mk k)) x)),
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Canonical comparison isomorphism `G.obj Q₁.pt ≅ Q₂.pt` when `G` preserves `Q₁` and `D₁.mapFunctor G`
is isomorphic on `≤ M` to `D₂`. -/
noncomputable def liftedRealizationIso
    {C' : Type u₃} [Category.{v₃} C'] (G : C ⥤ C')
    {M M₁ M₂ : ℕ} {h₁ : M ≤ M₁} {h₂ : M ≤ M₂}
    {D₁ : CosimplicialUpTo C M₁} {D₂ : CosimplicialUpTo C' M₂}
    (Φ : DiagramIsoOn M h₁ h₂ (D₁.mapFunctor G) D₂)
    {F : SemiSSet.{u}} (hF : HasDimLe M F)
    (Q₁ : SimplicialRealization D₁ F)
    (hG₁ : IsUniversalCocone (Q₁.cocone.mapFunctor G))
    (Q₂ : SimplicialRealization D₂ F) :
    G.obj Q₁.pt ≅ Q₂.pt :=
  ((hG₁.toRealization).changeDiagram Φ hF).realizationIso Q₂ (Iso.refl F)

lemma ι_liftedRealizationIso_hom
    {C' : Type u₃} [Category.{v₃} C'] (G : C ⥤ C')
    {M M₁ M₂ : ℕ} {h₁ : M ≤ M₁} {h₂ : M ≤ M₂}
    {D₁ : CosimplicialUpTo C M₁} {D₂ : CosimplicialUpTo C' M₂}
    (Φ : DiagramIsoOn M h₁ h₂ (D₁.mapFunctor G) D₂)
    {F : SemiSSet.{u}} (hF : HasDimLe M F)
    (Q₁ : SimplicialRealization D₁ F)
    (hG₁ : IsUniversalCocone (Q₁.cocone.mapFunctor G))
    (Q₂ : SimplicialRealization D₂ F)
    {k : ℕ} (hk : k ≤ M)
    (x : F.obj (op (Henry.SemiSimplexCategory.mk k))) :
    G.map (Q₁.cocone.ι k (hk.trans h₁) x) ≫ (liftedRealizationIso G Φ hF Q₁ hG₁ Q₂).hom =
      (Φ.iso k hk).hom ≫ Q₂.cocone.ι k (hk.trans h₂) x := by
  let QG₂ := (hG₁.toRealization).changeDiagram Φ hF
  have hfac := SimplicialRealization.ι_realizationMap QG₂ Q₂ (𝟙 F) k (hk.trans h₂) x
  have hfac' : (Φ.iso k hk).inv ≫ G.map (Q₁.cocone.ι k (hk.trans h₁) x) ≫
      (liftedRealizationIso G Φ hF Q₁ hG₁ Q₂).hom =
    Q₂.cocone.ι k (hk.trans h₂) x :=
    (Category.assoc (Φ.iso k hk).inv (G.map (Q₁.cocone.ι k (hk.trans h₁) x))
      (liftedRealizationIso G Φ hF Q₁ hG₁ Q₂).hom).symm.trans hfac
  rw [← hfac', ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rfl

lemma map_realizationMap_stdSimplex_eq_liftedRealizationIso
    {C' : Type u₃} [Category.{v₃} C'] (G : C ⥤ C')
    {M M₁ M₂ : ℕ} {h₁ : M ≤ M₁} {h₂ : M ≤ M₂}
    {D₁ : CosimplicialUpTo C M₁} {D₂ : CosimplicialUpTo C' M₂}
    (Φ : DiagramIsoOn M h₁ h₂ (D₁.mapFunctor G) D₂)
    {F : SemiSSet.{u}} (hF : HasDimLe M F)
    (Q₁ : SimplicialRealization D₁ F)
    (hG₁ : IsUniversalCocone (Q₁.cocone.mapFunctor G))
    (Q₂ : SimplicialRealization D₂ F)
    {m : ℕ} (hm : m ≤ M)
    (α : F ⟶ SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m)) :
    G.map (SimplicialRealization.realizationMap Q₁ (stdSimplexRealization D₁ m (hm.trans h₁)) α) =
      (liftedRealizationIso G Φ hF Q₁ hG₁ Q₂).hom ≫
        SimplicialRealization.realizationMap Q₂ (stdSimplexRealization D₂ m (hm.trans h₂)) α ≫
        (Φ.iso m hm).inv := by
  apply (hG₁.toRealization).hom_ext
  intro k hk₁ x
  have hk : k ≤ M := hF x
  let a := (Φ.iso k hk).hom
  let b := Q₂.cocone.ι k (hk.trans h₂) x
  let c := SimplicialRealization.realizationMap Q₂ (stdSimplexRealization D₂ m (hm.trans h₂)) α
  let d := (Φ.iso m hm).inv
  let g := ULift.down (α.app (op (Henry.SemiSimplexCategory.mk k)) x)
  have hk_le_m : k ≤ m := len_le_of_hom g
  have h1 : G.map (Q₁.cocone.ι k hk₁ x) ≫
      G.map (SimplicialRealization.realizationMap Q₁ (stdSimplexRealization D₁ m (hm.trans h₁)) α) =
      (D₁.mapFunctor G).map hk_le_m (hm.trans h₁) g :=
    (G.map_comp _ _).symm.trans (congrArg (fun f => G.map f)
      (SimplicialRealization.ι_realizationMap Q₁
        (stdSimplexRealization D₁ m (hm.trans h₁)) α k hk₁ x))
  have h_nat : (D₁.mapFunctor G).map hk_le_m (hm.trans h₁) g =
      a ≫ D₂.map hk_le_m (hm.trans h₂) g ≫ d := by
    rw [← Category.assoc a, ← Φ.naturality hk_le_m hm g, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have h2 := SimplicialRealization.ι_realizationMap Q₂
    (stdSimplexRealization D₂ m (hm.trans h₂)) α k (hk.trans h₂) x
  have h3 : a ≫ D₂.map hk_le_m (hm.trans h₂) g ≫ d = a ≫ (b ≫ c) ≫ d :=
    congrArg (fun u => a ≫ u ≫ d) h2.symm
  have h4 : a ≫ (b ≫ c) ≫ d = (a ≫ b) ≫ (c ≫ d) :=
    (congrArg (a ≫ ·) (Category.assoc b c d)).trans (Category.assoc a b (c ≫ d)).symm
  have h_leg := ι_liftedRealizationIso_hom G Φ hF Q₁ hG₁ Q₂ hk x
  have h5 : (a ≫ b) ≫ (c ≫ d) =
      G.map (Q₁.cocone.ι k hk₁ x) ≫
        ((liftedRealizationIso G Φ hF Q₁ hG₁ Q₂).hom ≫ c ≫ d) :=
    (congrArg (· ≫ (c ≫ d)) h_leg.symm).trans
      (Category.assoc (G.map (Q₁.cocone.ι k (hk.trans h₁) x))
        (liftedRealizationIso G Φ hF Q₁ hG₁ Q₂).hom (c ≫ d))
  exact h1.trans (h_nat.trans (h3.trans (h4.trans h5)))

end DiagramChangeHelpers

/-!
## Extending a truncated cosimplicial diagram from `M` to `M + 1`
-/

section ExtendCosimplicial

variable {C : Type u₂} [Category.{v₂} C] {M : ℕ}

/-- The boundary simplex in `∂Δ_{M+1}` at `[k]` defined by `f : [k] ⟶ [M + 1]` for `k ≤ M`. -/
def boundarySuccSimplex {k : ℕ} (hk : k ≤ M)
    (f : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk (M + 1)) :
    ((SemiSSet.boundary.{u} (M + 1)).toFunctor).obj (op (Henry.SemiSimplexCategory.mk k)) :=
  ⟨(ULift.up f : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk (M + 1))).obj
      (op (Henry.SemiSimplexCategory.mk k))),
    (mem_boundary_iff.{u} _).mpr (Nat.lt_succ_of_le hk)⟩

/-- A morphism `f : [k] ⟶ [m]` with `k ≤ M`, `m ≤ M + 1`, and `¬ m ≤ M` defines an element of
`∂Δ_{M+1}` at `[k]`. -/
def boundarySimplexOfLe {k m : ℕ} (hk : k ≤ M) (hm : m ≤ M + 1) (hm' : ¬ m ≤ M)
    (f : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk m) :
    ((SemiSSet.boundary.{u} (M + 1)).toFunctor).obj (op (Henry.SemiSimplexCategory.mk k)) :=
  boundarySuccSimplex.{u} hk (f ≫ eqToHom (congrArg Henry.SemiSimplexCategory.mk (by omega)))

lemma boundarySimplexOfLe_map {j k m : ℕ} (hj : j ≤ k) (hk : k ≤ M) (hm : m ≤ M + 1) (hm' : ¬ m ≤ M)
    (g : Henry.SemiSimplexCategory.mk j ⟶ Henry.SemiSimplexCategory.mk k)
    (f : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk m) :
    ((SemiSSet.boundary.{u} (M + 1)).toFunctor).map g.op (boundarySimplexOfLe hk hm hm' f) =
      boundarySimplexOfLe (hj.trans hk) hm hm' (g ≫ f) := by
  apply Subtype.ext
  apply ULift.ext
  exact (Category.assoc g f _).symm

lemma boundarySimplexOfLe_comp_end {k m n : ℕ} (hk : k ≤ M)
    (hm : m ≤ n) (hn : n ≤ M + 1) (hm' : ¬ m ≤ M) (hn' : ¬ n ≤ M)
    (f : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk m)
    (g : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk n) :
    boundarySimplexOfLe hk hn hn' (f ≫ g) =
      boundarySimplexOfLe hk (hm.trans hn) hm' f := by
  have hmn : m = n := by omega
  subst hmn
  have hg : g = 𝟙 (Henry.SemiSimplexCategory.mk m) := hom_eq_id_of_end g
  rw [hg, Category.comp_id]

/-- Object function for `CosimplicialUpTo.extend`. -/
def extendObj (D : CosimplicialUpTo C M) (X_succ : C) (k : ℕ) : C :=
  if hk : k ≤ M then D.obj k hk else X_succ

lemma extendObj_of_le (D : CosimplicialUpTo C M) (X_succ : C) {k : ℕ} (hk : k ≤ M) :
    extendObj D X_succ k = D.obj k hk :=
  dite_eq_left_of_eq_true (eq_true hk)

lemma extendObj_of_not_le (D : CosimplicialUpTo C M) (X_succ : C) {k : ℕ} (hk : ¬ k ≤ M) :
    extendObj D X_succ k = X_succ :=
  dite_eq_right_of_eq_false (eq_false hk)

lemma extendObj_succ (D : CosimplicialUpTo C M) (X_succ : C) :
    extendObj D X_succ (M + 1) = X_succ :=
  extendObj_of_not_le D X_succ (Nat.not_succ_le_self M)

/-- Extend `D : CosimplicialUpTo C M` to `CosimplicialUpTo C (M + 1)` by attaching `i_succ : Q_bd.pt ⟶ X_succ`
from a realization `Q_bd` of `∂Δ_{M+1}` along `D`. -/
def CosimplicialUpTo.extend (D : CosimplicialUpTo C M)
    (Q_bd : SimplicialRealization D (SemiSSet.boundary.{u} (M + 1)).toFunctor)
    (X_succ : C) (i_succ : Q_bd.pt ⟶ X_succ) :
    CosimplicialUpTo C (M + 1) where
  obj k _ := extendObj D X_succ k
  map {k m} hk hm f :=
    if hk' : k ≤ M then
      if hm' : m ≤ M then
        eqToHom (extendObj_of_le D X_succ hk') ≫
          D.map hk hm' f ≫
          eqToHom (extendObj_of_le D X_succ hm').symm
      else
        eqToHom (extendObj_of_le D X_succ hk') ≫
          Q_bd.cocone.ι k hk' (boundarySimplexOfLe hk' hm hm' f) ≫
          i_succ ≫
          eqToHom (extendObj_of_not_le D X_succ hm').symm
    else
      if hm' : m ≤ M then
        (hk' (hk.trans hm')).elim
      else
        eqToHom (extendObj_of_not_le D X_succ hk') ≫
          eqToHom (extendObj_of_not_le D X_succ hm').symm
  map_id k hk := by
    split_ifs with hk'
    · rw [D.map_id k hk', Category.id_comp, eqToHom_trans, eqToHom_refl]
    · rw [eqToHom_trans, eqToHom_refl]
  map_comp {k m n} hk hm hn f g := by
    split_ifs <;> try (exfalso; omega)
    · simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [← Category.assoc (D.map _ _ f), D.map_comp _ _ _ f g]
    · simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [← Category.assoc (D.map _ _ f),
        Q_bd.cocone.w hk _ f (boundarySimplexOfLe _ hn _ g),
        boundarySimplexOfLe_map hk _ hn _ f g]
    · simp only [Category.assoc, eqToHom_trans]
      rw [boundarySimplexOfLe_comp_end _ hm hn _ _ f g]
    · simp only [eqToHom_trans]

lemma CosimplicialUpTo.extend_obj_le (D : CosimplicialUpTo C M)
    (Q_bd : SimplicialRealization D (SemiSSet.boundary.{u} (M + 1)).toFunctor)
    (X_succ : C) (i_succ : Q_bd.pt ⟶ X_succ)
    {k : ℕ} (hk : k ≤ M) (hk_succ : k ≤ M + 1) :
    (D.extend Q_bd X_succ i_succ).obj k hk_succ = D.obj k hk :=
  extendObj_of_le D X_succ hk

lemma CosimplicialUpTo.extend_obj_not_le (D : CosimplicialUpTo C M)
    (Q_bd : SimplicialRealization D (SemiSSet.boundary.{u} (M + 1)).toFunctor)
    (X_succ : C) (i_succ : Q_bd.pt ⟶ X_succ)
    {k : ℕ} (hk : ¬ k ≤ M) (hk_succ : k ≤ M + 1) :
    (D.extend Q_bd X_succ i_succ).obj k hk_succ = X_succ :=
  extendObj_of_not_le D X_succ hk

lemma CosimplicialUpTo.extend_obj_succ (D : CosimplicialUpTo C M)
    (Q_bd : SimplicialRealization D (SemiSSet.boundary.{u} (M + 1)).toFunctor)
    (X_succ : C) (i_succ : Q_bd.pt ⟶ X_succ) :
    (D.extend Q_bd X_succ i_succ).obj (M + 1) (le_refl (M + 1)) = X_succ :=
  extendObj_succ D X_succ

lemma CosimplicialUpTo.extend_map_le_le (D : CosimplicialUpTo C M)
    (Q_bd : SimplicialRealization D (SemiSSet.boundary.{u} (M + 1)).toFunctor)
    (X_succ : C) (i_succ : Q_bd.pt ⟶ X_succ)
    {k m : ℕ} (hk : k ≤ m) (hm : m ≤ M) (hm_succ : m ≤ M + 1)
    (f : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk m) :
    (D.extend Q_bd X_succ i_succ).map hk hm_succ f =
      eqToHom (D.extend_obj_le Q_bd X_succ i_succ (hk.trans hm) (hk.trans hm_succ)) ≫
        D.map hk hm f ≫
        eqToHom (D.extend_obj_le Q_bd X_succ i_succ hm hm_succ).symm := by
  dsimp [CosimplicialUpTo.extend]
  rw [dite_eq_left_of_eq_true (eq_true (hk.trans hm)),
    dite_eq_left_of_eq_true (eq_true hm)]

lemma CosimplicialUpTo.extend_map_le_succ (D : CosimplicialUpTo C M)
    (Q_bd : SimplicialRealization D (SemiSSet.boundary.{u} (M + 1)).toFunctor)
    (X_succ : C) (i_succ : Q_bd.pt ⟶ X_succ)
    {k : ℕ} (hk : k ≤ M) (hk_succ : k ≤ M + 1)
    (f : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk (M + 1)) :
    (D.extend Q_bd X_succ i_succ).map hk_succ (le_refl (M + 1)) f =
      eqToHom (D.extend_obj_le Q_bd X_succ i_succ hk hk_succ) ≫
        Q_bd.cocone.ι k hk (boundarySuccSimplex.{u} hk f) ≫
        i_succ ≫
        eqToHom (D.extend_obj_succ Q_bd X_succ i_succ).symm := by
  dsimp [CosimplicialUpTo.extend, boundarySimplexOfLe, boundarySuccSimplex]
  rw [dite_eq_left_of_eq_true (eq_true hk),
    dite_eq_right_of_eq_false (eq_false (Nat.not_succ_le_self M))]
  simp

/-- `D` and `D.extend Q_bd X_succ i_succ` are canonically isomorphic on dimensions `≤ M`. -/
@[simps]
def CosimplicialUpTo.extendDiagramIsoOn (D : CosimplicialUpTo C M)
    (Q_bd : SimplicialRealization D (SemiSSet.boundary.{u} (M + 1)).toFunctor)
    (X_succ : C) (i_succ : Q_bd.pt ⟶ X_succ) :
    DiagramIsoOn M (le_refl M) (Nat.le_succ M) D (D.extend Q_bd X_succ i_succ) where
  iso k hk := eqToIso (D.extend_obj_le Q_bd X_succ i_succ hk (Nat.le_succ_of_le hk)).symm
  naturality hk hm f := by
    rw [D.extend_map_le_le Q_bd X_succ i_succ hk hm (Nat.le_succ_of_le hm) f]
    simp

/-- When `Q_bd` is transported to `D.extend Q_bd X_succ i_succ`, its boundary inclusion into
`stdSimplexRealization (D.extend ...) (M + 1)` is `i_succ` up to `eqToHom`. -/
lemma CosimplicialUpTo.realizationMap_extend_boundary_succ (D : CosimplicialUpTo C M)
    (Q_bd : SimplicialRealization D (SemiSSet.boundary.{u} (M + 1)).toFunctor)
    (X_succ : C) (i_succ : Q_bd.pt ⟶ X_succ) :
    SimplicialRealization.realizationMap
      (Q_bd.changeDiagram (D.extendDiagramIsoOn Q_bd X_succ i_succ) (hasDimLe_boundary M))
      (stdSimplexRealization (D.extend Q_bd X_succ i_succ) (M + 1) (le_refl (M + 1)))
      (SemiSSet.boundary.{u} (M + 1)).ι =
    i_succ ≫ eqToHom (D.extend_obj_succ Q_bd X_succ i_succ).symm := by
  let D' := D.extend Q_bd X_succ i_succ
  let Φ := D.extendDiagramIsoOn Q_bd X_succ i_succ
  let Q_bd' := Q_bd.changeDiagram Φ (hasDimLe_boundary M)
  apply Q_bd'.hom_ext
  intro k hk_succ x
  have hk : k ≤ M := hasDimLe_boundary M x
  have h1 := SimplicialRealization.ι_realizationMap Q_bd'
    (stdSimplexRealization D' (M + 1) (le_refl (M + 1)))
    (SemiSSet.boundary.{u} (M + 1)).ι k hk_succ x
  rw [h1]
  change D'.map hk_succ (le_refl (M + 1)) (ULift.down x.1) =
    (eqToHom (D.extend_obj_le Q_bd X_succ i_succ hk (Nat.le_succ_of_le hk)) ≫
      Q_bd.cocone.ι k hk x) ≫
      (i_succ ≫ eqToHom (D.extend_obj_succ Q_bd X_succ i_succ).symm)
  rw [D.extend_map_le_succ Q_bd X_succ i_succ hk hk_succ (ULift.down x.1)]
  simp only [Category.assoc]
  rfl

/-- Chosen boundary realization at `m ≤ M + 1` for `D.extend Q_bd X_succ i_succ`. -/
noncomputable def extendBdRealization [CategoryWithCofibrations C]
    (D : CosimplicialUpTo C M) (BData : CosimplicialBoundaryData.{v₂, u₂, u} D)
    (Q_bd : SimplicialRealization D (SemiSSet.boundary.{u} (M + 1)).toFunctor)
    (X_succ : C) (i_succ : Q_bd.pt ⟶ X_succ) (m : ℕ) (hm : m ≤ M + 1) :
    SimplicialRealization (D.extend Q_bd X_succ i_succ) (SemiSSet.boundary.{u} m).toFunctor :=
  if hm' : m ≤ M then
    (BData.bdRealization m hm').changeDiagram
      (D.extendDiagramIsoOn Q_bd X_succ i_succ)
      (hasDimLe_subfunctor_stdSimplex hm' (SemiSSet.boundary.{u} m))
  else
    (Q_bd.changeDiagram (D.extendDiagramIsoOn Q_bd X_succ i_succ) (hasDimLe_boundary M)).ofIso
      (eqToIso (by
        have hm_eq : m = M + 1 := by omega
        rw [hm_eq]))

lemma extendBdRealization_of_le [CategoryWithCofibrations C]
    (D : CosimplicialUpTo C M) (BData : CosimplicialBoundaryData.{v₂, u₂, u} D)
    (Q_bd : SimplicialRealization D (SemiSSet.boundary.{u} (M + 1)).toFunctor)
    (X_succ : C) (i_succ : Q_bd.pt ⟶ X_succ) {m : ℕ} (hm : m ≤ M + 1) (hm' : m ≤ M) :
    extendBdRealization D BData Q_bd X_succ i_succ m hm =
      (BData.bdRealization m hm').changeDiagram
        (D.extendDiagramIsoOn Q_bd X_succ i_succ)
        (hasDimLe_subfunctor_stdSimplex hm' (SemiSSet.boundary.{u} m)) :=
  dite_eq_left_of_eq_true (eq_true hm')

lemma extendBdRealization_succ [CategoryWithCofibrations C]
    (D : CosimplicialUpTo C M) (BData : CosimplicialBoundaryData.{v₂, u₂, u} D)
    (Q_bd : SimplicialRealization D (SemiSSet.boundary.{u} (M + 1)).toFunctor)
    (X_succ : C) (i_succ : Q_bd.pt ⟶ X_succ) (hm : M + 1 ≤ M + 1) :
    extendBdRealization D BData Q_bd X_succ i_succ (M + 1) hm =
      (Q_bd.changeDiagram (D.extendDiagramIsoOn Q_bd X_succ i_succ) (hasDimLe_boundary M)).ofIso
        (Iso.refl _) :=
  dite_eq_right_of_eq_false (eq_false (Nat.not_succ_le_self M))

lemma cofibrations_comp_iso_hom [CategoryWithCofibrations C] [IsCofibrationCategory C]
    {A B B' : C} (f : A ⟶ B) (e : B ≅ B') (hf : cofibrations C f) :
    cofibrations C (f ≫ e.hom) :=
  cofibrations_comp f e.hom hf (cofibrations_of_isIso e.hom)

/-- Extending `CosimplicialBoundaryData` from `D` to `D.extend Q_bd X_succ i_succ` when `i_succ` is
a cofibration. -/
noncomputable def CosimplicialUpTo.extendBoundaryData
    [CategoryWithCofibrations C] [IsCofibrationCategory C]
    (D : CosimplicialUpTo C M) (BData : CosimplicialBoundaryData.{v₂, u₂, u} D)
    (Q_bd : SimplicialRealization D (SemiSSet.boundary.{u} (M + 1)).toFunctor)
    (X_succ : C) (i_succ : Q_bd.pt ⟶ X_succ) (hi_succ : cofibrations C i_succ) :
    CosimplicialBoundaryData.{v₂, u₂, u} (D.extend Q_bd X_succ i_succ) where
  bdRealization m hm := extendBdRealization D BData Q_bd X_succ i_succ m hm
  bdInclusion_cofibration m hm := by
    let Φ := D.extendDiagramIsoOn Q_bd X_succ i_succ
    by_cases hm' : m ≤ M
    · rw [extendBdRealization_of_le D BData Q_bd X_succ i_succ hm hm',
        SimplicialRealization.realizationMap_changeDiagram_stdSimplex Φ
          (hasDimLe_subfunctor_stdSimplex hm' (SemiSSet.boundary.{u} m))
          (BData.bdRealization m hm') hm' (SemiSSet.boundary.{u} m).ι]
      exact cofibrations_comp_iso_hom _ (Φ.iso m hm') (BData.bdInclusion_cofibration m hm')
    · have hm_eq : m = M + 1 := by omega
      subst hm_eq
      rw [extendBdRealization_succ D BData Q_bd X_succ i_succ hm,
        SimplicialRealization.realizationMap_ofIso_left, Iso.refl_inv, Category.id_comp,
        D.realizationMap_extend_boundary_succ Q_bd X_succ i_succ]
      exact cofibrations_comp_iso_hom _ (eqToIso (D.extend_obj_succ Q_bd X_succ i_succ).symm) hi_succ

/-- If a functor `G : C ⥤ C'` preserves the boundary realizations of `BData` and preserves `Q_bd`,
then `G` preserves the boundary realizations of `D.extendBoundaryData BData Q_bd X_succ i_succ hi_succ`. -/
lemma CosimplicialUpTo.preservesBoundaryRealizations_extendBoundaryData
    [CategoryWithCofibrations C] [IsCofibrationCategory C]
    {C' : Type u₃} [Category.{v₃} C'] (G : C ⥤ C')
    (D : CosimplicialUpTo C M) (BData : CosimplicialBoundaryData.{v₂, u₂, u} D)
    (Q_bd : SimplicialRealization D (SemiSSet.boundary.{u} (M + 1)).toFunctor)
    (X_succ : C) (i_succ : Q_bd.pt ⟶ X_succ) (hi_succ : cofibrations C i_succ)
    (hG_bd : PreservesBoundaryRealizations BData G)
    (hG_succ : IsUniversalCocone (Q_bd.cocone.mapFunctor G)) :
    PreservesBoundaryRealizations
      (D.extendBoundaryData BData Q_bd X_succ i_succ hi_succ) G := by
  intro m hm
  change IsUniversalCocone ((extendBdRealization D BData Q_bd X_succ i_succ m hm).cocone.mapFunctor G)
  by_cases hm' : m ≤ M
  · rw [extendBdRealization_of_le D BData Q_bd X_succ i_succ hm hm']
    exact isUniversalCocone_mapFunctor_changeDiagram G
      (D.extendDiagramIsoOn Q_bd X_succ i_succ)
      (hasDimLe_subfunctor_stdSimplex hm' (SemiSSet.boundary.{u} m))
      (BData.bdRealization m hm') (hG_bd m hm')
  · have hm_eq : m = M + 1 := by omega
    subst hm_eq
    rw [extendBdRealization_succ D BData Q_bd X_succ i_succ hm]
    exact isUniversalCocone_precomp_iso
      (isUniversalCocone_mapFunctor_changeDiagram G
        (D.extendDiagramIsoOn Q_bd X_succ i_succ) (hasDimLe_boundary M) Q_bd hG_succ)
      (Iso.refl _)

end ExtendCosimplicial

/-!
## Realizations of free algebraic Kan complexes in `CDelta`
-/

section FreeCDeltaRealization

/-- Yoneda morphism `Δ_k ⟶ F` in `SemiSSet` corresponding to `x : F.obj (op [k])`. -/
@[simps]
def simplexToSemiSSet {F : SemiSSet.{u}} {k : ℕ}
    (x : F.obj (op (Henry.SemiSimplexCategory.mk k))) :
    SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k) ⟶ F where
  app Δ := ↾(fun g => F.map (ULift.down g).op x)
  naturality {Δ Δ'} f := by
    ext g
    exact ConcreteCategory.congr_hom (F.map_comp (ULift.down g).op f) x

@[simp]
lemma simplexToSemiSSet_app_id {F : SemiSSet.{u}} {k : ℕ}
    (x : F.obj (op (Henry.SemiSimplexCategory.mk k))) :
    (simplexToSemiSSet x).app (op (Henry.SemiSimplexCategory.mk k))
      (ULift.up (𝟙 (Henry.SemiSimplexCategory.mk k))) = x :=
  ConcreteCategory.congr_hom (F.map_id (op (Henry.SemiSimplexCategory.mk k))) x

lemma stdSimplex_map_comp_simplexToSemiSSet {F : SemiSSet.{u}} {k m : ℕ}
    (g : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk m)
    (y : F.obj (op (Henry.SemiSimplexCategory.mk m))) :
    SemiSSet.stdSimplex.{u}.map g ≫ simplexToSemiSSet y =
      simplexToSemiSSet (F.map g.op y) := by
  ext Δ h
  exact ConcreteCategory.congr_hom (F.map_comp g.op (ULift.down h).op) y

lemma simplexToSemiSSet_comp {F₁ F₂ : SemiSSet.{u}} (α : F₁ ⟶ F₂) {k : ℕ}
    (x : F₁.obj (op (Henry.SemiSimplexCategory.mk k))) :
    simplexToSemiSSet x ≫ α = simplexToSemiSSet (α.app (op (Henry.SemiSimplexCategory.mk k)) x) := by
  ext Δ g
  exact ConcreteCategory.congr_hom (α.naturality (ULift.down g).op) x

/-- The canonical cocone on `F : SemiSSet` along `stdCosimplicialUpTo M` with apex
`⟨freeAlgKan F, hCell⟩ : CDelta`. -/
@[simps]
noncomputable def freeCDeltaCocone (M : ℕ) (F : SemiSSet.{u})
    (hCell : AlgKan.IsFinitelyCellular (freeAlgKan F)) :
    SimplicialCocone (stdCosimplicialUpTo.{u} M) F ⟨freeAlgKan F, hCell⟩ where
  ι _k _ x := ObjectProperty.homMk (freeAlgKanMap (simplexToSemiSSet x))
  w _ _ g y := by
    apply ObjectProperty.hom_ext
    change freeAlgKanMap (SemiSSet.stdSimplex.{u}.map g) ≫ freeAlgKanMap (simplexToSemiSSet y) =
      freeAlgKanMap (simplexToSemiSSet (F.map g.op y))
    rw [← freeAlgKanMap_comp, stdSimplex_map_comp_simplexToSemiSSet]

/-- Given `HasDimLe M F`, a cocone `c : SimplicialCocone (stdCosimplicialUpTo M) F z` induces a
semi-simplicial map `F ⟶ z.obj.X`. -/
@[simps]
noncomputable def coconeToSemiSSet {M : ℕ} {F : SemiSSet.{u}} (hF : HasDimLe M F)
    {z : CDelta.{u}} (c : SimplicialCocone (stdCosimplicialUpTo.{u} M) F z) :
    F ⟶ z.obj.X where
  app Δ := ↾(fun x =>
    let k := (unop Δ).obj.len
    let idΔ : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k)).obj Δ :=
      ULift.up (𝟙 (unop Δ))
    (freeAlgKanUnit (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k)) ≫
      (c.ι k (hF x) x).hom.hom).app Δ idΔ)
  naturality {Δ Δ'} f := by
    ext x
    dsimp
    let k := (unop Δ).obj.len
    let k' := (unop Δ').obj.len
    have hk : k ≤ M := hF x
    have hk'k : k' ≤ k := len_le_of_hom (unop f)
    have hcomp := congrArg (fun h : stdSimplexCDelta.{u} k' ⟶ z =>
        freeAlgKanUnit (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k')) ≫ h.hom.hom)
      (c.w hk'k hk (unop f) x)
    dsimp only [stdCosimplicialUpTo] at hcomp
    have hunit :
        freeAlgKanUnit (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k')) ≫
          (stdSimplexCDeltaMap.{u} (unop f) ≫ c.ι k hk x).hom.hom =
        SemiSSet.stdSimplex.{u}.map (unop f) ≫
          (freeAlgKanUnit (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k)) ≫
            (c.ι k hk x).hom.hom) :=
      congrArg (· ≫ (c.ι k hk x).hom.hom)
        (freeAlgKanUnit_comp_freeAlgKanMap (SemiSSet.stdSimplex.{u}.map (unop f)))
    rw [hunit] at hcomp
    let idΔ' : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k')).obj Δ' :=
      ULift.up (𝟙 (unop Δ'))
    let idΔ : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k)).obj Δ :=
      ULift.up (𝟙 (unop Δ))
    have happ := ConcreteCategory.congr_hom (congr_app hcomp Δ') idΔ'
    have hnat := ConcreteCategory.congr_hom
      ((freeAlgKanUnit (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k)) ≫
        (c.ι k hk x).hom.hom).naturality f) idΔ
    have hId : (SemiSSet.stdSimplex.{u}.map (unop f)).app Δ' idΔ' =
        (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k)).map f idΔ :=
      ULift.ext _ _ ((Category.id_comp (unop f)).trans (Category.comp_id (unop f)).symm)
    exact happ.symm.trans ((congrArg
      ((freeAlgKanUnit (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k)) ≫
        (c.ι k hk x).hom.hom).app Δ') hId).trans hnat)

lemma simplexToSemiSSet_comp_coconeToSemiSSet {M : ℕ} {F : SemiSSet.{u}} (hF : HasDimLe M F)
    {z : CDelta.{u}} (c : SimplicialCocone (stdCosimplicialUpTo.{u} M) F z)
    (k : ℕ) (hk : k ≤ M) (x : F.obj (op (Henry.SemiSimplexCategory.mk k))) :
    simplexToSemiSSet x ≫ coconeToSemiSSet hF c =
      freeAlgKanUnit (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k)) ≫
        (c.ι k hk x).hom.hom := by
  ext Δ g
  let k' := (unop Δ).obj.len
  have hk'k : k' ≤ k := len_le_of_hom (ULift.down g)
  have hcomp := congrArg (fun h : stdSimplexCDelta.{u} k' ⟶ z =>
      freeAlgKanUnit (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k')) ≫ h.hom.hom)
     (c.w hk'k hk (ULift.down g) x)
  dsimp only [stdCosimplicialUpTo] at hcomp
  have hunit :
      freeAlgKanUnit (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k')) ≫
        (stdSimplexCDeltaMap.{u} (ULift.down g) ≫ c.ι k hk x).hom.hom =
      SemiSSet.stdSimplex.{u}.map (ULift.down g) ≫
        (freeAlgKanUnit (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k)) ≫
          (c.ι k hk x).hom.hom) :=
    congrArg (· ≫ (c.ι k hk x).hom.hom)
      (freeAlgKanUnit_comp_freeAlgKanMap (SemiSSet.stdSimplex.{u}.map (ULift.down g)))
  rw [hunit] at hcomp
  let idΔ : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k')).obj Δ :=
    ULift.up (𝟙 (unop Δ))
  have happ := ConcreteCategory.congr_hom (congr_app hcomp Δ) idΔ
  have hId : (SemiSSet.stdSimplex.{u}.map (ULift.down g)).app Δ idΔ = g :=
    ULift.ext _ _ (Category.id_comp (ULift.down g))
  exact happ.symm.trans (congrArg
    ((freeAlgKanUnit (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k)) ≫
      (c.ι k hk x).hom.hom).app Δ) hId)

/-- When `HasDimLe M F`, `freeCDeltaCocone M F hCell` is a universal cocone in `CDelta`. -/
theorem isUniversalCocone_freeCDeltaCocone (M : ℕ) {F : SemiSSet.{u}}
    (hF : HasDimLe M F) (hCell : AlgKan.IsFinitelyCellular (freeAlgKan F)) :
    IsUniversalCocone (freeCDeltaCocone M F hCell) := by
  intro z c
  obtain ⟨u₀, hu₀, huniq₀⟩ := freeAlgKan_isFreeOn F z.obj (coconeToSemiSSet hF c)
  refine ⟨ObjectProperty.homMk u₀, ?_, ?_⟩
  · intro k hk x
    apply ObjectProperty.hom_ext
    apply freeAlgKan_hom_ext
    change freeAlgKanUnit _ ≫ (freeAlgKanMap (simplexToSemiSSet x) ≫ u₀).hom =
      freeAlgKanUnit _ ≫ (c.ι k hk x).hom.hom
    have h1 := congrArg (· ≫ u₀.hom) (freeAlgKanUnit_comp_freeAlgKanMap (simplexToSemiSSet x))
    have h2 := congrArg (simplexToSemiSSet x ≫ ·) hu₀
    exact h1.trans (h2.trans (simplexToSemiSSet_comp_coconeToSemiSSet hF c k hk x))
  · intro m hm
    apply ObjectProperty.hom_ext
    apply huniq₀ m.hom
    ext Δ x
    let k := (unop Δ).obj.len
    have hk : k ≤ M := hF x
    let idΔ : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k)).obj Δ :=
      ULift.up (𝟙 (unop Δ))
    have hmk := congrArg
      (fun f : stdSimplexCDelta.{u} k ⟶ z =>
        (freeAlgKanUnit (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k)) ≫
          f.hom.hom).app Δ idΔ)
      (hm k hk x)
    have hunit := ConcreteCategory.congr_hom
      (congr_app (congrArg (· ≫ m.hom.hom)
        (freeAlgKanUnit_comp_freeAlgKanMap (simplexToSemiSSet x))) Δ)
      idΔ
    have hid : ((simplexToSemiSSet x ≫ freeAlgKanUnit F ≫ m.hom.hom).app Δ) idΔ =
        (freeAlgKanUnit F ≫ m.hom.hom).app Δ x :=
      congrArg ((freeAlgKanUnit F ≫ m.hom.hom).app Δ) (simplexToSemiSSet_app_id x)
    exact hid.symm.trans (hunit.symm.trans hmk)

/-- Realization of `F : SemiSSet` (with `HasDimLe M F` and `IsFinitelyCellular (freeAlgKan F)`)
along `stdCosimplicialUpTo M` in `CDelta`. -/
@[simps! pt cocone]
noncomputable def freeCDeltaRealization (M : ℕ) {F : SemiSSet.{u}}
    (hF : HasDimLe M F) (hCell : AlgKan.IsFinitelyCellular (freeAlgKan F)) :
    SimplicialRealization (stdCosimplicialUpTo.{u} M) F :=
  (isUniversalCocone_freeCDeltaCocone M hF hCell).toRealization

lemma realizationMap_freeCDeltaRealization_stdSimplex (M : ℕ) {F : SemiSSet.{u}}
    (hF : HasDimLe M F) (hCell : AlgKan.IsFinitelyCellular (freeAlgKan F))
    {m : ℕ} (hm : m ≤ M)
    (α : F ⟶ SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m)) :
    SimplicialRealization.realizationMap (freeCDeltaRealization M hF hCell)
      (stdSimplexRealization (stdCosimplicialUpTo.{u} M) m hm) α =
    ObjectProperty.homMk (freeAlgKanMap α) := by
  apply (freeCDeltaRealization M hF hCell).hom_ext
  intro k hk x
  have h1 := SimplicialRealization.ι_realizationMap (freeCDeltaRealization M hF hCell)
    (stdSimplexRealization (stdCosimplicialUpTo.{u} M) m hm) α k hk x
  rw [h1]
  apply ObjectProperty.hom_ext
  change freeAlgKanMap (SemiSSet.stdSimplex.{u}.map (ULift.down (α.app (op (Henry.SemiSimplexCategory.mk k)) x))) =
    freeAlgKanMap (simplexToSemiSSet x) ≫ freeAlgKanMap α
  rw [← freeAlgKanMap_comp, simplexToSemiSSet_comp]
  rfl

/-- Realization of `∂Δ_m` (`m ≤ M`) along `stdCosimplicialUpTo M` with `.pt = boundaryCDelta m`. -/
@[simps! pt cocone]
noncomputable def boundaryCDeltaRealization (M m : ℕ) (hm : m ≤ M) :
    SimplicialRealization (stdCosimplicialUpTo.{u} M) (SemiSSet.boundary.{u} m).toFunctor :=
  freeCDeltaRealization M (hasDimLe_subfunctor_stdSimplex hm (SemiSSet.boundary.{u} m))
    (isFinitelyCellular_freeAlgKan_subfunctor (SemiSSet.boundary.{u} m))

/-- Realization of `∂Δ_{M+1}` along `stdCosimplicialUpTo M` with `.pt = boundaryCDelta (M + 1)`. -/
@[simps! pt cocone]
noncomputable def boundarySuccCDeltaRealization (M : ℕ) :
    SimplicialRealization (stdCosimplicialUpTo.{u} M) (SemiSSet.boundary.{u} (M + 1)).toFunctor :=
  freeCDeltaRealization M (hasDimLe_boundary M)
    (isFinitelyCellular_freeAlgKan_subfunctor (SemiSSet.boundary.{u} (M + 1)))

/-- Realization of `Λ^{n+1}_k` (`n + 1 ≤ M`) along `stdCosimplicialUpTo M` with `.pt = hornCDelta n k`. -/
@[simps! pt cocone]
noncomputable def hornCDeltaRealization (M n : ℕ) (hn : n + 1 ≤ M) (k : Fin (n + 2)) :
    SimplicialRealization (stdCosimplicialUpTo.{u} M) (SemiSSet.horn.{u} (n + 1) k).toFunctor :=
  freeCDeltaRealization M (hasDimLe_subfunctor_stdSimplex hn (SemiSSet.horn.{u} (n + 1) k))
    (isFinitelyCellular_freeAlgKan_subfunctor (SemiSSet.horn.{u} (n + 1) k))

@[simp]
lemma realizationMap_boundaryCDeltaRealization (M m : ℕ) (hm : m ≤ M) :
    SimplicialRealization.realizationMap (boundaryCDeltaRealization.{u} M m hm)
      (stdSimplexRealization (stdCosimplicialUpTo.{u} M) m hm) (SemiSSet.boundary.{u} m).ι =
    boundaryCDeltaInclusion.{u} m :=
  realizationMap_freeCDeltaRealization_stdSimplex M _ _ hm (SemiSSet.boundary.{u} m).ι

@[simp]
lemma realizationMap_hornCDeltaRealization (M n : ℕ) (hn : n + 1 ≤ M) (k : Fin (n + 2)) :
    SimplicialRealization.realizationMap (hornCDeltaRealization.{u} M n hn k)
      (stdSimplexRealization (stdCosimplicialUpTo.{u} M) (n + 1) hn)
      (SemiSSet.horn.{u} (n + 1) k).ι =
    hornInclusionCDelta.{u} n k :=
  realizationMap_freeCDeltaRealization_stdSimplex M _ _ hn (SemiSSet.horn.{u} (n + 1) k).ι

/-- Boundary realization data for `stdCosimplicialUpTo M` in `CDelta`. -/
noncomputable def stdCosimplicialBoundaryData (M : ℕ) :
    CosimplicialBoundaryData.{u, u + 1, u} (stdCosimplicialUpTo.{u} M) where
  bdRealization m hm := boundaryCDeltaRealization.{u} M m hm
  bdInclusion_cofibration m hm := by
    rw [realizationMap_boundaryCDeltaRealization]
    exact boundaryCDeltaInclusion_cofibration m

/-- `stdCosimplicialUpTo M` and `stdCosimplicialUpTo M'` agree via `Iso.refl` on `≤ M` when `M ≤ M'`. -/
@[simps]
noncomputable def stdCosimplicialDiagramIsoOn {M M' : ℕ} (hM : M ≤ M') :
    DiagramIsoOn M (le_refl M) hM (stdCosimplicialUpTo.{u} M) (stdCosimplicialUpTo.{u} M') where
  iso _ _ := Iso.refl _
  naturality _ _ _ := by simp [stdCosimplicialUpTo]

lemma isUniversalCocone_mapFunctor_freeCDeltaCocone_of_le
    {C' : Type u₃} [Category.{v₃} C'] (G : CDelta.{u} ⥤ C')
    {M M' : ℕ} (hM : M ≤ M') {F : SemiSSet.{u}} (hF : HasDimLe M F)
    (hCell : AlgKan.IsFinitelyCellular (freeAlgKan F))
    (hG : IsUniversalCocone ((freeCDeltaCocone M F hCell).mapFunctor G)) :
    IsUniversalCocone ((freeCDeltaCocone M' F hCell).mapFunctor G) := by
  have hchange := isUniversalCocone_mapFunctor_changeDiagram G
    (stdCosimplicialDiagramIsoOn.{u} hM) hF (freeCDeltaRealization M hF hCell) hG
  have heq : (((freeCDeltaRealization M hF hCell).changeDiagram
      (stdCosimplicialDiagramIsoOn.{u} hM) hF).cocone).mapFunctor G =
      (freeCDeltaCocone M' F hCell).mapFunctor G := by
    ext k hk x
    exact congrArg (fun f => G.map f)
      (Category.id_comp ((freeCDeltaCocone M' F hCell).ι k hk x))
  rwa [← heq]

/-- `boundaryCDelta 0` is initial in `CDelta`. -/
noncomputable def boundaryCDeltaZeroIsInitial : IsInitial (boundaryCDelta.{u} 0) := by
  let B := SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk 0)
  have hle₁ : SemiSSet.boundary.{u} 0 ≤ (⊥ : Subfunctor B) := by
    intro Δ x hx
    exact (Nat.not_lt_zero _ ((mem_boundary_iff x).mp hx)).elim
  have hle₂ : (⊥ : Subfunctor B) ≤ SemiSSet.boundary.{u} 0 := bot_le
  have hInit_bot : IsInitial
      (⟨freeAlgKan (⊥ : Subfunctor B).toFunctor,
        isFinitelyCellular_freeAlgKan_subfunctor ⊥⟩ : CDelta.{u}) :=
    IsInitial.ofUniqueHom
      (fun Z => ObjectProperty.homMk
        ((freeAlgKan_isFreeOn (⊥ : Subfunctor B).toFunctor Z.obj
          { app _ := ↾(fun x => x.2.elim)
            naturality _ _ _ := by ext x; exact x.2.elim }).choose))
      (fun Z g => by
        apply ObjectProperty.hom_ext
        apply freeAlgKan_hom_ext
        ext _ x
        exact x.2.elim)
  let e : (⟨freeAlgKan (⊥ : Subfunctor B).toFunctor,
      isFinitelyCellular_freeAlgKan_subfunctor ⊥⟩ : CDelta.{u}) ≅ boundaryCDelta.{u} 0 :=
    { hom := ObjectProperty.homMk (freeAlgKanMap (Subfunctor.homOfLe hle₂))
      inv := ObjectProperty.homMk (freeAlgKanMap (Subfunctor.homOfLe hle₁))
      hom_inv_id := by
        apply ObjectProperty.hom_ext
        change freeAlgKanMap _ ≫ freeAlgKanMap _ = 𝟙 _
        rw [← freeAlgKanMap_comp, show Subfunctor.homOfLe hle₂ ≫ Subfunctor.homOfLe hle₁ = 𝟙 _ by rfl,
          freeAlgKanMap_id]
      inv_hom_id := by
        apply ObjectProperty.hom_ext
        change freeAlgKanMap _ ≫ freeAlgKanMap _ = 𝟙 _
        rw [← freeAlgKanMap_comp, show Subfunctor.homOfLe hle₁ ≫ Subfunctor.homOfLe hle₂ = 𝟙 _ by rfl,
          freeAlgKanMap_id] }
  exact IsInitial.ofIso hInit_bot e

/-- Any cofibration morphism `G : CDelta ⥤ C'` preserves `stdCosimplicialBoundaryData M` for every `M : ℕ`. -/
theorem preservesBoundaryRealizations_stdCosimplicialBoundaryData
    {C' : Type u₃} [Category.{v₃} C'] [CategoryWithCofibrations C']
    (G : CDelta.{u} ⥤ C') (hG : IsCofibrationMorphism G) :
    ∀ M : ℕ, PreservesBoundaryRealizations (stdCosimplicialBoundaryData.{u} M) G := by
  have : IsCofibrationCategory CDelta.{u} := cDelta_isCofibrationCategory.{u}
  intro M
  induction M with
  | zero =>
    intro m hm
    have hm0 : m = 0 := Nat.le_zero.mp hm
    subst hm0
    have hGI : IsInitial (G.obj (boundaryCDelta.{u} 0)) :=
      (hG.map_initial boundaryCDeltaZeroIsInitial).some
    intro z c
    refine ⟨hGI.to z, ?_, ?_⟩
    · intro k _ x
      exact (Nat.not_lt_zero _ ((mem_boundary_iff x.1).mp x.2)).elim
    · intro u _
      exact hGI.hom_ext u (hGI.to z)
  | succ M ih =>
    intro m hm
    rcases Nat.of_le_succ hm with hmM | rfl
    · exact isUniversalCocone_mapFunctor_freeCDeltaCocone_of_le G (Nat.le_succ M)
        (hasDimLe_subfunctor_stdSimplex hmM (SemiSSet.boundary.{u} m))
        (isFinitelyCellular_freeAlgKan_subfunctor (SemiSSet.boundary.{u} m))
        (ih m hmM)
    · have h_succ_M : IsUniversalCocone ((boundarySuccCDeltaRealization.{u} M).cocone.mapFunctor G) :=
        isUniversalCocone_mapFunctor_of_subfunctor (stdCosimplicialBoundaryData.{u} M)
          G hG ih (SemiSSet.boundary.{u} (M + 1)) (hasDimLe_boundary M)
          (boundarySuccCDeltaRealization.{u} M)
      exact isUniversalCocone_mapFunctor_freeCDeltaCocone_of_le G (Nat.le_succ M)
        (hasDimLe_boundary M)
        (isFinitelyCellular_freeAlgKan_subfunctor (SemiSSet.boundary.{u} (M + 1)))
        h_succ_M

/-- Any cofibration morphism `G : CDelta ⥤ C'` preserves the realization of every subfunctor
`T : Subfunctor Δ_N` with `HasDimLe M T.toFunctor`. -/
theorem isUniversalCocone_mapFunctor_freeCDeltaCocone
    {C' : Type u₃} [Category.{v₃} C'] [CategoryWithCofibrations C']
    (G : CDelta.{u} ⥤ C') (hG : IsCofibrationMorphism G)
    {M N : ℕ} (T : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)))
    (hT : HasDimLe M T.toFunctor) :
    IsUniversalCocone
      ((freeCDeltaCocone M T.toFunctor (isFinitelyCellular_freeAlgKan_subfunctor T)).mapFunctor G) := by
  have : IsCofibrationCategory CDelta.{u} := cDelta_isCofibrationCategory.{u}
  exact isUniversalCocone_mapFunctor_of_subfunctor
    (stdCosimplicialBoundaryData.{u} M) G hG
    (preservesBoundaryRealizations_stdCosimplicialBoundaryData G hG M)
    T hT (freeCDeltaRealization M hT (isFinitelyCellular_freeAlgKan_subfunctor T))

end FreeCDeltaRealization

/-!
## Inductive lifting of `stdCosimplicialUpTo` along `p : X ⥤ Y`
-/

section LiftedCosimplicial

variable {X Y : Type u₂} [Category.{v₂} X] [CategoryWithCofibrations X]
  [CategoryWithWeakEquivalences X] [Category.{v₂} Y] [CategoryWithCofibrations Y]
  [CategoryWithWeakEquivalences Y]
  (p : X ⥤ Y) (hp : IsLiftingTarget false X Y p)
  (h : CDelta.{u} ⥤ Y) (hh : IsCylinderMorphism h)
  (x₀ : X) (hx₀ : p.obj x₀ = h.obj (stdSimplexCDelta.{u} 0))

/-- Stage-`M` data for the inductive lift of `stdCosimplicialUpTo M` along `p : X ⥤ Y` over
`h : CDelta ⥤ Y` anchored at `x₀ : X`. -/
structure LiftedCosimplicialUpTo (M : ℕ) where
  D : CosimplicialUpTo X M
  BData : CosimplicialBoundaryData.{v₂, u₂, u} D
  p_preserves_bd : PreservesBoundaryRealizations BData p
  obj_zero : D.obj 0 (Nat.zero_le M) = x₀
  c : ∀ (k : ℕ) (hk : k ≤ M), D.obj k hk ⟶ x₀
  c_zero : c 0 (Nat.zero_le M) = eqToHom obj_zero
  c_comp : ∀ {k m : ℕ} (hk : k ≤ m) (hm : m ≤ M)
    (g : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk m),
    D.map hk hm g ≫ c m hm = c k (hk.trans hm)
  c_weq : ∀ (k : ℕ) (hk : k ≤ M), weakEquivalences X (c k hk)
  p_obj : ∀ (k : ℕ) (hk : k ≤ M), p.obj (D.obj k hk) = h.obj (stdSimplexCDelta.{u} k)
  p_map : ∀ {k m : ℕ} (hk : k ≤ m) (hm : m ≤ M)
    (g : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk m),
    p.map (D.map hk hm g) =
      eqToHom (p_obj k (hk.trans hm)) ≫
        h.map (stdSimplexCDeltaMap.{u} g) ≫
        eqToHom (p_obj m hm).symm
  p_c : ∀ (k : ℕ) (hk : k ≤ M),
    p.map (c k hk) =
      eqToHom (p_obj k hk) ≫
        h.map (simplexContraction.{u} k) ≫
        eqToHom hx₀.symm

namespace LiftedCosimplicialUpTo

variable {p hp h hh x₀ hx₀}

/-- `L.D.mapFunctor p` and `(stdCosimplicialUpTo M).mapFunctor h` are isomorphic via `eqToIso (L.p_obj k hk)`. -/
@[simps]
noncomputable def diagramIsoOn {M : ℕ} (L : LiftedCosimplicialUpTo p h x₀ hx₀ M) :
    DiagramIsoOn M (le_refl M) (le_refl M)
      (L.D.mapFunctor p) ((stdCosimplicialUpTo.{u} M).mapFunctor h) where
  iso k hk := eqToIso (L.p_obj k hk)
  naturality hk hm g := by
    change p.map (L.D.map hk hm g) ≫ eqToHom (L.p_obj _ hm) =
      eqToHom (L.p_obj _ (hk.trans hm)) ≫ h.map (stdSimplexCDeltaMap.{u} g)
    rw [L.p_map hk hm g, Category.assoc, Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.comp_id]

/-- Every morphism `L.D.map hk hm g` in `L.D` is a weak equivalence in `X`. -/
lemma map_weq (hp : IsLiftingTarget false X Y p) {M : ℕ}
    (L : LiftedCosimplicialUpTo p h x₀ hx₀ M)
    {k m : ℕ} (hk : k ≤ m) (hm : m ≤ M)
    (g : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk m) :
    weakEquivalences X (L.D.map hk hm g) := by
  have : IsCylinderCategory X := hp.1
  apply weakEquivalences_of_comp_right (L.D.map hk hm g) (L.c m hm) (L.c_weq m hm)
  rw [L.c_comp hk hm g]
  exact L.c_weq k (hk.trans hm)

end LiftedCosimplicialUpTo

include hp in
/-- Base case `M = 0` of `LiftedCosimplicialUpTo`. -/
noncomputable def liftedCosimplicialUpToZero :
    LiftedCosimplicialUpTo p h x₀ hx₀ 0 := by
  have : IsCylinderCategory X := hp.1
  have : IsCofibrationCategory X := hp.1.toIsCofibrationCategory
  let D₀ : CosimplicialUpTo X 0 :=
    { obj := fun _ _ => x₀
      map := fun _ _ _ => 𝟙 x₀
      map_id := fun _ _ => rfl
      map_comp := fun _ _ _ _ _ => (Category.id_comp (𝟙 x₀)).symm }
  let I : X := (IsCofibrationCategory.exists_initial (C := X)).choose
  have hI : IsInitial I := (IsCofibrationCategory.exists_initial (C := X)).choose_spec.some
  let B₀ := SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk 0)
  have hle₁ : SemiSSet.boundary.{u} 0 ≤ (⊥ : Subfunctor B₀) := by
    intro Δ x hx
    exact (Nat.not_lt_zero _ ((mem_boundary_iff x).mp hx)).elim
  have hle₂ : (⊥ : Subfunctor B₀) ≤ SemiSSet.boundary.{u} 0 := bot_le
  let e_bot : (⊥ : Subfunctor B₀).toFunctor ≅ (SemiSSet.boundary.{u} 0).toFunctor :=
    subfunctorIsoOfLe hle₂ hle₁
  let Q_bd₀ : SimplicialRealization D₀ (SemiSSet.boundary.{u} 0).toFunctor :=
    (botRealization D₀ B₀ hI).ofIso e_bot.symm
  have hG_bd₀ : IsUniversalCocone (Q_bd₀.cocone.mapFunctor p) :=
    isUniversalCocone_precomp_iso
      (isUniversalCocone_mapFunctor_botCocone p D₀ B₀
        (hp.2.2.1.toIsCofibrationMorphism.map_initial hI).some)
      e_bot.symm
  let BData₀ : CosimplicialBoundaryData.{v₂, u₂, u} D₀ :=
    { bdRealization := fun m hm =>
        Q_bd₀.ofIso (eqToIso (by rw [Nat.le_zero.mp hm]))
      bdInclusion_cofibration := fun m hm => by
        have heq : SimplicialRealization.realizationMap
            (Q_bd₀.ofIso (eqToIso (by rw [Nat.le_zero.mp hm])))
            (stdSimplexRealization D₀ m hm) (SemiSSet.boundary.{u} m).ι =
            hI.to (D₀.obj m hm) := hI.hom_ext _ _
        rw [heq]
        exact IsCofibrationCategory.initial_cofibration hI (D₀.obj m hm) }
  refine
    { D := D₀
      BData := BData₀
      p_preserves_bd := fun m hm => by
        have hm0 : m = 0 := Nat.le_zero.mp hm
        subst hm0
        exact isUniversalCocone_precomp_iso hG_bd₀ (eqToIso rfl)
      obj_zero := rfl
      c := fun _ _ => 𝟙 x₀
      c_zero := rfl
      c_comp := fun _ _ _ => Category.id_comp (𝟙 x₀)
      c_weq := fun _ _ => weakEquivalences_id x₀
      p_obj := fun k hk => by
        have hk0 : k = 0 := Nat.le_zero.mp hk
        subst hk0
        exact hx₀
      p_map := fun {k m} hk hm g => by
        have hm0 : m = 0 := Nat.le_zero.mp hm
        have hk0 : k = 0 := Nat.le_zero.mp (hk.trans hm)
        subst hm0 hk0
        have hg : g = 𝟙 (Henry.SemiSimplexCategory.mk 0) := hom_eq_id_of_end g
        rw [hg, stdSimplexCDeltaMap_id, p.map_id, h.map_id, Category.id_comp,
          eqToHom_trans, eqToHom_refl]
      p_c := fun k hk => by
        have hk0 : k = 0 := Nat.le_zero.mp hk
        subst hk0
        rw [simplexContraction_zero, p.map_id, h.map_id, Category.id_comp,
          eqToHom_trans, eqToHom_refl] }

lemma weakEquivalences_eqToHom_comp [IsCylinderCategory X]
    {A A' B : X} (heq : A = A') (f : A' ⟶ B) (hf : weakEquivalences X f) :
    weakEquivalences X (eqToHom heq ≫ f) :=
  weakEquivalences_comp (eqToHom heq) f (weakEquivalences_of_isIso (eqToHom heq)) hf

include hp hh in
/-- Inductive step from `M` to `M + 1` for `LiftedCosimplicialUpTo`. -/
noncomputable def liftedCosimplicialUpToSucc (M : ℕ)
    (L : LiftedCosimplicialUpTo p h x₀ hx₀ M) :
    LiftedCosimplicialUpTo p h x₀ hx₀ (M + 1) := by
  have : IsCylinderCategory X := hp.1
  have : IsCofibrationCategory X := hp.1.toIsCofibrationCategory
  have : IsCylinderCategory Y := hp.2.1
  have : IsCofibrationCategory Y := hp.2.1.toIsCofibrationCategory
  let Q_bd_X : SimplicialRealization L.D (SemiSSet.boundary.{u} (M + 1)).toFunctor :=
    subfunctorRealization L.BData (SemiSSet.boundary.{u} (M + 1)) (hasDimLe_boundary M)
  have hp_bd_X : IsUniversalCocone (Q_bd_X.cocone.mapFunctor p) :=
    isUniversalCocone_mapFunctor_of_subfunctor L.BData p
      hp.2.2.1.toIsCofibrationMorphism L.p_preserves_bd
      (SemiSSet.boundary.{u} (M + 1)) (hasDimLe_boundary M) Q_bd_X
  let c_bd_X : SimplicialCocone L.D (SemiSSet.boundary.{u} (M + 1)).toFunctor x₀ :=
    { ι := fun k hk _ => L.c k hk
      w := fun hk hm g _ => L.c_comp hk hm g }
  let f_bd_X : Q_bd_X.pt ⟶ x₀ := Q_bd_X.desc c_bd_X
  have hh_bd_Y : IsUniversalCocone ((boundarySuccCDeltaRealization.{u} M).cocone.mapFunctor h) :=
    isUniversalCocone_mapFunctor_freeCDeltaCocone h hh.toIsCofibrationMorphism
      (SemiSSet.boundary.{u} (M + 1)) (hasDimLe_boundary M)
  let Q_bd_Y : SimplicialRealization ((stdCosimplicialUpTo.{u} M).mapFunctor h)
      (SemiSSet.boundary.{u} (M + 1)).toFunctor :=
    hh_bd_Y.toRealization
  let e_bd : p.obj Q_bd_X.pt ≅ h.obj (boundaryCDelta.{u} (M + 1)) :=
    liftedRealizationIso p L.diagramIsoOn (hasDimLe_boundary M) Q_bd_X hp_bd_X Q_bd_Y
  let i_Y : p.obj Q_bd_X.pt ⟶ h.obj (stdSimplexCDelta.{u} (M + 1)) :=
    e_bd.hom ≫ h.map (boundaryCDeltaInclusion.{u} (M + 1))
  let w_Y : h.obj (stdSimplexCDelta.{u} (M + 1)) ⟶ p.obj x₀ :=
    h.map (simplexContraction.{u} (M + 1)) ≫ eqToHom hx₀.symm
  have hi_Y : cofibrations Y i_Y :=
    cofibrations_comp _ _ (cofibrations_of_isIso e_bd.hom)
      (hh.map_cofibration _ (boundaryCDeltaInclusion_cofibration (M + 1)))
  have hw_Y : weakEquivalences Y w_Y :=
    weakEquivalences_comp _ _
      (hh.map_weakEquivalence _ (simplexContraction_weakEquivalence (M + 1)))
      (weakEquivalences_of_isIso _)
  have hfac_Y : i_Y ≫ w_Y = p.map f_bd_X := by
    apply (hp_bd_X.toRealization).hom_ext
    intro k hk x
    change p.map (Q_bd_X.cocone.ι k hk x) ≫ (i_Y ≫ w_Y) =
      p.map (Q_bd_X.cocone.ι k hk x) ≫ p.map f_bd_X
    rw [← p.map_comp, Q_bd_X.fac c_bd_X k hk x]
    change _ = p.map (L.c k hk)
    rw [L.p_c k hk]
    have h_leg : p.map (Q_bd_X.cocone.ι k hk x) ≫ e_bd.hom =
        eqToHom (L.p_obj k hk) ≫
          h.map (ObjectProperty.homMk (freeAlgKanMap (simplexToSemiSSet x)) :
            stdSimplexCDelta.{u} k ⟶ boundaryCDelta.{u} (M + 1)) :=
      ι_liftedRealizationIso_hom p L.diagramIsoOn (hasDimLe_boundary M)
        Q_bd_X hp_bd_X Q_bd_Y hk x
    dsimp [i_Y, w_Y]
    simp only [Category.assoc]
    rw [← Category.assoc (p.map (Q_bd_X.cocone.ι k hk x)), h_leg]
    have h_inc : (ObjectProperty.homMk (freeAlgKanMap (simplexToSemiSSet x)) :
          stdSimplexCDelta.{u} k ⟶ boundaryCDelta.{u} (M + 1)) ≫
        boundaryCDeltaInclusion.{u} (M + 1) =
        stdSimplexCDeltaMap.{u} (ULift.down x.1) := by
      apply ObjectProperty.hom_ext
      change freeAlgKanMap (simplexToSemiSSet x) ≫ freeAlgKanMap (SemiSSet.boundary.{u} (M + 1)).ι =
        freeAlgKanMap (SemiSSet.stdSimplex.{u}.map (ULift.down x.1))
      rw [← freeAlgKanMap_comp]
      rfl
    simp only [Category.assoc]
    rw [← Category.assoc (h.map _), ← h.map_comp, h_inc,
      ← Category.assoc (h.map (stdSimplexCDeltaMap.{u} (ULift.down x.1))),
      ← h.map_comp, stdSimplexCDeltaMap_comp_simplexContraction]
  let h_lift := hp.2.2.2.1.lift_factorization f_bd_X i_Y w_Y hi_Y hw_Y hfac_Y
  let X_succ := h_lift.choose
  let i_succ := h_lift.choose_spec.choose
  let c_succ := h_lift.choose_spec.choose_spec.choose
  have he_lift := h_lift.choose_spec.choose_spec.choose_spec
  have e_succ := he_lift.choose
  have h_props := he_lift.choose_spec
  have hi_succ := h_props.1
  have hw_succ := h_props.2.1
  have hfac_X := h_props.2.2.1
  have hp_i_succ := h_props.2.2.2.1
  have hp_c_succ := h_props.2.2.2.2
  let D' := L.D.extend Q_bd_X X_succ i_succ
  let BData' := L.D.extendBoundaryData L.BData Q_bd_X X_succ i_succ hi_succ
  have hp_bd' : PreservesBoundaryRealizations BData' p :=
    L.D.preservesBoundaryRealizations_extendBoundaryData p L.BData Q_bd_X X_succ i_succ hi_succ
      L.p_preserves_bd hp_bd_X
  have hobj_zero' : D'.obj 0 (Nat.zero_le (M + 1)) = x₀ :=
    (L.D.extend_obj_le Q_bd_X X_succ i_succ (Nat.zero_le M) (Nat.zero_le (M + 1))).trans L.obj_zero
  let c' : ∀ (k : ℕ) (hk : k ≤ M + 1), D'.obj k hk ⟶ x₀ := fun k hk =>
    if hk' : k ≤ M then
      eqToHom (L.D.extend_obj_le Q_bd_X X_succ i_succ hk' hk) ≫ L.c k hk'
    else
      eqToHom (L.D.extend_obj_not_le Q_bd_X X_succ i_succ hk' hk) ≫ c_succ
  have hp_obj' : ∀ (k : ℕ) (hk : k ≤ M + 1),
      p.obj (D'.obj k hk) = h.obj (stdSimplexCDelta.{u} k) := by
    intro k hk
    by_cases hk' : k ≤ M
    · exact (congrArg p.obj (L.D.extend_obj_le Q_bd_X X_succ i_succ hk' hk)).trans (L.p_obj k hk')
    · have hk_eq : k = M + 1 := by omega
      subst hk_eq
      exact (congrArg p.obj (L.D.extend_obj_succ Q_bd_X X_succ i_succ)).trans e_succ
  refine
    { D := D'
      BData := BData'
      p_preserves_bd := hp_bd'
      obj_zero := hobj_zero'
      c := c'
      c_zero := by
        have hc0 : c' 0 (Nat.zero_le (M + 1)) =
            eqToHom (L.D.extend_obj_le Q_bd_X X_succ i_succ (Nat.zero_le M) (Nat.zero_le (M + 1))) ≫
              L.c 0 (Nat.zero_le M) :=
          dite_eq_left_of_eq_true (eq_true (Nat.zero_le M))
        rw [hc0, L.c_zero, eqToHom_trans]
      c_comp := fun {k m} hk hm g => by
        dsimp [c']
        split_ifs with hm' hk' hk'₂
        · rw [L.D.extend_map_le_le Q_bd_X X_succ i_succ hk hm' hm g]
          simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
          rw [L.c_comp hk hm' g]
        · exfalso; exact hk' (hk.trans hm')
        · have hm_eq : m = M + 1 := by omega
          subst hm_eq
          rw [L.D.extend_map_le_succ Q_bd_X X_succ i_succ hk'₂ hk g]
          have h_id : eqToHom (L.D.extend_obj_succ Q_bd_X X_succ i_succ).symm ≫
              (eqToHom (L.D.extend_obj_not_le Q_bd_X X_succ i_succ hm' hm) ≫ c_succ) = c_succ := by
            change eqToHom (extendObj_succ L.D X_succ).symm ≫
              (eqToHom (extendObj_of_not_le L.D X_succ hm') ≫ c_succ) = c_succ
            rw [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
          simp only [Category.assoc]
          rw [h_id, hfac_X, Q_bd_X.fac c_bd_X k hk'₂ (boundarySuccSimplex.{u} hk'₂ g)]
        · have hm_eq : m = M + 1 := by omega
          have hk_eq : k = M + 1 := by omega
          subst hm_eq hk_eq
          have hg : g = 𝟙 (Henry.SemiSimplexCategory.mk (M + 1)) := hom_eq_id_of_end g
          rw [hg, D'.map_id, Category.id_comp]
      c_weq := fun k hk => by
        dsimp [c']
        split_ifs with hk'
        · exact weakEquivalences_eqToHom_comp _ _ (L.c_weq k hk')
        · exact weakEquivalences_eqToHom_comp _ _ hw_succ
      p_obj := hp_obj'
      p_map := fun {k m} hk hm g => by
        by_cases hm' : m ≤ M
        · have hk' : k ≤ M := hk.trans hm'
          rw [L.D.extend_map_le_le Q_bd_X X_succ i_succ hk hm' hm g, p.map_comp, p.map_comp,
            eqToHom_map, eqToHom_map, L.p_map hk hm' g]
          simp [Category.assoc]
        · have hm_eq : m = M + 1 := by omega
          subst hm_eq
          by_cases hk' : k ≤ M
          · rw [L.D.extend_map_le_succ Q_bd_X X_succ i_succ hk' hk g,
              p.map_comp, p.map_comp, p.map_comp, eqToHom_map, eqToHom_map, hp_i_succ]
            have h_leg : p.map (Q_bd_X.cocone.ι k hk' (boundarySuccSimplex.{u} hk' g)) ≫ e_bd.hom =
                eqToHom (L.p_obj k hk') ≫
                  h.map (ObjectProperty.homMk
                    (freeAlgKanMap (simplexToSemiSSet (boundarySuccSimplex.{u} hk' g))) :
                    stdSimplexCDelta.{u} k ⟶ boundaryCDelta.{u} (M + 1)) :=
              ι_liftedRealizationIso_hom p L.diagramIsoOn (hasDimLe_boundary M)
                Q_bd_X hp_bd_X Q_bd_Y hk' (boundarySuccSimplex.{u} hk' g)
            dsimp [i_Y]
            simp only [Category.assoc]
            rw [← Category.assoc (p.map (Q_bd_X.cocone.ι k hk' _)), h_leg]
            have h_inc : (ObjectProperty.homMk
                (freeAlgKanMap (simplexToSemiSSet (boundarySuccSimplex.{u} hk' g))) :
                stdSimplexCDelta.{u} k ⟶ boundaryCDelta.{u} (M + 1)) ≫
                boundaryCDeltaInclusion.{u} (M + 1) =
                stdSimplexCDeltaMap.{u} g := by
              apply ObjectProperty.hom_ext
              change freeAlgKanMap _ ≫ freeAlgKanMap _ = freeAlgKanMap _
              rw [← freeAlgKanMap_comp]
              rfl
            simp only [Category.assoc, eqToHom_trans_assoc]
            rw [← Category.assoc (h.map _), ← h.map_comp, h_inc]
            simp
          · have hk_eq : k = M + 1 := by omega
            subst hk_eq
            have hg : g = 𝟙 (Henry.SemiSimplexCategory.mk (M + 1)) := hom_eq_id_of_end g
            rw [hg, D'.map_id, stdSimplexCDeltaMap_id, p.map_id, h.map_id,
              Category.id_comp, eqToHom_trans, eqToHom_refl]
      p_c := fun k hk => by
        dsimp [c']
        split_ifs with hk'
        · rw [p.map_comp, eqToHom_map, L.p_c k hk', eqToHom_trans_assoc]
        · have hk_eq : k = M + 1 := by omega
          subst hk_eq
          rw [p.map_comp, eqToHom_map, hp_c_succ]
          dsimp [w_Y]
          simp }

include hp hh in
/-- Coherent sequence of lifted cosimplicial diagrams up to `M` for all `M : ℕ`. -/
noncomputable def liftedCosimplicialUpTo : ∀ M : ℕ, LiftedCosimplicialUpTo p h x₀ hx₀ M
  | 0 => liftedCosimplicialUpToZero p hp h x₀ hx₀
  | M + 1 => liftedCosimplicialUpToSucc p hp h hh x₀ hx₀ M (liftedCosimplicialUpTo M)

include hp hh in
lemma liftedCosimplicialUpTo_obj_agrees {M : ℕ} (k : ℕ) (hk : k ≤ M) :
    (liftedCosimplicialUpTo p hp h hh x₀ hx₀ (M + 1)).D.obj k (Nat.le_succ_of_le hk) =
      (liftedCosimplicialUpTo p hp h hh x₀ hx₀ M).D.obj k hk :=
  CosimplicialUpTo.extend_obj_le _ _ _ _ hk (Nat.le_succ_of_le hk)

include hp hh in
lemma liftedCosimplicialUpTo_map_agrees {M k m : ℕ} (hk : k ≤ m) (hm : m ≤ M)
    (g : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk m) :
    (liftedCosimplicialUpTo p hp h hh x₀ hx₀ (M + 1)).D.map hk (Nat.le_succ_of_le hm) g =
      eqToHom (liftedCosimplicialUpTo_obj_agrees p hp h hh x₀ hx₀ k (hk.trans hm)) ≫
        (liftedCosimplicialUpTo p hp h hh x₀ hx₀ M).D.map hk hm g ≫
        eqToHom (liftedCosimplicialUpTo_obj_agrees p hp h hh x₀ hx₀ m hm).symm :=
  CosimplicialUpTo.extend_map_le_le _ _ _ _ hk hm (Nat.le_succ_of_le hm) g

/-!
## Lifting canonical horn retractions along `p : X ⥤ Y`
-/

include hp hh in
/-- Chosen realization of `Λ^{n+1}_k` in `X` along `(liftedCosimplicialUpTo (n + 1)).D`. -/
noncomputable def liftedHornRealization (n : ℕ) (k : Fin (n + 2)) :
    SimplicialRealization (liftedCosimplicialUpTo p hp h hh x₀ hx₀ (n + 1)).D
      (SemiSSet.horn.{u} (n + 1) k).toFunctor :=
  haveI : IsCofibrationCategory X := hp.1.toIsCofibrationCategory
  subfunctorRealization (liftedCosimplicialUpTo p hp h hh x₀ hx₀ (n + 1)).BData
    (SemiSSet.horn.{u} (n + 1) k)
    (hasDimLe_subfunctor_stdSimplex (le_refl (n + 1)) (SemiSSet.horn.{u} (n + 1) k))

include hp hh in
/-- `p` preserves the universal cocone of `liftedHornRealization n k`. -/
lemma isUniversalCocone_mapFunctor_liftedHornRealization (n : ℕ) (k : Fin (n + 2)) :
    IsUniversalCocone ((liftedHornRealization p hp h hh x₀ hx₀ n k).cocone.mapFunctor p) := by
  have : IsCofibrationCategory X := hp.1.toIsCofibrationCategory
  exact isUniversalCocone_mapFunctor_of_subfunctor
    (liftedCosimplicialUpTo p hp h hh x₀ hx₀ (n + 1)).BData
    p hp.2.2.1.toIsCofibrationMorphism
    (liftedCosimplicialUpTo p hp h hh x₀ hx₀ (n + 1)).p_preserves_bd
    (SemiSSet.horn.{u} (n + 1) k)
    (hasDimLe_subfunctor_stdSimplex (le_refl (n + 1)) (SemiSSet.horn.{u} (n + 1) k))
    (liftedHornRealization p hp h hh x₀ hx₀ n k)

include hp hh in
/-- Canonical comparison isomorphism `p.obj (liftedHornRealization n k).pt ≅ h.obj (hornCDelta n k)`. -/
noncomputable def liftedHornIso (n : ℕ) (k : Fin (n + 2)) :
    p.obj (liftedHornRealization p hp h hh x₀ hx₀ n k).pt ≅ h.obj (hornCDelta.{u} n k) :=
  let L := liftedCosimplicialUpTo p hp h hh x₀ hx₀ (n + 1)
  have hh_horn : IsUniversalCocone
      ((hornCDeltaRealization.{u} (n + 1) n (le_refl (n + 1)) k).cocone.mapFunctor h) :=
    isUniversalCocone_mapFunctor_freeCDeltaCocone h hh.toIsCofibrationMorphism
      (SemiSSet.horn.{u} (n + 1) k)
      (hasDimLe_subfunctor_stdSimplex (le_refl (n + 1)) (SemiSSet.horn.{u} (n + 1) k))
  liftedRealizationIso p L.diagramIsoOn
    (hasDimLe_subfunctor_stdSimplex (le_refl (n + 1)) (SemiSSet.horn.{u} (n + 1) k))
    (liftedHornRealization p hp h hh x₀ hx₀ n k)
    (isUniversalCocone_mapFunctor_liftedHornRealization p hp h hh x₀ hx₀ n k)
    hh_horn.toRealization

include hp hh in
/-- For every `n : ℕ` and `k : Fin (n + 2)`, there exists a retraction
`r_X : (liftedCosimplicialUpTo (n + 1)).D.obj (n + 1) ⟶ (liftedHornRealization n k).pt` in `X`
of the horn inclusion in `X`, lifting `h.map (canonicalHornRetraction n k)` along `p`. -/
theorem exists_liftedHornRetraction (n : ℕ) (k : Fin (n + 2)) :
    let L := liftedCosimplicialUpTo p hp h hh x₀ hx₀ (n + 1)
    let Q_horn := liftedHornRealization p hp h hh x₀ hx₀ n k
    let i_horn := SimplicialRealization.realizationMap Q_horn
      (stdSimplexRealization L.D (n + 1) (le_refl (n + 1)))
      (SemiSSet.horn.{u} (n + 1) k).ι
    ∃ r_X : L.D.obj (n + 1) (le_refl (n + 1)) ⟶ Q_horn.pt,
      i_horn ≫ r_X = 𝟙 Q_horn.pt ∧
      p.map r_X =
        eqToHom (L.p_obj (n + 1) (le_refl (n + 1))) ≫
          h.map (canonicalHornRetraction.{u} n k) ≫
          (liftedHornIso p hp h hh x₀ hx₀ n k).inv := by
  have : IsCylinderCategory X := hp.1
  have : IsCofibrationCategory X := hp.1.toIsCofibrationCategory
  let L := liftedCosimplicialUpTo p hp h hh x₀ hx₀ (n + 1)
  let Q_horn := liftedHornRealization p hp h hh x₀ hx₀ n k
  let i_horn := SimplicialRealization.realizationMap Q_horn
    (stdSimplexRealization L.D (n + 1) (le_refl (n + 1)))
    (SemiSSet.horn.{u} (n + 1) k).ι
  have hi_horn : cofibrations X i_horn :=
    cofibration_realizationMap_iota L.BData (le_refl (n + 1))
      (SemiSSet.horn.{u} (n + 1) k) Q_horn
  have hw_horn : weakEquivalences X i_horn :=
    weakEquivalence_horn_realizationMap L.BData (fun hk hm g => L.map_weq hp hk hm g)
      n (le_refl (n + 1)) k Q_horn
  have hh_horn : IsUniversalCocone
      ((hornCDeltaRealization.{u} (n + 1) n (le_refl (n + 1)) k).cocone.mapFunctor h) :=
    isUniversalCocone_mapFunctor_freeCDeltaCocone h hh.toIsCofibrationMorphism
      (SemiSSet.horn.{u} (n + 1) k)
      (hasDimLe_subfunctor_stdSimplex (le_refl (n + 1)) (SemiSSet.horn.{u} (n + 1) k))
  let Q_horn_Y := hh_horn.toRealization
  have hp_i_horn : p.map i_horn =
      (liftedHornIso p hp h hh x₀ hx₀ n k).hom ≫
        SimplicialRealization.realizationMap Q_horn_Y
          (stdSimplexRealization ((stdCosimplicialUpTo.{u} (n + 1)).mapFunctor h)
            (n + 1) (le_refl (n + 1)))
          (SemiSSet.horn.{u} (n + 1) k).ι ≫
        eqToHom (L.p_obj (n + 1) (le_refl (n + 1))).symm :=
    map_realizationMap_stdSimplex_eq_liftedRealizationIso p L.diagramIsoOn
      (hasDimLe_subfunctor_stdSimplex (le_refl (n + 1)) (SemiSSet.horn.{u} (n + 1) k))
      Q_horn (isUniversalCocone_mapFunctor_liftedHornRealization p hp h hh x₀ hx₀ n k)
      Q_horn_Y (le_refl (n + 1)) (SemiSSet.horn.{u} (n + 1) k).ι
  have h_real_Y : SimplicialRealization.realizationMap Q_horn_Y
      (stdSimplexRealization ((stdCosimplicialUpTo.{u} (n + 1)).mapFunctor h)
        (n + 1) (le_refl (n + 1)))
      (SemiSSet.horn.{u} (n + 1) k).ι =
      h.map (hornInclusionCDelta.{u} n k) := by
    apply Q_horn_Y.hom_ext
    intro m hm x
    have h1 := SimplicialRealization.ι_realizationMap Q_horn_Y
      (stdSimplexRealization ((stdCosimplicialUpTo.{u} (n + 1)).mapFunctor h)
        (n + 1) (le_refl (n + 1)))
      (SemiSSet.horn.{u} (n + 1) k).ι m hm x
    have h2 := congrArg (fun f => h.map f)
      (SimplicialRealization.ι_realizationMap
        (hornCDeltaRealization.{u} (n + 1) n (le_refl (n + 1)) k)
        (stdSimplexRealization (stdCosimplicialUpTo.{u} (n + 1)) (n + 1) (le_refl (n + 1)))
        (SemiSSet.horn.{u} (n + 1) k).ι m hm x)
    have h3 : h.map
        ((hornCDeltaRealization.{u} (n + 1) n (le_refl (n + 1)) k).cocone.ι m hm x ≫
          SimplicialRealization.realizationMap
            (hornCDeltaRealization.{u} (n + 1) n (le_refl (n + 1)) k)
            (stdSimplexRealization (stdCosimplicialUpTo.{u} (n + 1)) (n + 1) (le_refl (n + 1)))
            (SemiSSet.horn.{u} (n + 1) k).ι) =
        Q_horn_Y.cocone.ι m hm x ≫ h.map (hornInclusionCDelta.{u} n k) := by
      rw [h.map_comp, realizationMap_hornCDeltaRealization (n + 1) n (le_refl (n + 1)) k]
      rfl
    exact h1.trans (h2.symm.trans h3)
  rw [h_real_Y] at hp_i_horn
  let r_Y : p.obj (L.D.obj (n + 1) (le_refl (n + 1))) ⟶ p.obj Q_horn.pt :=
    eqToHom (L.p_obj (n + 1) (le_refl (n + 1))) ≫
      h.map (canonicalHornRetraction.{u} n k) ≫
      (liftedHornIso p hp h hh x₀ hx₀ n k).inv
  have hr_Y : p.map i_horn ≫ r_Y = 𝟙 (p.obj Q_horn.pt) := by
    rw [hp_i_horn]
    change ((liftedHornIso p hp h hh x₀ hx₀ n k).hom ≫
        h.map (hornInclusionCDelta.{u} n k) ≫
        eqToHom (L.p_obj (n + 1) (le_refl (n + 1))).symm) ≫
      (eqToHom (L.p_obj (n + 1) (le_refl (n + 1))) ≫
        h.map (canonicalHornRetraction.{u} n k) ≫
        (liftedHornIso p hp h hh x₀ hx₀ n k).inv) =
      𝟙 (p.obj Q_horn.pt)
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← Category.assoc (h.map (hornInclusionCDelta.{u} n k)), ← h.map_comp,
      hornInclusionCDelta_comp_canonicalHornRetraction, h.map_id, Category.id_comp,
      Iso.hom_inv_id]
  exact hp.2.2.2.1.lift_retraction i_horn hi_horn hw_horn r_Y hr_Y

end LiftedCosimplicial

end HomotopyHypothesis.Cylinder.SimplicialCategory
