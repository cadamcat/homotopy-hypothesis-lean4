import HomotopyHypothesis.Cylinder.SimplicialCategory.HornFiltration
import HomotopyHypothesis.Cylinder.SimplicialCategory.SimplexRealization
import HomotopyHypothesis.Cylinder.SimplicialCategory.SimplexSubfunctors
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
/-!
# Skeletal realizations of subfunctors and horn realizations in cylinder categories

This file proves:
1. Uniqueness of `SimplicialRealization` up to canonical cocone isomorphism, so that cofibrancy and
   weak-equivalence properties of `realizationMap` and functorial preservation of `IsUniversalCocone`
   are independent of the choice of realizations.
2. The general single-simplex attachment theorem `attachSimplexRealization`: if `S ⊓ simplexSubfunctor σ`
   is identified via `subfunctorIsoInf` with `K : Subfunctor Δ_m` whose inclusion `Q_K.pt ⟶ D.obj m`
   is a cofibration (resp. trivial cofibration), then `S ⊔ simplexSubfunctor σ` has a realization
   obtained by pushing out along `Q_K.pt ⟶ D.obj m`, the inclusion `Q_S.pt ⟶ Q_{S ⊔ σ}.pt` is a
   cofibration (resp. trivial cofibration), and any cofibration morphism `G` preserving `Q_K` and
   `Q_S` also preserves `Q_{S ⊔ σ}`.
3. Skeletal realization theorem for `CosimplicialBoundaryData`: every subfunctor `S` of `Δ_N` with
   `HasDimLe M S.toFunctor` admits a realization `subfunctorRealization`, every inclusion `S ≤ T`
   with `HasDimLe M T.toFunctor` induces a cofibration in `C`, and every cofibration morphism `G`
   preserving boundary realizations preserves all subfunctor realizations.
4. Horn inclusion theorem `weakEquivalence_horn_realizationMap`: in any cylinder category `C`, if
   all maps of `D : CosimplicialUpTo C M` are weak equivalences and `D` has `CosimplicialBoundaryData`,
   then for every `n + 1 ≤ M` and `k : Fin (n + 2)` the horn inclusion `Q_{Λ^{n+1}_k}.pt ⟶ D.obj (n + 1)`
   is a trivial cofibration in `C`.
5. Extension of a truncated cosimplicial diagram `D : CosimplicialUpTo C M` to `M + 1` from a single
   morphism `Q_{∂Δ_{M+1}}.pt ⟶ X_{M+1}` (`CosimplicialUpTo.extend`).
-/

universe v₃ u₃ v₂ u₂ u

open CategoryTheory Limits HomotopicalAlgebra Opposite ConcreteCategory

namespace HomotopyHypothesis.Cylinder.SimplicialCategory

open HomotopyHypothesis.Henry

/-!
## Basic closure properties in cofibration and cylinder categories
-/

section CategoryHelpers

variable {C : Type u₂} [Category.{v₂} C] [CategoryWithCofibrations C]

lemma cofibrations_of_isIso [IsCofibrationCategory C] {X Y : C} (f : X ⟶ Y) [IsIso f] :
    cofibrations C f :=
  IsCofibrationCategory.isomorphisms_le f (MorphismProperty.isomorphisms.infer_property f)

lemma cofibrations_id [IsCofibrationCategory C] (X : C) :
    cofibrations C (𝟙 X) :=
  cofibrations_of_isIso (𝟙 X)

lemma cofibrations_comp [IsCofibrationCategory C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : cofibrations C f) (hg : cofibrations C g) :
    cofibrations C (f ≫ g) :=
  IsCofibrationCategory.isMultiplicative.comp_mem f g hf hg

lemma cofibrations_of_isPushout [IsCofibrationCategory C] {A B X P : C}
    {i : A ⟶ B} {f : A ⟶ X} {k : B ⟶ P} {j : X ⟶ P}
    (sq : IsPushout i f k j) (hi : cofibrations C i) :
    cofibrations C j :=
  IsCofibrationCategory.isStableUnderCobaseChange.of_isPushout sq.flip hi

variable [CategoryWithWeakEquivalences C] [IsCylinderCategory C]

lemma weakEquivalences_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] :
    weakEquivalences C f :=
  IsCylinderCategory.isomorphisms_le_weakEquivalences f
    (MorphismProperty.isomorphisms.infer_property f)

lemma weakEquivalences_id (X : C) :
    weakEquivalences C (𝟙 X) :=
  weakEquivalences_of_isIso (𝟙 X)

lemma weakEquivalences_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : weakEquivalences C f) (hg : weakEquivalences C g) :
    weakEquivalences C (f ≫ g) :=
  IsCylinderCategory.weakEquivalences_isMultiplicative.comp_mem f g hf hg

lemma weakEquivalences_of_comp_left {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : weakEquivalences C f) (hfg : weakEquivalences C (f ≫ g)) :
    weakEquivalences C g := by
  have h := IsCylinderCategory.twoOutOfSix (𝟙 X) f g (by rw [Category.id_comp]; exact hf) hfg
  exact h.2.2.1

lemma weakEquivalences_of_comp_right {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg : weakEquivalences C g) (hfg : weakEquivalences C (f ≫ g)) :
    weakEquivalences C f := by
  have h := IsCylinderCategory.twoOutOfSix f g (𝟙 Z) hfg (by rw [Category.comp_id]; exact hg)
  exact h.1

end CategoryHelpers

/-!
## Independence of choice of `SimplicialRealization`
-/

section RealizationIndependence

variable {C : Type u₂} [Category.{v₂} C] {M : ℕ} {D : CosimplicialUpTo C M}

/-- Isomorphism `S₁.toFunctor ≅ S₂.toFunctor` from mutual inclusion `S₁ ≤ S₂` and `S₂ ≤ S₁`. -/
@[simps]
def subfunctorIsoOfLe {B : SemiSSet.{u}} {S₁ S₂ : Subfunctor B} (h₁₂ : S₁ ≤ S₂) (h₂₁ : S₂ ≤ S₁) :
    S₁.toFunctor ≅ S₂.toFunctor where
  hom := Subfunctor.homOfLe h₁₂
  inv := Subfunctor.homOfLe h₂₁
  hom_inv_id := rfl
  inv_hom_id := rfl

lemma isIso_realizationMap_of_le_antisymm {B : SemiSSet.{u}} {S₁ S₂ : Subfunctor B}
    (h₁₂ : S₁ ≤ S₂) (h₂₁ : S₂ ≤ S₁)
    (Q₁ : SimplicialRealization D S₁.toFunctor) (Q₂ : SimplicialRealization D S₂.toFunctor) :
    IsIso (SimplicialRealization.realizationMap Q₁ Q₂ (Subfunctor.homOfLe h₁₂)) := by
  change IsIso (Q₁.realizationIso Q₂ (subfunctorIsoOfLe h₁₂ h₂₁)).hom
  infer_instance

lemma realizationMap_eq_comp_realizationIsoRefl {F₁ F₂ : SemiSSet.{u}}
    (Q₁ Q₁' : SimplicialRealization D F₁) (Q₂ Q₂' : SimplicialRealization D F₂) (α : F₁ ⟶ F₂) :
    SimplicialRealization.realizationMap Q₁' Q₂' α =
      (Q₁'.realizationIso Q₁ (Iso.refl F₁)).hom ≫
        SimplicialRealization.realizationMap Q₁ Q₂ α ≫
        (Q₂.realizationIso Q₂' (Iso.refl F₂)).hom := by
  rw [SimplicialRealization.realizationIso_hom, SimplicialRealization.realizationIso_hom,
    ← SimplicialRealization.realizationMap_comp, ← SimplicialRealization.realizationMap_comp,
    Iso.refl_hom, Category.id_comp, Iso.refl_hom, Category.comp_id]

lemma cofibration_realizationMap_of_realizations [CategoryWithCofibrations C]
    [IsCofibrationCategory C] {F₁ F₂ : SemiSSet.{u}}
    (Q₁ Q₁' : SimplicialRealization D F₁) (Q₂ Q₂' : SimplicialRealization D F₂) (α : F₁ ⟶ F₂)
    (h : cofibrations C (SimplicialRealization.realizationMap Q₁ Q₂ α)) :
    cofibrations C (SimplicialRealization.realizationMap Q₁' Q₂' α) := by
  rw [realizationMap_eq_comp_realizationIsoRefl Q₁ Q₁' Q₂ Q₂' α]
  exact cofibrations_comp _ _ (cofibrations_of_isIso _)
    (cofibrations_comp _ _ h (cofibrations_of_isIso _))

lemma weakEquivalence_realizationMap_of_realizations [CategoryWithCofibrations C]
    [CategoryWithWeakEquivalences C] [IsCylinderCategory C] {F₁ F₂ : SemiSSet.{u}}
    (Q₁ Q₁' : SimplicialRealization D F₁) (Q₂ Q₂' : SimplicialRealization D F₂) (α : F₁ ⟶ F₂)
    (h : weakEquivalences C (SimplicialRealization.realizationMap Q₁ Q₂ α)) :
    weakEquivalences C (SimplicialRealization.realizationMap Q₁' Q₂' α) := by
  rw [realizationMap_eq_comp_realizationIsoRefl Q₁ Q₁' Q₂ Q₂' α]
  exact weakEquivalences_comp _ _ (weakEquivalences_of_isIso _)
    (weakEquivalences_comp _ _ h (weakEquivalences_of_isIso _))

lemma isUniversalCocone_postcomp_iso {F : SemiSSet.{u}} {pt pt' : C}
    {cocone : SimplicialCocone D F pt} (h : IsUniversalCocone cocone) (e : pt ≅ pt') :
    IsUniversalCocone (cocone.postcomp e.hom) := by
  intro z c
  obtain ⟨m, hm, hm_uniq⟩ := h c
  refine ⟨e.inv ≫ m, ?_, ?_⟩
  · intro k hk x
    change (cocone.ι k hk x ≫ e.hom) ≫ (e.inv ≫ m) = c.ι k hk x
    rw [Category.assoc, ← Category.assoc e.hom, Iso.hom_inv_id, Category.id_comp]
    exact hm k hk x
  · intro m' hm'
    rw [Iso.eq_inv_comp]
    apply hm_uniq (e.hom ≫ m')
    intro k hk x
    rw [← Category.assoc]
    exact hm' k hk x

lemma isUniversalCocone_mapFunctor_of_realization {C' : Type u₃} [Category.{v₃} C'] (G : C ⥤ C')
    {F : SemiSSet.{u}} (Q₁ Q₂ : SimplicialRealization D F)
    (h₁ : IsUniversalCocone (Q₁.cocone.mapFunctor G)) :
    IsUniversalCocone (Q₂.cocone.mapFunctor G) := by
  let e : G.obj Q₁.pt ≅ G.obj Q₂.pt := G.mapIso (Q₁.realizationIso Q₂ (Iso.refl F))
  have heq : (Q₁.cocone.mapFunctor G).postcomp e.hom = Q₂.cocone.mapFunctor G := by
    ext k hk x
    change G.map (Q₁.cocone.ι k hk x) ≫ G.map (Q₁.realizationMap Q₂ (𝟙 F)) =
      G.map (Q₂.cocone.ι k hk x)
    rw [← G.map_comp, SimplicialRealization.ι_realizationMap]
    rfl
  rw [← heq]
  exact isUniversalCocone_postcomp_iso h₁ e

end RealizationIndependence

/-!
## Single-simplex attachment theorem
-/

section AttachSimplex

variable {C : Type u₂} [Category.{v₂} C] {M m N : ℕ} {D : CosimplicialUpTo C M} (hm : m ≤ M)
  (S : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)))
  (σ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk N)
  (K : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m)))
  (hK : ∀ ⦃Δ : Henry.SemiSimplexCategoryᵒᵖ⦄
    (x : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m)).obj Δ),
    ULift.up (ULift.down x ≫ σ) ∈ S.obj Δ ↔ x ∈ K.obj Δ)

/-- Under the intersection isomorphism `subfunctorIsoInf S σ K hK`, the right inclusion map
`S ⊓ simplexSubfunctor σ ⟶ simplexSubfunctor σ` induces the map `Q_K.pt ⟶ D.obj m hm` induced by
`K.ι : K.toFunctor ⟶ Δ_m`. -/
lemma realizationMap_subfunctorIsoInf_right (Q_K : SimplicialRealization D K.toFunctor) :
    SimplicialRealization.realizationMap
      (Q_K.ofIso (subfunctorIsoInf S σ K hK).symm)
      (simplexSubfunctorRealization D hm σ)
      (Subfunctor.homOfLe inf_le_right) =
    SimplicialRealization.realizationMap Q_K (stdSimplexRealization D m hm) K.ι := by
  unfold simplexSubfunctorRealization
  rw [SimplicialRealization.realizationMap_ofIso_left,
    SimplicialRealization.realizationMap_ofIso_right]
  congr 1
  rw [Iso.symm_inv, Iso.symm_hom, subfunctorIsoInf_hom_comp_right,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- If the inclusion `Q_K.pt ⟶ D.obj m hm` is a cofibration in `C`, then `S ⊔ simplexSubfunctor σ`
admits a realization `Q_sup` obtained by pushout along `Q_K.pt ⟶ D.obj m hm`, the inclusion
`Q_S.pt ⟶ Q_sup.pt` is a cofibration in `C`, and any cofibration morphism `G` preserving `Q_K`
and `Q_S` also preserves `Q_sup`. -/
theorem attachSimplexRealization [CategoryWithCofibrations C] [IsCofibrationCategory C]
    (Q_K : SimplicialRealization D K.toFunctor)
    (Q_S : SimplicialRealization D S.toFunctor)
    (hi_K : cofibrations C
      (SimplicialRealization.realizationMap Q_K (stdSimplexRealization D m hm) K.ι)) :
    ∃ Q_sup : SimplicialRealization D (S ⊔ simplexSubfunctor.{u} σ).toFunctor,
      IsPushout
        (SimplicialRealization.realizationMap
          (Q_K.ofIso (subfunctorIsoInf S σ K hK).symm) Q_S (Subfunctor.homOfLe inf_le_left))
        (SimplicialRealization.realizationMap Q_K (stdSimplexRealization D m hm) K.ι)
        (SimplicialRealization.realizationMap Q_S Q_sup (Subfunctor.homOfLe le_sup_left))
        (SimplicialRealization.realizationMap
          (simplexSubfunctorRealization D hm σ) Q_sup (Subfunctor.homOfLe le_sup_right)) ∧
      cofibrations C
        (SimplicialRealization.realizationMap Q_S Q_sup (Subfunctor.homOfLe le_sup_left)) ∧
      ∀ {C' : Type u₃} [Category.{v₃} C'] [CategoryWithCofibrations C'] (G : C ⥤ C'),
        IsCofibrationMorphism G →
        IsUniversalCocone (Q_K.cocone.mapFunctor G) →
        IsUniversalCocone (Q_S.cocone.mapFunctor G) →
        IsUniversalCocone (Q_sup.cocone.mapFunctor G) := by
  let Q₀ := Q_K.ofIso (subfunctorIsoInf S σ K hK).symm
  let Q₂ := simplexSubfunctorRealization D hm σ
  let i₁ := SimplicialRealization.realizationMap Q₀ Q_S (Subfunctor.homOfLe inf_le_left)
  let i₂ := SimplicialRealization.realizationMap Q₀ Q₂ (Subfunctor.homOfLe inf_le_right)
  have hi₂_eq : i₂ = SimplicialRealization.realizationMap Q_K (stdSimplexRealization D m hm) K.ι :=
    realizationMap_subfunctorIsoInf_right hm S σ K hK Q_K
  have hi₂ : cofibrations C i₂ := by
    rw [hi₂_eq]
    exact hi_K
  have : HasPushout i₂ i₁ := IsCofibrationCategory.hasPushout i₂ i₁ hi₂
  let P : C := pushout i₂ i₁
  let j₂ : Q₂.pt ⟶ P := pushout.inl i₂ i₁
  let j₁ : Q_S.pt ⟶ P := pushout.inr i₂ i₁
  have sq₀ : IsPushout i₁ i₂ j₁ j₂ := (IsPushout.of_hasPushout i₂ i₁).flip
  have huniv : IsUniversalCocone (supCocone Q₀ Q_S Q₂ j₁ j₂ sq₀.w) :=
    (isPushout_iff_isUniversalCocone_supCocone Q₀ Q_S Q₂ j₁ j₂ sq₀.w).mp sq₀
  let Q_sup : SimplicialRealization D (S ⊔ simplexSubfunctor.{u} σ).toFunctor :=
    huniv.toRealization
  have sq : IsPushout i₁ i₂
      (SimplicialRealization.realizationMap Q_S Q_sup (Subfunctor.homOfLe le_sup_left))
      (SimplicialRealization.realizationMap Q₂ Q_sup (Subfunctor.homOfLe le_sup_right)) :=
    isPushout_of_realizations Q₀ Q_S Q₂ Q_sup
  refine ⟨Q_sup, ?_, cofibrations_of_isPushout sq.flip hi₂, ?_⟩
  · rw [← hi₂_eq]
    exact sq
  · intro C' _ _ G hG hGK hGS
    have hG₀ : IsUniversalCocone (Q₀.cocone.mapFunctor G) :=
      isUniversalCocone_precomp_iso hGK (subfunctorIsoInf S σ K hK).symm
    have hG₂ : IsUniversalCocone (Q₂.cocone.mapFunctor G) :=
      isUniversalCocone_mapFunctor_simplexSubfunctorRealization G D hm σ
    have hsqG : IsPushout
        (G.map i₁) (G.map i₂)
        (G.map (SimplicialRealization.realizationMap Q_S Q_sup (Subfunctor.homOfLe le_sup_left)))
        (G.map (SimplicialRealization.realizationMap Q₂ Q_sup (Subfunctor.homOfLe le_sup_right))) :=
      (hG.map_isPushout i₂ i₁ _ _ sq.flip hi₂).flip
    exact isUniversalCocone_mapFunctor_of_sup Q₀ Q_S Q₂ G Q_sup hG₀ hGS hG₂ hsqG

include hK in
/-- If in addition `C` is a cylinder category and `Q_K.pt ⟶ D.obj m hm` is a weak equivalence in `C`,
then for any realizations `Q_S` of `S` and `Q_sup` of `S ⊔ simplexSubfunctor σ`, the inclusion
`Q_S.pt ⟶ Q_sup.pt` is a weak equivalence in `C`. -/
theorem weakEquivalence_of_attachSimplexRealization [CategoryWithCofibrations C]
    [CategoryWithWeakEquivalences C] [IsCylinderCategory C]
    (Q_K : SimplicialRealization D K.toFunctor)
    (Q_S : SimplicialRealization D S.toFunctor)
    (Q_sup : SimplicialRealization D (S ⊔ simplexSubfunctor.{u} σ).toFunctor)
    (hi_K : cofibrations C
      (SimplicialRealization.realizationMap Q_K (stdSimplexRealization D m hm) K.ι))
    (hw_K : weakEquivalences C
      (SimplicialRealization.realizationMap Q_K (stdSimplexRealization D m hm) K.ι)) :
    weakEquivalences C
      (SimplicialRealization.realizationMap Q_S Q_sup (Subfunctor.homOfLe le_sup_left)) := by
  obtain ⟨Q_sup', sq, _, _⟩ :=
    attachSimplexRealization.{v₂, u₂, v₂, u₂, u} hm S σ K hK Q_K Q_S hi_K
  have hw' : weakEquivalences C
      (SimplicialRealization.realizationMap Q_S Q_sup' (Subfunctor.homOfLe le_sup_left)) :=
    IsCylinderCategory.trivialCofibration_cobaseChange _ _ _ _ sq.flip hi_K hw_K
  exact weakEquivalence_realizationMap_of_realizations Q_S Q_S Q_sup' Q_sup _ hw'

end AttachSimplex

/-!
## Skeletal realizations for `CosimplicialBoundaryData`
-/

/-- Boundary realization data for a truncated cosimplicial diagram `D : CosimplicialUpTo C M`:
chosen realizations of `∂Δ_m` (`m ≤ M`) whose boundary inclusions `Q_{∂Δ_m}.pt ⟶ D.obj m` are
cofibrations in `C`. -/
structure CosimplicialBoundaryData {C : Type u₂} [Category.{v₂} C] [CategoryWithCofibrations C]
    {M : ℕ} (D : CosimplicialUpTo C M) where
  bdRealization : ∀ (m : ℕ), m ≤ M →
    SimplicialRealization D (SemiSSet.boundary.{u} m).toFunctor
  bdInclusion_cofibration : ∀ (m : ℕ) (hm : m ≤ M),
    cofibrations C
      (SimplicialRealization.realizationMap (bdRealization m hm)
        (stdSimplexRealization D m hm) (SemiSSet.boundary.{u} m).ι)

/-- A functor `G : C ⥤ C'` preserves the boundary realizations of `BData` if it sends each
`(BData.bdRealization m hm).cocone` (`m ≤ M`) to a universal cocone in `C'`. -/
def PreservesBoundaryRealizations {C : Type u₂} [Category.{v₂} C] [CategoryWithCofibrations C]
    {C' : Type u₃} [Category.{v₃} C'] {M : ℕ} {D : CosimplicialUpTo C M}
    (BData : CosimplicialBoundaryData.{v₂, u₂, u} D) (G : C ⥤ C') : Prop :=
  ∀ (m : ℕ) (hm : m ≤ M), IsUniversalCocone ((BData.bdRealization m hm).cocone.mapFunctor G)

section SkeletalRealization

variable {C : Type u₂} [Category.{v₂} C] [CategoryWithCofibrations C] [IsCofibrationCategory C]
  {M : ℕ} {D : CosimplicialUpTo C M} (BData : CosimplicialBoundaryData.{v₂, u₂, u} D)

/-- Attaching a finite set `F` of `m`-simplices (`m ≤ M`) whose proper faces lie in `S'` produces
a realization of `addCellsAt m S' F`, a cofibration `Q_{S'}.pt ⟶ Q_{addCellsAt m S' F}.pt`, and
preserves `IsUniversalCocone (·.cocone.mapFunctor G)` for any cofibration morphism `G` preserving
boundary realizations. -/
theorem exists_realization_addCellsAt {m N : ℕ} (hm : m ≤ M)
    (S' : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)))
    (F : Finset (Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk N))
    (hF_bd : ∀ σ ∈ F, ∀ ⦃Δ : Henry.SemiSimplexCategoryᵒᵖ⦄
      (g : unop Δ ⟶ Henry.SemiSimplexCategory.mk m),
      (unop Δ).obj.len < m → ULift.up (g ≫ σ) ∈ S'.obj Δ)
    (Q_S' : SimplicialRealization D S'.toFunctor)
    {C' : Type u₃} [Category.{v₃} C'] [CategoryWithCofibrations C'] (G : C ⥤ C')
    (hG : IsCofibrationMorphism G) (hG_bd : PreservesBoundaryRealizations BData G) :
    ∃ Q_add : SimplicialRealization D (addCellsAt m S' F).toFunctor,
      cofibrations C
        (SimplicialRealization.realizationMap Q_S' Q_add
          (Subfunctor.homOfLe
            (le_addCellsAt_empty m S' |>.trans (addCellsAt_mono m S' (Finset.empty_subset F))))) ∧
      (IsUniversalCocone (Q_S'.cocone.mapFunctor G) →
        IsUniversalCocone (Q_add.cocone.mapFunctor G)) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    let e := subfunctorIsoOfLe (le_addCellsAt_empty m S') (addCellsAt_empty_le m S')
    let Q_empty := Q_S'.ofIso e.symm
    refine ⟨Q_empty, ?_, ?_⟩
    · have : IsIso (SimplicialRealization.realizationMap Q_S' Q_empty
          (Subfunctor.homOfLe (le_addCellsAt_empty m S'))) :=
        isIso_realizationMap_of_le_antisymm (le_addCellsAt_empty m S') (addCellsAt_empty_le m S')
          Q_S' Q_empty
      exact cofibrations_of_isIso _
    · intro hGS'
      exact isUniversalCocone_precomp_iso hGS' e.symm
  | @insert σ F hσ_not_mem ih =>
    have hF_bd' : ∀ τ ∈ F, ∀ ⦃Δ : Henry.SemiSimplexCategoryᵒᵖ⦄
        (g : unop Δ ⟶ Henry.SemiSimplexCategory.mk m),
        (unop Δ).obj.len < m → ULift.up (g ≫ τ) ∈ S'.obj Δ :=
      fun τ hτ => hF_bd τ (Finset.mem_insert_of_mem hτ)
    obtain ⟨Q_F, hc_F, hG_F⟩ := ih hF_bd'
    have hle_F : S' ≤ addCellsAt m S' F :=
      le_addCellsAt_empty m S' |>.trans (addCellsAt_mono m S' (Finset.empty_subset F))
    have hle_step : addCellsAt m S' F ≤ addCellsAt m S' (insert σ F) :=
      addCellsAt_mono m S' (Finset.subset_insert σ F)
    by_cases hσ_mem : ULift.up σ ∈ (addCellsAt m S' F).obj (op (Henry.SemiSimplexCategory.mk m))
    · have hle_rev : addCellsAt m S' (insert σ F) ≤ addCellsAt m S' F := by
        intro Δ x hx
        rcases addCellsAt_insert_le_sup m S' F σ Δ hx with hxF | ⟨g, rfl⟩
        · exact hxF
        · exact (addCellsAt m S' F).map g.op hσ_mem
      let e_step := subfunctorIsoOfLe hle_step hle_rev
      let Q_ins := Q_F.ofIso e_step.symm
      refine ⟨Q_ins, ?_, ?_⟩
      · have heq : SimplicialRealization.realizationMap Q_S' Q_ins
            (Subfunctor.homOfLe (hle_F.trans hle_step)) =
            SimplicialRealization.realizationMap Q_S' Q_F (Subfunctor.homOfLe hle_F) ≫
              SimplicialRealization.realizationMap Q_F Q_ins (Subfunctor.homOfLe hle_step) :=
          SimplicialRealization.realizationMap_comp Q_S' Q_F Q_ins
            (Subfunctor.homOfLe hle_F) (Subfunctor.homOfLe hle_step)
        rw [heq]
        have : IsIso (SimplicialRealization.realizationMap Q_F Q_ins
            (Subfunctor.homOfLe hle_step)) :=
          isIso_realizationMap_of_le_antisymm hle_step hle_rev Q_F Q_ins
        exact cofibrations_comp _ _ hc_F (cofibrations_of_isIso _)
      · intro hGS'
        exact isUniversalCocone_precomp_iso (hG_F hGS') e_step.symm
    · have hσ_bd' : ∀ ⦃Δ : Henry.SemiSimplexCategoryᵒᵖ⦄
          (g : unop Δ ⟶ Henry.SemiSimplexCategory.mk m),
          (unop Δ).obj.len < m → ULift.up (g ≫ σ) ∈ (addCellsAt m S' F).obj Δ :=
        fun Δ g hlt => Or.inl (hF_bd σ (Finset.mem_insert_self σ F) g hlt)
      have hK_bd : ∀ ⦃Δ : Henry.SemiSimplexCategoryᵒᵖ⦄
          (x : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m)).obj Δ),
          ULift.up (ULift.down x ≫ σ) ∈ (addCellsAt m S' F).obj Δ ↔
            x ∈ (SemiSSet.boundary.{u} m).obj Δ :=
        fun _ x => mem_subfunctor_iff_mem_boundary (addCellsAt m S' F) σ hσ_mem hσ_bd' x
      obtain ⟨Q_sup, _, hc_sup, hG_sup⟩ :=
        attachSimplexRealization hm (addCellsAt m S' F) σ (SemiSSet.boundary.{u} m) hK_bd
          (BData.bdRealization m hm) Q_F (BData.bdInclusion_cofibration m hm)
      let e_ins := subfunctorIsoOfLe
        (sup_le_addCellsAt_insert m S' F σ) (addCellsAt_insert_le_sup m S' F σ)
      let Q_ins := Q_sup.ofIso e_ins.symm
      refine ⟨Q_ins, ?_, ?_⟩
      · have heq : SimplicialRealization.realizationMap Q_S' Q_ins
            (Subfunctor.homOfLe (hle_F.trans hle_step)) =
            SimplicialRealization.realizationMap Q_S' Q_F (Subfunctor.homOfLe hle_F) ≫
              SimplicialRealization.realizationMap Q_F Q_sup (Subfunctor.homOfLe le_sup_left) ≫
              SimplicialRealization.realizationMap Q_sup Q_ins
                (Subfunctor.homOfLe (sup_le_addCellsAt_insert m S' F σ)) := by
          rw [← SimplicialRealization.realizationMap_comp,
            ← SimplicialRealization.realizationMap_comp]
          rfl
        rw [heq]
        have : IsIso (SimplicialRealization.realizationMap Q_sup Q_ins
            (Subfunctor.homOfLe (sup_le_addCellsAt_insert m S' F σ))) :=
          isIso_realizationMap_of_le_antisymm
            (sup_le_addCellsAt_insert m S' F σ) (addCellsAt_insert_le_sup m S' F σ) Q_sup Q_ins
        exact cofibrations_comp _ _ hc_F (cofibrations_comp _ _ hc_sup (cofibrations_of_isIso _))
      · intro hGS'
        exact isUniversalCocone_precomp_iso
          (hG_sup G hG (hG_bd m hm) (hG_F hGS')) e_ins.symm

/-- Step from `skelSubfunctor S T m` to `skelSubfunctor S T (m + 1)` for `m ≤ M`. -/
theorem exists_realization_skelSubfunctor_step {m N : ℕ} (hm : m ≤ M)
    (S T : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)))
    (Q_m : SimplicialRealization D (skelSubfunctor S T m).toFunctor)
    {C' : Type u₃} [Category.{v₃} C'] [CategoryWithCofibrations C'] (G : C ⥤ C')
    (hG : IsCofibrationMorphism G) (hG_bd : PreservesBoundaryRealizations BData G) :
    ∃ Q_succ : SimplicialRealization D (skelSubfunctor S T (m + 1)).toFunctor,
      cofibrations C
        (SimplicialRealization.realizationMap Q_m Q_succ
          (Subfunctor.homOfLe
            (show skelSubfunctor S T m ≤ skelSubfunctor S T (m + 1) from
              fun _ _ hx => hx.imp id (fun ⟨hxT, hlt⟩ => ⟨hxT, Nat.lt_succ_of_lt hlt⟩)))) ∧
      (IsUniversalCocone (Q_m.cocone.mapFunctor G) →
        IsUniversalCocone (Q_succ.cocone.mapFunctor G)) := by
  classical
  let S_m := skelSubfunctor S T m
  let F : Finset (Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk N) :=
    Finset.univ.filter (fun σ => ULift.up σ ∈ T.obj (op (Henry.SemiSimplexCategory.mk m)))
  have hF_bd : ∀ σ ∈ F, ∀ ⦃Δ : Henry.SemiSimplexCategoryᵒᵖ⦄
      (g : unop Δ ⟶ Henry.SemiSimplexCategory.mk m),
      (unop Δ).obj.len < m → ULift.up (g ≫ σ) ∈ S_m.obj Δ := by
    intro σ hσ Δ g hlt
    have hσT : ULift.up σ ∈ T.obj (op (Henry.SemiSimplexCategory.mk m)) :=
      (Finset.mem_filter.mp hσ).2
    exact Or.inr ⟨T.map g.op hσT, hlt⟩
  obtain ⟨Q_add, hc_add, hG_add⟩ :=
    exists_realization_addCellsAt BData hm S_m F hF_bd Q_m G hG hG_bd
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
  let e_skel := subfunctorIsoOfLe hle₁ hle₂
  let Q_succ := Q_add.ofIso e_skel.symm
  refine ⟨Q_succ, ?_, ?_⟩
  · have heq : SimplicialRealization.realizationMap Q_m Q_succ
        (Subfunctor.homOfLe
          (show skelSubfunctor S T m ≤ skelSubfunctor S T (m + 1) from
            fun _ _ hx => hx.imp id (fun ⟨hxT, hlt⟩ => ⟨hxT, Nat.lt_succ_of_lt hlt⟩))) =
        SimplicialRealization.realizationMap Q_m Q_add
          (Subfunctor.homOfLe
            (le_addCellsAt_empty m S_m |>.trans (addCellsAt_mono m S_m (Finset.empty_subset F)))) ≫
          SimplicialRealization.realizationMap Q_add Q_succ (Subfunctor.homOfLe hle₁) := by
      rw [← SimplicialRealization.realizationMap_comp]
      rfl
    rw [heq]
    have : IsIso (SimplicialRealization.realizationMap Q_add Q_succ (Subfunctor.homOfLe hle₁)) :=
      isIso_realizationMap_of_le_antisymm hle₁ hle₂ Q_add Q_succ
    exact cofibrations_comp _ _ hc_add (cofibrations_of_isIso _)
  · intro hGm
    exact isUniversalCocone_precomp_iso (hG_add hGm) e_skel.symm

/-- Skeletal induction up to `d ≤ M + 1` for `skelSubfunctor S T d`. -/
theorem exists_realization_skelSubfunctor {N : ℕ}
    (S T : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)))
    (Q_0 : SimplicialRealization D (skelSubfunctor S T 0).toFunctor)
    {C' : Type u₃} [Category.{v₃} C'] [CategoryWithCofibrations C'] (G : C ⥤ C')
    (hG : IsCofibrationMorphism G) (hG_bd : PreservesBoundaryRealizations BData G) :
    ∀ (d : ℕ), d ≤ M + 1 →
      ∃ Q_d : SimplicialRealization D (skelSubfunctor S T d).toFunctor,
        cofibrations C
          (SimplicialRealization.realizationMap Q_0 Q_d
            (Subfunctor.homOfLe
              (show skelSubfunctor S T 0 ≤ skelSubfunctor S T d from
                fun _ _ hx => hx.imp id (fun ⟨_, hlt⟩ => (Nat.not_lt_zero _ hlt).elim)))) ∧
        (IsUniversalCocone (Q_0.cocone.mapFunctor G) →
          IsUniversalCocone (Q_d.cocone.mapFunctor G)) := by
  intro d
  induction d with
  | zero =>
    intro _
    refine ⟨Q_0, ?_, id⟩
    have heq : Subfunctor.homOfLe
        (show skelSubfunctor S T 0 ≤ skelSubfunctor S T 0 from
          fun _ _ hx => hx.imp id (fun ⟨_, hlt⟩ => (Nat.not_lt_zero _ hlt).elim)) =
        𝟙 (skelSubfunctor S T 0).toFunctor := rfl
    rw [heq, SimplicialRealization.realizationMap_id]
    exact cofibrations_id Q_0.pt
  | succ d ih =>
    intro hd_succ
    have hdM : d ≤ M := Nat.le_of_succ_le_succ hd_succ
    obtain ⟨Q_d, hc_d, hG_d⟩ := ih (Nat.le_of_succ_le hd_succ)
    obtain ⟨Q_succ, hc_step, hG_step⟩ :=
      exists_realization_skelSubfunctor_step BData hdM S T Q_d G hG hG_bd
    refine ⟨Q_succ, ?_, fun hG0 => hG_step (hG_d hG0)⟩
    have heq : SimplicialRealization.realizationMap Q_0 Q_succ
        (Subfunctor.homOfLe
          (show skelSubfunctor S T 0 ≤ skelSubfunctor S T (d + 1) from
            fun _ _ hx => hx.imp id (fun ⟨_, hlt⟩ => (Nat.not_lt_zero _ hlt).elim))) =
        SimplicialRealization.realizationMap Q_0 Q_d
          (Subfunctor.homOfLe
            (show skelSubfunctor S T 0 ≤ skelSubfunctor S T d from
              fun _ _ hx => hx.imp id (fun ⟨_, hlt⟩ => (Nat.not_lt_zero _ hlt).elim))) ≫
          SimplicialRealization.realizationMap Q_d Q_succ
            (Subfunctor.homOfLe
              (show skelSubfunctor S T d ≤ skelSubfunctor S T (d + 1) from
                fun _ _ hx => hx.imp id (fun ⟨hxT, hlt⟩ => ⟨hxT, Nat.lt_succ_of_lt hlt⟩))) := by
      rw [← SimplicialRealization.realizationMap_comp]
      rfl
    rw [heq]
    exact cofibrations_comp _ _ hc_d hc_step

/-- For any `S ≤ T : Subfunctor Δ_N` with `HasDimLe M T.toFunctor` and any realization `Q_S` of `S`,
there exists a realization `Q_T` of `T` such that `Q_S.pt ⟶ Q_T.pt` is a cofibration in `C` and
any cofibration morphism `G` preserving boundary realizations and `Q_S` also preserves `Q_T`. -/
theorem exists_realization_of_le {N : ℕ}
    {S T : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N))}
    (hST : S ≤ T) (hT : HasDimLe M T.toFunctor)
    (Q_S : SimplicialRealization D S.toFunctor)
    {C' : Type u₃} [Category.{v₃} C'] [CategoryWithCofibrations C'] (G : C ⥤ C')
    (hG : IsCofibrationMorphism G) (hG_bd : PreservesBoundaryRealizations BData G) :
    ∃ Q_T : SimplicialRealization D T.toFunctor,
      cofibrations C (SimplicialRealization.realizationMap Q_S Q_T (Subfunctor.homOfLe hST)) ∧
      (IsUniversalCocone (Q_S.cocone.mapFunctor G) →
        IsUniversalCocone (Q_T.cocone.mapFunctor G)) := by
  have hle_zero₁ : S ≤ skelSubfunctor S T 0 := fun _ _ hx => Or.inl hx
  have hle_zero₂ : skelSubfunctor S T 0 ≤ S := by
    intro Δ x hx
    rcases hx with hxS | ⟨_, hlt⟩
    · exact hxS
    · exact (Nat.not_lt_zero _ hlt).elim
  have hle_top₁ : skelSubfunctor S T (M + 1) ≤ T := by
    intro Δ x hx
    rcases hx with hxS | ⟨hxT, _⟩
    · exact hST Δ hxS
    · exact hxT
  have hle_top₂ : T ≤ skelSubfunctor S T (M + 1) := by
    intro Δ x hxT
    exact Or.inr ⟨hxT, Nat.lt_succ_of_le (hT ⟨x, hxT⟩)⟩
  let e_zero := subfunctorIsoOfLe hle_zero₁ hle_zero₂
  let Q_0 := Q_S.ofIso e_zero.symm
  obtain ⟨Q_top, hc_top, hG_top⟩ :=
    exists_realization_skelSubfunctor BData S T Q_0 G hG hG_bd (M + 1) (le_refl (M + 1))
  let e_top := subfunctorIsoOfLe hle_top₁ hle_top₂
  let Q_T := Q_top.ofIso e_top.symm
  refine ⟨Q_T, ?_, ?_⟩
  · have heq : SimplicialRealization.realizationMap Q_S Q_T (Subfunctor.homOfLe hST) =
        SimplicialRealization.realizationMap Q_S Q_0 (Subfunctor.homOfLe hle_zero₁) ≫
          SimplicialRealization.realizationMap Q_0 Q_top
            (Subfunctor.homOfLe
              (show skelSubfunctor S T 0 ≤ skelSubfunctor S T (M + 1) from
                fun _ _ hx => hx.imp id (fun ⟨_, hlt⟩ => (Nat.not_lt_zero _ hlt).elim))) ≫
          SimplicialRealization.realizationMap Q_top Q_T (Subfunctor.homOfLe hle_top₁) := by
      rw [← SimplicialRealization.realizationMap_comp,
        ← SimplicialRealization.realizationMap_comp]
      rfl
    rw [heq]
    have : IsIso (SimplicialRealization.realizationMap Q_S Q_0 (Subfunctor.homOfLe hle_zero₁)) :=
      isIso_realizationMap_of_le_antisymm hle_zero₁ hle_zero₂ Q_S Q_0
    have : IsIso (SimplicialRealization.realizationMap Q_top Q_T (Subfunctor.homOfLe hle_top₁)) :=
      isIso_realizationMap_of_le_antisymm hle_top₁ hle_top₂ Q_top Q_T
    exact cofibrations_comp _ _ (cofibrations_of_isIso _)
      (cofibrations_comp _ _ hc_top (cofibrations_of_isIso _))
  · intro hGS
    exact isUniversalCocone_precomp_iso
      (hG_top (isUniversalCocone_precomp_iso hGS e_zero.symm)) e_top.symm

omit [IsCofibrationCategory C] in
lemma isCofibrationMorphism_id : IsCofibrationMorphism (𝟭 C) where
  map_cofibration := by intro X Y f hf; exact hf
  map_initial := by intro I hI; exact ⟨hI⟩
  map_isPushout := by intro A B X P i f k j sq _; exact sq

omit [IsCofibrationCategory C] in
lemma preservesBoundaryRealizations_id : PreservesBoundaryRealizations BData (𝟭 C) := by
  intro m hm
  have heq : ((BData.bdRealization m hm).cocone).mapFunctor (𝟭 C) =
      (BData.bdRealization m hm).cocone := rfl
  rw [heq]
  exact (BData.bdRealization m hm).isUniversal

include BData in
/-- Every subfunctor `T : Subfunctor Δ_N` with `HasDimLe M T.toFunctor` admits a realization along `D`. -/
theorem exists_subfunctorRealization {N : ℕ}
    (T : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)))
    (hT : HasDimLe M T.toFunctor) :
    Nonempty (SimplicialRealization D T.toFunctor) := by
  obtain ⟨I, ⟨hI⟩⟩ := IsCofibrationCategory.exists_initial (C := C)
  let Q_bot := botRealization D
    (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)) hI
  obtain ⟨Q_T, _, _⟩ := exists_realization_of_le BData (bot_le : ⊥ ≤ T) hT Q_bot
    (𝟭 C) isCofibrationMorphism_id (preservesBoundaryRealizations_id BData)
  exact ⟨Q_T⟩

include BData in
/-- Chosen realization of `T : Subfunctor Δ_N` (with `HasDimLe M T.toFunctor`) along `D`. -/
noncomputable def subfunctorRealization {N : ℕ}
    (T : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)))
    (hT : HasDimLe M T.toFunctor) :
    SimplicialRealization D T.toFunctor :=
  (exists_subfunctorRealization BData T hT).some

include BData in
/-- For any `S ≤ T : Subfunctor Δ_N` with `HasDimLe M T.toFunctor` and any realizations `Q_S` of `S`
and `Q_T` of `T`, the induced map `Q_S.pt ⟶ Q_T.pt` is a cofibration in `C`. -/
theorem cofibration_realizationMap_of_le {N : ℕ}
    {S T : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N))}
    (hST : S ≤ T) (hT : HasDimLe M T.toFunctor)
    (Q_S : SimplicialRealization D S.toFunctor)
    (Q_T : SimplicialRealization D T.toFunctor) :
    cofibrations C (SimplicialRealization.realizationMap Q_S Q_T (Subfunctor.homOfLe hST)) := by
  obtain ⟨Q_T', hc, _⟩ := exists_realization_of_le BData hST hT Q_S
    (𝟭 C) isCofibrationMorphism_id (preservesBoundaryRealizations_id BData)
  exact cofibration_realizationMap_of_realizations Q_S Q_S Q_T' Q_T _ hc

include BData in
/-- For any `m ≤ M`, any `S : Subfunctor Δ_m`, and any realization `Q_S` of `S`, the induced map
`Q_S.pt ⟶ D.obj m hm` is a cofibration in `C`. -/
theorem cofibration_realizationMap_iota {m : ℕ} (hm : m ≤ M)
    (S : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m)))
    (Q_S : SimplicialRealization D S.toFunctor) :
    cofibrations C
      (SimplicialRealization.realizationMap Q_S (stdSimplexRealization D m hm) S.ι) := by
  let B := SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m)
  let Q_top : SimplicialRealization D (⊤ : Subfunctor B).toFunctor :=
    (stdSimplexRealization D m hm).ofIso (topSubfunctorIso B)
  have hc_top : cofibrations C
      (SimplicialRealization.realizationMap Q_S Q_top (Subfunctor.homOfLe (le_top : S ≤ ⊤))) :=
    cofibration_realizationMap_of_le BData (le_top : S ≤ ⊤)
      (hasDimLe_subfunctor_stdSimplex hm ⊤) Q_S Q_top
  have heq : SimplicialRealization.realizationMap Q_S Q_top (Subfunctor.homOfLe (le_top : S ≤ ⊤)) =
      SimplicialRealization.realizationMap Q_S (stdSimplexRealization D m hm) S.ι := by
    unfold Q_top
    rw [SimplicialRealization.realizationMap_ofIso_right]
    rfl
  rw [← heq]
  exact hc_top

/-- Any cofibration morphism `G : C ⥤ C'` that preserves the boundary realizations of `BData`
preserves the realization of every subfunctor `T : Subfunctor Δ_N` with `HasDimLe M T.toFunctor`. -/
theorem isUniversalCocone_mapFunctor_of_subfunctor
    {C' : Type u₃} [Category.{v₃} C'] [CategoryWithCofibrations C'] (G : C ⥤ C')
    (hG : IsCofibrationMorphism G) (hG_bd : PreservesBoundaryRealizations BData G)
    {N : ℕ} (T : Subfunctor (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)))
    (hT : HasDimLe M T.toFunctor) (Q_T : SimplicialRealization D T.toFunctor) :
    IsUniversalCocone (Q_T.cocone.mapFunctor G) := by
  obtain ⟨I, ⟨hI⟩⟩ := IsCofibrationCategory.exists_initial (C := C)
  let B := SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk N)
  let Q_bot := botRealization D B hI
  have hG_bot : IsUniversalCocone (Q_bot.cocone.mapFunctor G) :=
    isUniversalCocone_mapFunctor_botCocone G D B (hG.map_initial hI).some
  obtain ⟨Q_T', _, hG_T'⟩ :=
    exists_realization_of_le BData (bot_le : ⊥ ≤ T) hT Q_bot G hG hG_bd
  exact isUniversalCocone_mapFunctor_of_realization G Q_T' Q_T (hG_T' hG_bot)

end SkeletalRealization

/-!
## Horn inclusions are trivial cofibrations in a cylinder category
-/

section HornWeakEquivalence

variable {C : Type u₂} [Category.{v₂} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [IsCylinderCategory C]
  {M : ℕ} {D : CosimplicialUpTo C M} (BData : CosimplicialBoundaryData.{v₂, u₂, u} D)

omit [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [IsCylinderCategory C] in
/-- For `k : Fin (N + 1)` and `hN : N ≤ M`, the inclusion of the vertex subfunctor
`simplexSubfunctor (vertexSimplex k)` into `Δ_N` realizes to `D.map (Nat.zero_le N) hN (vertexSimplex k)`. -/
lemma realizationMap_vertexSimplex {N : ℕ} (hN : N ≤ M) (k : Fin (N + 1)) :
    SimplicialRealization.realizationMap
      (simplexSubfunctorRealization D (Nat.zero_le M) (vertexSimplex k))
      (stdSimplexRealization D N hN)
      (simplexSubfunctor.{u} (vertexSimplex k)).ι =
    D.map (Nat.zero_le N) hN (vertexSimplex k) := by
  unfold simplexSubfunctorRealization
  rw [SimplicialRealization.realizationMap_ofIso_left]
  unfold SimplicialRealization.realizationMap
  rw [stdSimplexRealization_desc]
  change D.map (Nat.zero_le N) hN (𝟙 (Henry.SemiSimplexCategory.mk 0) ≫ vertexSimplex k) =
    D.map (Nat.zero_le N) hN (vertexSimplex k)
  rw [Category.id_comp]

include BData in
/-- In any cylinder category `C`, if all morphisms `D.map hk hm g` of `D : CosimplicialUpTo C M`
are weak equivalences and `D` has `CosimplicialBoundaryData`, then for every `n + 1 ≤ M`,
`k : Fin (n + 2)`, and any realization `Q_horn` of `Λ^{n+1}_k`, the horn inclusion
`Q_horn.pt ⟶ D.obj (n + 1)` is a weak equivalence in `C`. -/
theorem weakEquivalence_horn_realizationMap
    (hD_weq : ∀ {k m : ℕ} (hk : k ≤ m) (hm : m ≤ M)
      (g : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk m),
      weakEquivalences C (D.map hk hm g)) :
    ∀ (n : ℕ) (hn : n + 1 ≤ M) (k : Fin (n + 2))
      (Q_horn : SimplicialRealization D (SemiSSet.horn.{u} (n + 1) k).toFunctor),
      weakEquivalences C
        (SimplicialRealization.realizationMap Q_horn
          (stdSimplexRealization D (n + 1) hn) (SemiSSet.horn.{u} (n + 1) k).ι) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn k Q_horn
    have h_add : ∀ {d : ℕ} (hd : d < n)
        (F : Finset (Henry.SemiSimplexCategory.mk (d + 1) ⟶ Henry.SemiSimplexCategory.mk (n + 1))),
        F ⊆ hornCellsAt n k d →
        ∀ (Q_base : SimplicialRealization D (hornSkelSubfunctor.{u} n k d).toFunctor)
          (Q_F : SimplicialRealization D
            (addCellsAt (d + 1) (hornSkelSubfunctor.{u} n k d) F).toFunctor),
          weakEquivalences C
            (SimplicialRealization.realizationMap Q_base Q_F
              (Subfunctor.homOfLe
                (le_addCellsAt_empty (d + 1) (hornSkelSubfunctor.{u} n k d) |>.trans
                  (addCellsAt_mono (d + 1) (hornSkelSubfunctor.{u} n k d)
                    (Finset.empty_subset F))))) := by
      classical
      intro d hd F
      induction F using Finset.induction_on with
      | empty =>
        intro _ Q_base Q_empty
        have : IsIso (SimplicialRealization.realizationMap Q_base Q_empty
            (Subfunctor.homOfLe (le_addCellsAt_empty (d + 1) (hornSkelSubfunctor.{u} n k d)))) :=
          isIso_realizationMap_of_le_antisymm
            (le_addCellsAt_empty (d + 1) (hornSkelSubfunctor.{u} n k d))
            (addCellsAt_empty_le (d + 1) (hornSkelSubfunctor.{u} n k d))
            Q_base Q_empty
        exact weakEquivalences_of_isIso _
      | @insert σ F hσ_not_mem ihF =>
        intro hF_ins Q_base Q_ins
        have hF_sub : F ⊆ hornCellsAt n k d :=
          (Finset.subset_insert σ F).trans hF_ins
        have hσ_horn : σ ∈ hornCellsAt n k d :=
          hF_ins (Finset.mem_insert_self σ F)
        obtain ⟨j_k, hj_k⟩ := (mem_hornCellsAt_iff σ).mp hσ_horn
        have hd_le_M : d + 1 ≤ M := by omega
        have hdim_F : HasDimLe M
            (addCellsAt (d + 1) (hornSkelSubfunctor.{u} n k d) F).toFunctor :=
          hasDimLe_addCellsAt hd_le_M
            (hasDimLe_hornSkelSubfunctor n k (by omega)) F
        let Q_F := subfunctorRealization BData
          (addCellsAt (d + 1) (hornSkelSubfunctor.{u} n k d) F) hdim_F
        have hw_F := ihF hF_sub Q_base Q_F
        let K := SemiSSet.horn.{u} (d + 1) j_k
        have hdim_K : HasDimLe M K.toFunctor :=
          hasDimLe_subfunctor_stdSimplex hd_le_M K
        let Q_K := subfunctorRealization BData K hdim_K
        have hi_K : cofibrations C
            (SimplicialRealization.realizationMap Q_K (stdSimplexRealization D (d + 1) hd_le_M) K.ι) :=
          cofibration_realizationMap_iota BData hd_le_M K Q_K
        have hw_K : weakEquivalences C
            (SimplicialRealization.realizationMap Q_K (stdSimplexRealization D (d + 1) hd_le_M) K.ι) :=
          ih d hd hd_le_M j_k Q_K
        have hK_iff : ∀ ⦃Δ : Henry.SemiSimplexCategoryᵒᵖ⦄
            (y : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk (d + 1))).obj Δ),
            ULift.up (ULift.down y ≫ σ) ∈
              (addCellsAt (d + 1) (hornSkelSubfunctor.{u} n k d) F).obj Δ ↔
              y ∈ K.obj Δ :=
          fun _ y =>
            mem_addCellsAt_hornSkelSubfunctor_iff_mem_horn F hF_sub σ hσ_not_mem j_k hj_k y
        let e_ins := subfunctorIsoOfLe
          (sup_le_addCellsAt_insert (d + 1) (hornSkelSubfunctor.{u} n k d) F σ)
          (addCellsAt_insert_le_sup (d + 1) (hornSkelSubfunctor.{u} n k d) F σ)
        let Q_sup := Q_ins.ofIso e_ins
        have hw_sup : weakEquivalences C
            (SimplicialRealization.realizationMap Q_F Q_sup (Subfunctor.homOfLe le_sup_left)) :=
          weakEquivalence_of_attachSimplexRealization hd_le_M
            (addCellsAt (d + 1) (hornSkelSubfunctor.{u} n k d) F) σ K hK_iff
            Q_K Q_F Q_sup hi_K hw_K
        have heq : SimplicialRealization.realizationMap Q_base Q_ins
            (Subfunctor.homOfLe
              (le_addCellsAt_empty (d + 1) (hornSkelSubfunctor.{u} n k d) |>.trans
                (addCellsAt_mono (d + 1) (hornSkelSubfunctor.{u} n k d)
                  (Finset.empty_subset (insert σ F))))) =
            SimplicialRealization.realizationMap Q_base Q_F
              (Subfunctor.homOfLe
                (le_addCellsAt_empty (d + 1) (hornSkelSubfunctor.{u} n k d) |>.trans
                  (addCellsAt_mono (d + 1) (hornSkelSubfunctor.{u} n k d)
                    (Finset.empty_subset F)))) ≫
              SimplicialRealization.realizationMap Q_F Q_sup (Subfunctor.homOfLe le_sup_left) ≫
              SimplicialRealization.realizationMap Q_sup Q_ins
                (Subfunctor.homOfLe
                  (sup_le_addCellsAt_insert (d + 1) (hornSkelSubfunctor.{u} n k d) F σ)) := by
          rw [← SimplicialRealization.realizationMap_comp,
            ← SimplicialRealization.realizationMap_comp]
          rfl
        rw [heq]
        have : IsIso (SimplicialRealization.realizationMap Q_sup Q_ins
            (Subfunctor.homOfLe
              (sup_le_addCellsAt_insert (d + 1) (hornSkelSubfunctor.{u} n k d) F σ))) :=
          isIso_realizationMap_of_le_antisymm
            (sup_le_addCellsAt_insert (d + 1) (hornSkelSubfunctor.{u} n k d) F σ)
            (addCellsAt_insert_le_sup (d + 1) (hornSkelSubfunctor.{u} n k d) F σ) Q_sup Q_ins
        exact weakEquivalences_comp _ _ hw_F
          (weakEquivalences_comp _ _ hw_sup (weakEquivalences_of_isIso _))
    have h_skel : ∀ (d : ℕ) (hd : d ≤ n)
        (Q_0 : SimplicialRealization D (hornSkelSubfunctor.{u} n k 0).toFunctor)
        (Q_d : SimplicialRealization D (hornSkelSubfunctor.{u} n k d).toFunctor),
        weakEquivalences C
          (SimplicialRealization.realizationMap Q_0 Q_d
            (Subfunctor.homOfLe
              (show hornSkelSubfunctor.{u} n k 0 ≤ hornSkelSubfunctor.{u} n k d from
                fun _ _ ⟨m, hm0, σ, hkσ, hxσ⟩ => ⟨m, hm0.trans (Nat.zero_le _), σ, hkσ, hxσ⟩))) := by
      intro d
      induction d with
      | zero =>
        intro _ Q_0 Q_0'
        have : IsIso (SimplicialRealization.realizationMap Q_0 Q_0'
            (Subfunctor.homOfLe (le_refl (hornSkelSubfunctor.{u} n k 0)))) :=
          isIso_realizationMap_of_le_antisymm (le_refl _) (le_refl _) Q_0 Q_0'
        exact weakEquivalences_of_isIso _
      | succ d ih_d =>
        intro hd_succ Q_0 Q_succ
        have hd_lt : d < n := hd_succ
        let Q_d := subfunctorRealization BData (hornSkelSubfunctor.{u} n k d)
          (hasDimLe_hornSkelSubfunctor n k (by omega))
        have hw_d := ih_d (Nat.le_of_lt hd_lt) Q_0 Q_d
        let e_succ := subfunctorIsoOfLe
          (addCellsAt_le_hornSkelSubfunctor_succ n k d)
          (hornSkelSubfunctor_succ_le_addCellsAt n k d)
        let Q_add := Q_succ.ofIso e_succ
        have hw_step := h_add hd_lt (hornCellsAt n k d) (Finset.Subset.refl _) Q_d Q_add
        have heq : SimplicialRealization.realizationMap Q_0 Q_succ
            (Subfunctor.homOfLe
              (show hornSkelSubfunctor.{u} n k 0 ≤ hornSkelSubfunctor.{u} n k (d + 1) from
                fun _ _ ⟨m, hm0, σ, hkσ, hxσ⟩ => ⟨m, hm0.trans (Nat.zero_le _), σ, hkσ, hxσ⟩)) =
            SimplicialRealization.realizationMap Q_0 Q_d
              (Subfunctor.homOfLe
                (show hornSkelSubfunctor.{u} n k 0 ≤ hornSkelSubfunctor.{u} n k d from
                  fun _ _ ⟨m, hm0, σ, hkσ, hxσ⟩ =>
                    ⟨m, hm0.trans (Nat.zero_le _), σ, hkσ, hxσ⟩)) ≫
              SimplicialRealization.realizationMap Q_d Q_add
                (Subfunctor.homOfLe
                  (le_addCellsAt_empty (d + 1) (hornSkelSubfunctor.{u} n k d) |>.trans
                    (addCellsAt_mono (d + 1) (hornSkelSubfunctor.{u} n k d)
                      (Finset.empty_subset (hornCellsAt n k d))))) ≫
              SimplicialRealization.realizationMap Q_add Q_succ
                (Subfunctor.homOfLe (addCellsAt_le_hornSkelSubfunctor_succ n k d)) := by
          rw [← SimplicialRealization.realizationMap_comp,
            ← SimplicialRealization.realizationMap_comp]
          rfl
        rw [heq]
        have : IsIso (SimplicialRealization.realizationMap Q_add Q_succ
            (Subfunctor.homOfLe (addCellsAt_le_hornSkelSubfunctor_succ n k d))) :=
          isIso_realizationMap_of_le_antisymm
            (addCellsAt_le_hornSkelSubfunctor_succ n k d)
            (hornSkelSubfunctor_succ_le_addCellsAt n k d) Q_add Q_succ
        exact weakEquivalences_comp _ _ hw_d
          (weakEquivalences_comp _ _ hw_step (weakEquivalences_of_isIso _))
    let Q_vert := simplexSubfunctorRealization D (Nat.zero_le M) (vertexSimplex k)
    let e_zero := subfunctorIsoOfLe
      (le_hornSkelSubfunctor_zero n k) (hornSkelSubfunctor_zero_le n k)
    let Q_0 := Q_vert.ofIso e_zero.symm
    let e_n := subfunctorIsoOfLe
      (hornSkelSubfunctor_le_horn n k) (horn_le_hornSkelSubfunctor n k)
    let Q_n := Q_horn.ofIso e_n
    have hw_0_n := h_skel n (le_refl n) Q_0 Q_n
    have hle_0_horn : simplexSubfunctor.{u} (vertexSimplex k) ≤ SemiSSet.horn.{u} (n + 1) k :=
      (le_hornSkelSubfunctor_zero n k).trans
        ((show hornSkelSubfunctor.{u} n k 0 ≤ hornSkelSubfunctor.{u} n k n from
          fun _ _ ⟨m, hm0, σ, hkσ, hxσ⟩ => ⟨m, hm0.trans (Nat.zero_le _), σ, hkσ, hxσ⟩).trans
          (hornSkelSubfunctor_le_horn n k))
    have hw_vert_horn : weakEquivalences C
        (SimplicialRealization.realizationMap Q_vert Q_horn
          (Subfunctor.homOfLe hle_0_horn)) := by
      have heq : SimplicialRealization.realizationMap Q_vert Q_horn
          (Subfunctor.homOfLe hle_0_horn) =
          SimplicialRealization.realizationMap Q_vert Q_0
            (Subfunctor.homOfLe (le_hornSkelSubfunctor_zero n k)) ≫
            SimplicialRealization.realizationMap Q_0 Q_n
              (Subfunctor.homOfLe
                (show hornSkelSubfunctor.{u} n k 0 ≤ hornSkelSubfunctor.{u} n k n from
                  fun _ _ ⟨m, hm0, σ, hkσ, hxσ⟩ => ⟨m, hm0.trans (Nat.zero_le _), σ, hkσ, hxσ⟩)) ≫
            SimplicialRealization.realizationMap Q_n Q_horn
              (Subfunctor.homOfLe (hornSkelSubfunctor_le_horn n k)) := by
        rw [← SimplicialRealization.realizationMap_comp,
          ← SimplicialRealization.realizationMap_comp]
        rfl
      rw [heq]
      have : IsIso (SimplicialRealization.realizationMap Q_vert Q_0
          (Subfunctor.homOfLe (le_hornSkelSubfunctor_zero n k))) :=
        isIso_realizationMap_of_le_antisymm
          (le_hornSkelSubfunctor_zero n k) (hornSkelSubfunctor_zero_le n k) Q_vert Q_0
      have : IsIso (SimplicialRealization.realizationMap Q_n Q_horn
          (Subfunctor.homOfLe (hornSkelSubfunctor_le_horn n k))) :=
        isIso_realizationMap_of_le_antisymm
          (hornSkelSubfunctor_le_horn n k) (horn_le_hornSkelSubfunctor n k) Q_n Q_horn
      exact weakEquivalences_comp _ _ (weakEquivalences_of_isIso _)
        (weakEquivalences_comp _ _ hw_0_n (weakEquivalences_of_isIso _))
    have hw_vert_std : weakEquivalences C
        (SimplicialRealization.realizationMap Q_vert
          (stdSimplexRealization D (n + 1) hn) (simplexSubfunctor.{u} (vertexSimplex k)).ι) := by
      rw [realizationMap_vertexSimplex hn k]
      exact hD_weq (Nat.zero_le (n + 1)) hn (vertexSimplex k)
    have hcomp : SimplicialRealization.realizationMap Q_vert Q_horn
          (Subfunctor.homOfLe hle_0_horn) ≫
        SimplicialRealization.realizationMap Q_horn
          (stdSimplexRealization D (n + 1) hn) (SemiSSet.horn.{u} (n + 1) k).ι =
        SimplicialRealization.realizationMap Q_vert
          (stdSimplexRealization D (n + 1) hn) (simplexSubfunctor.{u} (vertexSimplex k)).ι := by
      rw [← SimplicialRealization.realizationMap_comp]
      rfl
    rw [← hcomp] at hw_vert_std
    exact weakEquivalences_of_comp_left _ _ hw_vert_horn hw_vert_std

end HornWeakEquivalence

end HomotopyHypothesis.Cylinder.SimplicialCategory
