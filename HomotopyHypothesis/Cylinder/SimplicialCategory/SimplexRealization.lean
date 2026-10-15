import HomotopyHypothesis.Cylinder.SimplicialCategory.HornFiltration
import HomotopyHypothesis.Cylinder.SimplicialCategory.SimplexContractions
import HomotopyHypothesis.Cylinder.SimplicialCategory.SimplexSubfunctors
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
/-!
# Realizations of semi-simplicial sets along truncated cosimplicial diagrams

This file develops the universal cocone / colimit realization of a semi-simplicial set `F` of
dimension at most `M` along a truncated cosimplicial diagram `D : CosimplicialUpTo C M` in any
category `C`. We prove:
1. Functoriality of realizations `realizationMap`, `realizationIso`, and invariance under
   truncation / diagram isomorphism `DiagramIsoOn`.
2. Base realizations for the empty subfunctor `⊥` (given an initial object of `C`), the standard
   simplex `Δ_m` (`m ≤ M`), and any `m`-simplex subfunctor `simplexSubfunctor σ`.
3. The pushout theorem for binary unions `S₁ ⊔ S₂` of subfunctors: a square from the realizations of
   `S₁ ⊓ S₂`, `S₁`, `S₂` to an object `P` is a pushout square in `C` if and only if the induced
   cocone on `S₁ ⊔ S₂` with apex `P` is universal.
4. Preservation of universal cocones under functors `G : C ⥤ C'` that preserve pushouts along the
   attaching cofibration.
-/

universe v₃ u₃ v₂ u₂ u

open CategoryTheory Limits HomotopicalAlgebra Opposite ConcreteCategory

namespace HomotopyHypothesis.Cylinder.SimplicialCategory

open HomotopyHypothesis.Henry

/-!
## Truncated cosimplicial diagrams up to dimension `M`
-/

/-- A truncated cosimplicial diagram of length `M` in a category `C`, assigning an object
`obj k hk` to each `k ≤ M` and a morphism `map hk hm g` to each semi-simplicial map
`g : [k] ⟶ [m]` for `k ≤ m ≤ M`. -/
structure CosimplicialUpTo (C : Type u₂) [Category.{v₂} C] (M : ℕ) where
  obj : ∀ (k : ℕ), k ≤ M → C
  map : ∀ {k m : ℕ} (hk : k ≤ m) (hm : m ≤ M),
    (Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk m) →
      (obj k (hk.trans hm) ⟶ obj m hm)
  map_id : ∀ (k : ℕ) (hk : k ≤ M),
    map (le_refl k) hk (𝟙 (Henry.SemiSimplexCategory.mk k)) = 𝟙 (obj k hk)
  map_comp : ∀ {j k m : ℕ} (hjk : j ≤ k) (hkm : k ≤ m) (hm : m ≤ M)
    (f : Henry.SemiSimplexCategory.mk j ⟶ Henry.SemiSimplexCategory.mk k)
    (g : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk m),
    map (hjk.trans hkm) hm (f ≫ g) = map hjk (hkm.trans hm) f ≫ map hkm hm g

/-- Image of a truncated cosimplicial diagram under a functor `G : C ⥤ C'`. -/
@[simps]
def CosimplicialUpTo.mapFunctor {C : Type u₂} [Category.{v₂} C]
    {C' : Type u₃} [Category.{v₃} C'] (G : C ⥤ C') {M : ℕ}
    (D : CosimplicialUpTo C M) : CosimplicialUpTo C' M where
  obj k hk := G.obj (D.obj k hk)
  map hk hm f := G.map (D.map hk hm f)
  map_id k hk := by rw [D.map_id, CategoryTheory.Functor.map_id]
  map_comp hjk hkm hm f g := by rw [D.map_comp, CategoryTheory.Functor.map_comp]

/-- Restriction of a truncated cosimplicial diagram from `M'` to `M ≤ M'`. -/
@[simps]
def CosimplicialUpTo.truncate {C : Type u₂} [Category.{v₂} C] {M M' : ℕ} (hMM' : M ≤ M')
    (D : CosimplicialUpTo C M') : CosimplicialUpTo C M where
  obj k hk := D.obj k (hk.trans hMM')
  map hk hm f := D.map hk (hm.trans hMM') f
  map_id k hk := D.map_id k (hk.trans hMM')
  map_comp hjk hkm hm f g := D.map_comp hjk hkm (hm.trans hMM') f g

/-- The standard truncated cosimplicial diagram `k ↦ stdSimplexCDelta k` in `CDelta`. -/
@[simps]
noncomputable def stdCosimplicialUpTo (M : ℕ) : CosimplicialUpTo CDelta.{u} M where
  obj k _ := stdSimplexCDelta.{u} k
  map _ _ f := stdSimplexCDeltaMap.{u} f
  map_id k _ := stdSimplexCDeltaMap_id.{u} k
  map_comp _ _ _ f g := stdSimplexCDeltaMap_comp.{u} f g

/-!
## Simplicial cocones and realizations
-/

/-- A cocone in `C` with apex `z` from a semi-simplicial set `F` along a truncated cosimplicial
diagram `D : CosimplicialUpTo C M`. -/
@[ext]
structure SimplicialCocone {C : Type u₂} [Category.{v₂} C] {M : ℕ}
    (D : CosimplicialUpTo C M) (F : SemiSSet.{u}) (z : C) where
  ι : ∀ (k : ℕ) (hk : k ≤ M),
    F.obj (op (Henry.SemiSimplexCategory.mk k)) → (D.obj k hk ⟶ z)
  w : ∀ {k m : ℕ} (hk : k ≤ m) (hm : m ≤ M)
    (g : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk m)
    (x : F.obj (op (Henry.SemiSimplexCategory.mk m))),
    D.map hk hm g ≫ ι m hm x = ι k (hk.trans hm) (F.map g.op x)

namespace SimplicialCocone

variable {C : Type u₂} [Category.{v₂} C] {M : ℕ} {D : CosimplicialUpTo C M}

/-- Postcomposition of a simplicial cocone with a morphism `h : z ⟶ z'`. -/
@[simps]
def postcomp {F : SemiSSet.{u}} {z z' : C} (c : SimplicialCocone D F z) (h : z ⟶ z') :
    SimplicialCocone D F z' where
  ι k hk x := c.ι k hk x ≫ h
  w hk hm g x := by rw [← Category.assoc, c.w]

/-- Precomposition of a simplicial cocone with a morphism of semi-simplicial sets `α : F₁ ⟶ F₂`. -/
@[simps]
def precomp {F₁ F₂ : SemiSSet.{u}} (α : F₁ ⟶ F₂) {z : C} (c : SimplicialCocone D F₂ z) :
    SimplicialCocone D F₁ z where
  ι k hk x := c.ι k hk (α.app (op (Henry.SemiSimplexCategory.mk k)) x)
  w hk hm g x := by
    rw [c.w]
    congr 1
    exact (ConcreteCategory.congr_hom (α.naturality g.op) x).symm

/-- Image of a simplicial cocone under a functor `G : C ⥤ C'`. -/
@[simps]
def mapFunctor {C' : Type u₃} [Category.{v₃} C'] (G : C ⥤ C')
    {F : SemiSSet.{u}} {z : C} (c : SimplicialCocone D F z) :
    SimplicialCocone (D.mapFunctor G) F (G.obj z) where
  ι k hk x := G.map (c.ι k hk x)
  w hk hm g x := by
    change G.map (D.map hk hm g) ≫ G.map (c.ι _ hm x) =
      G.map (c.ι _ (hk.trans hm) (F.map g.op x))
    rw [← CategoryTheory.Functor.map_comp, c.w]

end SimplicialCocone

/-- A simplicial cocone with apex `pt` is universal if every simplicial cocone with apex `z`
factors uniquely through `pt`. -/
def IsUniversalCocone {C : Type u₂} [Category.{v₂} C] {M : ℕ}
    {D : CosimplicialUpTo C M} {F : SemiSSet.{u}} {pt : C}
    (cocone : SimplicialCocone D F pt) : Prop :=
  ∀ ⦃z : C⦄ (c : SimplicialCocone D F z),
    ∃! m : pt ⟶ z, ∀ (k : ℕ) (hk : k ≤ M)
      (x : F.obj (op (Henry.SemiSimplexCategory.mk k))),
      cocone.ι k hk x ≫ m = c.ι k hk x

/-- A realization of a semi-simplicial set `F` along `D : CosimplicialUpTo C M`. -/
structure SimplicialRealization {C : Type u₂} [Category.{v₂} C] {M : ℕ}
    (D : CosimplicialUpTo C M) (F : SemiSSet.{u}) where
  pt : C
  cocone : SimplicialCocone D F pt
  desc : ∀ {z : C}, SimplicialCocone D F z → (pt ⟶ z)
  fac : ∀ {z : C} (c : SimplicialCocone D F z) (k : ℕ) (hk : k ≤ M)
    (x : F.obj (op (Henry.SemiSimplexCategory.mk k))),
    cocone.ι k hk x ≫ desc c = c.ι k hk x
  uniq : ∀ {z : C} (c : SimplicialCocone D F z) (m : pt ⟶ z),
    (∀ (k : ℕ) (hk : k ≤ M) (x : F.obj (op (Henry.SemiSimplexCategory.mk k))),
      cocone.ι k hk x ≫ m = c.ι k hk x) → m = desc c

/-- Every `SimplicialRealization` has a universal cocone. -/
lemma SimplicialRealization.isUniversal {C : Type u₂} [Category.{v₂} C] {M : ℕ}
    {D : CosimplicialUpTo C M} {F : SemiSSet.{u}} (Q : SimplicialRealization D F) :
    IsUniversalCocone Q.cocone :=
  fun _ c => ⟨Q.desc c, Q.fac c, Q.uniq c⟩

/-- Construct a `SimplicialRealization` from a universal cocone, with the same `pt` and `cocone`. -/
@[simps pt cocone]
noncomputable def IsUniversalCocone.toRealization {C : Type u₂} [Category.{v₂} C] {M : ℕ}
    {D : CosimplicialUpTo C M} {F : SemiSSet.{u}} {pt : C}
    {cocone : SimplicialCocone D F pt} (h : IsUniversalCocone cocone) :
    SimplicialRealization D F where
  pt := pt
  cocone := cocone
  desc c := (h c).choose
  fac c := (h c).choose_spec.1
  uniq c m hm := (h c).choose_spec.2 m hm

namespace SimplicialRealization

variable {C : Type u₂} [Category.{v₂} C] {M : ℕ} {D : CosimplicialUpTo C M}

lemma hom_ext {F : SemiSSet.{u}} (Q : SimplicialRealization D F) {z : C} {m₁ m₂ : Q.pt ⟶ z}
    (h : ∀ (k : ℕ) (hk : k ≤ M) (x : F.obj (op (Henry.SemiSimplexCategory.mk k))),
      Q.cocone.ι k hk x ≫ m₁ = Q.cocone.ι k hk x ≫ m₂) :
    m₁ = m₂ := by
  have h1 : m₁ = Q.desc (Q.cocone.postcomp m₂) := Q.uniq (Q.cocone.postcomp m₂) m₁ h
  have h2 : m₂ = Q.desc (Q.cocone.postcomp m₂) :=
    Q.uniq (Q.cocone.postcomp m₂) m₂ (fun _ _ _ => rfl)
  exact h1.trans h2.symm

/-- The morphism between realizations induced by a morphism of semi-simplicial sets `α : F₁ ⟶ F₂`. -/
def realizationMap {F₁ F₂ : SemiSSet.{u}}
    (Q₁ : SimplicialRealization D F₁) (Q₂ : SimplicialRealization D F₂) (α : F₁ ⟶ F₂) :
    Q₁.pt ⟶ Q₂.pt :=
  Q₁.desc (Q₂.cocone.precomp α)

@[simp, reassoc]
lemma ι_realizationMap {F₁ F₂ : SemiSSet.{u}}
    (Q₁ : SimplicialRealization D F₁) (Q₂ : SimplicialRealization D F₂) (α : F₁ ⟶ F₂)
    (k : ℕ) (hk : k ≤ M) (x : F₁.obj (op (Henry.SemiSimplexCategory.mk k))) :
    Q₁.cocone.ι k hk x ≫ realizationMap Q₁ Q₂ α =
      Q₂.cocone.ι k hk (α.app (op (Henry.SemiSimplexCategory.mk k)) x) :=
  Q₁.fac (Q₂.cocone.precomp α) k hk x

@[simp]
lemma realizationMap_id {F : SemiSSet.{u}} (Q : SimplicialRealization D F) :
    realizationMap Q Q (𝟙 F) = 𝟙 Q.pt := by
  apply Q.hom_ext
  intro k hk x
  rw [ι_realizationMap, Category.comp_id]
  rfl

@[simp, reassoc]
lemma realizationMap_comp {F₁ F₂ F₃ : SemiSSet.{u}}
    (Q₁ : SimplicialRealization D F₁) (Q₂ : SimplicialRealization D F₂)
    (Q₃ : SimplicialRealization D F₃) (α : F₁ ⟶ F₂) (β : F₂ ⟶ F₃) :
    realizationMap Q₁ Q₃ (α ≫ β) = realizationMap Q₁ Q₂ α ≫ realizationMap Q₂ Q₃ β := by
  apply Q₁.hom_ext
  intro k hk x
  rw [ι_realizationMap, ← Category.assoc, ι_realizationMap, ι_realizationMap]
  rfl

/-- Isomorphism between realizations induced by an isomorphism `F₁ ≅ F₂`. -/
@[simps]
def realizationIso {F₁ F₂ : SemiSSet.{u}}
    (Q₁ : SimplicialRealization D F₁) (Q₂ : SimplicialRealization D F₂) (e : F₁ ≅ F₂) :
    Q₁.pt ≅ Q₂.pt where
  hom := realizationMap Q₁ Q₂ e.hom
  inv := realizationMap Q₂ Q₁ e.inv
  hom_inv_id := by rw [← realizationMap_comp, e.hom_inv_id, realizationMap_id]
  inv_hom_id := by rw [← realizationMap_comp, e.inv_hom_id, realizationMap_id]

lemma iso_hom_inv_app_apply {F₁ F₂ : SemiSSet.{u}} (e : F₂ ≅ F₁)
    (Δ : Henry.SemiSimplexCategoryᵒᵖ) (x : F₂.obj Δ) :
    e.inv.app Δ (e.hom.app Δ x) = x :=
  ConcreteCategory.congr_hom (e.hom_inv_id_app Δ) x

lemma iso_inv_hom_app_apply {F₁ F₂ : SemiSSet.{u}} (e : F₂ ≅ F₁)
    (Δ : Henry.SemiSimplexCategoryᵒᵖ) (y : F₁.obj Δ) :
    e.hom.app Δ (e.inv.app Δ y) = y :=
  ConcreteCategory.congr_hom (e.inv_hom_id_app Δ) y

/-- Transport a realization along an isomorphism `e : F₂ ≅ F₁`. -/
@[simps]
def ofIso {F₁ F₂ : SemiSSet.{u}} (Q : SimplicialRealization D F₁) (e : F₂ ≅ F₁) :
    SimplicialRealization D F₂ where
  pt := Q.pt
  cocone := Q.cocone.precomp e.hom
  desc c := Q.desc (c.precomp e.inv)
  fac c k hk x := by
    change Q.cocone.ι k hk (e.hom.app _ x) ≫ Q.desc (c.precomp e.inv) = c.ι k hk x
    rw [Q.fac (c.precomp e.inv)]
    exact congrArg (c.ι k hk) (iso_hom_inv_app_apply e _ x)
  uniq c m hm := by
    apply Q.uniq (c.precomp e.inv) m
    intro k hk y
    have h_eq : Q.cocone.ι k hk (e.hom.app _ (e.inv.app _ y)) ≫ m =
        c.ι k hk (e.inv.app _ y) :=
      hm k hk (e.inv.app (op (Henry.SemiSimplexCategory.mk k)) y)
    rw [iso_inv_hom_app_apply e _ y] at h_eq
    exact h_eq

lemma realizationMap_ofIso_left {F₁ F₂ F₃ : SemiSSet.{u}}
    (Q : SimplicialRealization D F₁) (e : F₂ ≅ F₁)
    (Q₃ : SimplicialRealization D F₃) (α : F₂ ⟶ F₃) :
    realizationMap (Q.ofIso e) Q₃ α = realizationMap Q Q₃ (e.inv ≫ α) := by
  apply Q.hom_ext
  intro k hk y
  rw [ι_realizationMap]
  have h1 : Q.cocone.ι k hk (e.hom.app _ (e.inv.app _ y)) ≫
      realizationMap (Q.ofIso e) Q₃ α =
      Q₃.cocone.ι k hk (α.app _ (e.inv.app _ y)) :=
    ι_realizationMap (Q.ofIso e) Q₃ α k hk (e.inv.app (op (Henry.SemiSimplexCategory.mk k)) y)
  rw [iso_inv_hom_app_apply e _ y] at h1
  exact h1

lemma realizationMap_ofIso_right {F₁ F₂ F₃ : SemiSSet.{u}}
    (Q₁ : SimplicialRealization D F₁)
    (Q : SimplicialRealization D F₂) (e : F₃ ≅ F₂) (α : F₁ ⟶ F₃) :
    realizationMap Q₁ (Q.ofIso e) α = realizationMap Q₁ Q (α ≫ e.hom) := by
  apply Q₁.hom_ext
  intro k hk x
  exact (ι_realizationMap Q₁ (Q.ofIso e) α k hk x).trans
    (ι_realizationMap Q₁ Q (α ≫ e.hom) k hk x).symm

end SimplicialRealization

lemma isUniversalCocone_precomp_iso {C : Type u₂} [Category.{v₂} C] {M : ℕ}
    {D : CosimplicialUpTo C M} {F₁ F₂ : SemiSSet.{u}} {pt : C}
    {cocone : SimplicialCocone D F₁ pt} (h : IsUniversalCocone cocone) (e : F₂ ≅ F₁) :
    IsUniversalCocone (cocone.precomp e.hom) :=
  ((h.toRealization).ofIso e).isUniversal

/-!
## Invariance of realizations under diagram isomorphisms on `[0, M]`
-/

/-- An isomorphism on the first `M` levels between two truncated cosimplicial diagrams `D₁` and `D₂`
of lengths `M₁ ≥ M` and `M₂ ≥ M`. -/
structure DiagramIsoOn {C : Type u₂} [Category.{v₂} C] (M : ℕ) {M₁ M₂ : ℕ}
    (h₁ : M ≤ M₁) (h₂ : M ≤ M₂)
    (D₁ : CosimplicialUpTo C M₁) (D₂ : CosimplicialUpTo C M₂) where
  iso : ∀ (k : ℕ) (hk : k ≤ M), D₁.obj k (hk.trans h₁) ≅ D₂.obj k (hk.trans h₂)
  naturality : ∀ {k m : ℕ} (hk : k ≤ m) (hm : m ≤ M)
    (g : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk m),
    D₁.map hk (hm.trans h₁) g ≫ (iso m hm).hom =
      (iso k (hk.trans hm)).hom ≫ D₂.map hk (hm.trans h₂) g

namespace DiagramIsoOn

variable {C : Type u₂} [Category.{v₂} C] {M M₁ M₂ : ℕ} {h₁ : M ≤ M₁} {h₂ : M ≤ M₂}
  {D₁ : CosimplicialUpTo C M₁} {D₂ : CosimplicialUpTo C M₂}

/-- Symmetry of `DiagramIsoOn`. -/
@[simps]
def symm (Φ : DiagramIsoOn M h₁ h₂ D₁ D₂) : DiagramIsoOn M h₂ h₁ D₂ D₁ where
  iso k hk := (Φ.iso k hk).symm
  naturality hk hm g := by
    rw [Iso.symm_hom, Iso.symm_hom, Iso.comp_inv_eq, Category.assoc,
      Φ.naturality hk hm g, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Transport a cocone on `F` (with `HasDimLe M F`) along a `DiagramIsoOn`. -/
@[simps]
def coconeTo (Φ : DiagramIsoOn M h₁ h₂ D₁ D₂) {F : SemiSSet.{u}} (hF : HasDimLe M F)
    {z : C} (c₁ : SimplicialCocone D₁ F z) : SimplicialCocone D₂ F z where
  ι k _ x := (Φ.iso k (hF x)).inv ≫ c₁.ι k ((hF x).trans h₁) x
  w {k m} hk _ g x := by
    have hm : m ≤ M := hF x
    have hkM : k ≤ M := hk.trans hm
    have hnat : D₂.map hk (hm.trans h₂) g ≫ (Φ.iso m hm).inv =
        (Φ.iso k hkM).inv ≫ D₁.map hk (hm.trans h₁) g :=
      Φ.symm.naturality hk hm g
    calc D₂.map hk (hm.trans h₂) g ≫ ((Φ.iso m hm).inv ≫ c₁.ι m (hm.trans h₁) x)
      _ = (D₂.map hk (hm.trans h₂) g ≫ (Φ.iso m hm).inv) ≫ c₁.ι m (hm.trans h₁) x :=
          (Category.assoc _ _ _).symm
      _ = ((Φ.iso k hkM).inv ≫ D₁.map hk (hm.trans h₁) g) ≫ c₁.ι m (hm.trans h₁) x := by
          rw [hnat]
      _ = (Φ.iso k hkM).inv ≫ (D₁.map hk (hm.trans h₁) g ≫ c₁.ι m (hm.trans h₁) x) :=
          Category.assoc _ _ _
      _ = (Φ.iso k hkM).inv ≫ c₁.ι k (hkM.trans h₁) (F.map g.op x) := by
          rw [c₁.w hk (hm.trans h₁) g x]

end DiagramIsoOn

/-- Transport a realization of `F` (with `HasDimLe M F`) along a `DiagramIsoOn`. -/
@[simps]
def SimplicialRealization.changeDiagram {C : Type u₂} [Category.{v₂} C]
    {M M₁ M₂ : ℕ} {h₁ : M ≤ M₁} {h₂ : M ≤ M₂}
    {D₁ : CosimplicialUpTo C M₁} {D₂ : CosimplicialUpTo C M₂}
    (Φ : DiagramIsoOn M h₁ h₂ D₁ D₂) {F : SemiSSet.{u}} (hF : HasDimLe M F)
    (Q₁ : SimplicialRealization D₁ F) : SimplicialRealization D₂ F where
  pt := Q₁.pt
  cocone := Φ.coconeTo hF Q₁.cocone
  desc c₂ := Q₁.desc (Φ.symm.coconeTo hF c₂)
  fac c₂ k hk₂ x := by
    change ((Φ.iso k (hF x)).inv ≫ Q₁.cocone.ι k ((hF x).trans h₁) x) ≫
      Q₁.desc (Φ.symm.coconeTo hF c₂) = c₂.ι k hk₂ x
    rw [Category.assoc, Q₁.fac (Φ.symm.coconeTo hF c₂)]
    change (Φ.iso k (hF x)).inv ≫ ((Φ.iso k (hF x)).hom ≫ c₂.ι k ((hF x).trans h₂) x) =
      c₂.ι k hk₂ x
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  uniq c₂ m hm := by
    apply Q₁.uniq (Φ.symm.coconeTo hF c₂) m
    intro k hk₁ x
    have h_eq : ((Φ.iso k (hF x)).inv ≫ Q₁.cocone.ι k ((hF x).trans h₁) x) ≫ m =
        c₂.ι k ((hF x).trans h₂) x :=
      hm k ((hF x).trans h₂) x
    change Q₁.cocone.ι k hk₁ x ≫ m = (Φ.iso k (hF x)).hom ≫ c₂.ι k ((hF x).trans h₂) x
    rw [← h_eq, ← Category.assoc, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

lemma SimplicialRealization.realizationMap_changeDiagram {C : Type u₂} [Category.{v₂} C]
    {M M₁ M₂ : ℕ} {h₁ : M ≤ M₁} {h₂ : M ≤ M₂}
    {D₁ : CosimplicialUpTo C M₁} {D₂ : CosimplicialUpTo C M₂}
    (Φ : DiagramIsoOn M h₁ h₂ D₁ D₂) {F₁ F₂ : SemiSSet.{u}}
    (hF₁ : HasDimLe M F₁) (hF₂ : HasDimLe M F₂)
    (Q₁ : SimplicialRealization D₁ F₁) (Q₂ : SimplicialRealization D₁ F₂) (α : F₁ ⟶ F₂) :
    SimplicialRealization.realizationMap (Q₁.changeDiagram Φ hF₁) (Q₂.changeDiagram Φ hF₂) α =
      SimplicialRealization.realizationMap Q₁ Q₂ α := by
  apply Q₁.uniq (Q₂.cocone.precomp α)
    (Q₁.desc (Φ.symm.coconeTo hF₁ ((Q₂.changeDiagram Φ hF₂).cocone.precomp α)))
  intro k hk₁ x
  rw [Q₁.fac]
  change (Φ.iso k (hF₁ x)).hom ≫
      ((Φ.iso k (hF₁ x)).inv ≫
        Q₂.cocone.ι k hk₁ (α.app (op (Henry.SemiSimplexCategory.mk k)) x)) =
    Q₂.cocone.ι k hk₁ (α.app (op (Henry.SemiSimplexCategory.mk k)) x)
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-!
## Base realizations: empty subfunctor `⊥`, standard simplex `Δ_m`, and `simplexSubfunctor σ`
-/

/-- The empty cocone on `(⊥ : Subfunctor B).toFunctor` with apex `I`. -/
@[simps]
def botCocone {C : Type u₂} [Category.{v₂} C] {M : ℕ}
    (D : CosimplicialUpTo C M) (B : SemiSSet.{u}) (I : C) :
    SimplicialCocone D (⊥ : Subfunctor B).toFunctor I where
  ι _ _ x := x.2.elim
  w _ _ _ x := x.2.elim

lemma isUniversalCocone_botCocone {C : Type u₂} [Category.{v₂} C] {M : ℕ}
    (D : CosimplicialUpTo C M) (B : SemiSSet.{u}) {I : C} (hI : IsInitial I) :
    IsUniversalCocone (botCocone D B I) := by
  intro z c
  refine ⟨hI.to z, ?_, ?_⟩
  · intro _ _ x
    exact x.2.elim
  · intro m _
    exact hI.hom_ext m (hI.to z)

/-- Realization of `(⊥ : Subfunctor B).toFunctor` given an initial object `I : C`. -/
@[simps! pt cocone]
noncomputable def botRealization {C : Type u₂} [Category.{v₂} C] {M : ℕ}
    (D : CosimplicialUpTo C M) (B : SemiSSet.{u}) {I : C} (hI : IsInitial I) :
    SimplicialRealization D (⊥ : Subfunctor B).toFunctor :=
  (isUniversalCocone_botCocone D B hI).toRealization

lemma isUniversalCocone_mapFunctor_botCocone {C : Type u₂} [Category.{v₂} C]
    {C' : Type u₃} [Category.{v₃} C'] (G : C ⥤ C')
    {M : ℕ} (D : CosimplicialUpTo C M) (B : SemiSSet.{u}) {I : C}
    (hGI : IsInitial (G.obj I)) :
    IsUniversalCocone ((botCocone D B I).mapFunctor G) := by
  have heq : (botCocone D B I).mapFunctor G = botCocone (D.mapFunctor G) B (G.obj I) := by
    ext _ _ x
    exact x.2.elim
  rw [heq]
  exact isUniversalCocone_botCocone (D.mapFunctor G) B hGI

/-- The tautological cocone on `Δ_m` with apex `D.obj m hm`. -/
@[simps]
def stdSimplexCocone {C : Type u₂} [Category.{v₂} C] {M : ℕ}
    (D : CosimplicialUpTo C M) (m : ℕ) (hm : m ≤ M) :
    SimplicialCocone D (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m))
      (D.obj m hm) where
  ι _k _ x := D.map (len_le_of_hom (ULift.down x)) hm (ULift.down x)
  w hk _ g x := (D.map_comp hk (len_le_of_hom (ULift.down x)) hm g (ULift.down x)).symm

lemma isUniversalCocone_stdSimplexCocone {C : Type u₂} [Category.{v₂} C] {M : ℕ}
    (D : CosimplicialUpTo C M) (m : ℕ) (hm : m ≤ M) :
    IsUniversalCocone (stdSimplexCocone.{v₂, u₂, u} D m hm) := by
  intro z c
  refine ⟨c.ι m hm (ULift.up (𝟙 (Henry.SemiSimplexCategory.mk m))), ?_, ?_⟩
  · intro k hk x
    dsimp [stdSimplexCocone]
    rw [c.w (len_le_of_hom (ULift.down x)) hm (ULift.down x)
      (ULift.up (𝟙 (Henry.SemiSimplexCategory.mk m)))]
    congr 2
    change ULift.up (ULift.down x ≫ 𝟙 (Henry.SemiSimplexCategory.mk m)) = x
    rw [Category.comp_id]
  · intro f hf
    have h_id := hf m hm (ULift.up (𝟙 (Henry.SemiSimplexCategory.mk m)))
    dsimp [stdSimplexCocone] at h_id
    rw [D.map_id m hm, Category.id_comp] at h_id
    exact h_id

/-- Realization of `Δ_m` (`m ≤ M`) with apex `D.obj m hm`. -/
@[simps! pt cocone]
noncomputable def stdSimplexRealization {C : Type u₂} [Category.{v₂} C] {M : ℕ}
    (D : CosimplicialUpTo C M) (m : ℕ) (hm : m ≤ M) :
    SimplicialRealization D (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m)) :=
  (isUniversalCocone_stdSimplexCocone D m hm).toRealization

lemma stdSimplexRealization_desc {C : Type u₂} [Category.{v₂} C] {M : ℕ}
    (D : CosimplicialUpTo C M) (m : ℕ) (hm : m ≤ M) {z : C}
    (c : SimplicialCocone D (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk m)) z) :
    (stdSimplexRealization D m hm).desc c =
      c.ι m hm (ULift.up (𝟙 (Henry.SemiSimplexCategory.mk m))) := by
  symm
  apply (stdSimplexRealization D m hm).uniq
  intro k hk x
  change D.map (len_le_of_hom (ULift.down x)) hm (ULift.down x) ≫
      c.ι m hm (ULift.up (𝟙 (Henry.SemiSimplexCategory.mk m))) =
    c.ι k hk x
  rw [c.w (len_le_of_hom (ULift.down x)) hm (ULift.down x)
    (ULift.up (𝟙 (Henry.SemiSimplexCategory.mk m)))]
  congr 2
  change ULift.up (ULift.down x ≫ 𝟙 (Henry.SemiSimplexCategory.mk m)) = x
  rw [Category.comp_id]

lemma isUniversalCocone_mapFunctor_stdSimplexCocone {C : Type u₂} [Category.{v₂} C]
    {C' : Type u₃} [Category.{v₃} C'] (G : C ⥤ C')
    {M : ℕ} (D : CosimplicialUpTo C M) (m : ℕ) (hm : m ≤ M) :
    IsUniversalCocone ((stdSimplexCocone.{v₂, u₂, u} D m hm).mapFunctor G) :=
  isUniversalCocone_stdSimplexCocone (D.mapFunctor G) m hm

/-- Realization of `simplexSubfunctor σ` (`m ≤ M`) with apex `D.obj m hm`. -/
@[simps! pt cocone]
noncomputable def simplexSubfunctorRealization {C : Type u₂} [Category.{v₂} C] {M m N : ℕ}
    (D : CosimplicialUpTo C M) (hm : m ≤ M)
    (σ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk N) :
    SimplicialRealization D (simplexSubfunctor.{u} σ).toFunctor :=
  (stdSimplexRealization D m hm).ofIso (simplexSubfunctorIso.{u} σ).symm

lemma isUniversalCocone_mapFunctor_simplexSubfunctorRealization {C : Type u₂} [Category.{v₂} C]
    {C' : Type u₃} [Category.{v₃} C'] (G : C ⥤ C')
    {M m N : ℕ} (D : CosimplicialUpTo C M) (hm : m ≤ M)
    (σ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk N) :
    IsUniversalCocone ((simplexSubfunctorRealization.{v₂, u₂, u} D hm σ).cocone.mapFunctor G) :=
  isUniversalCocone_precomp_iso
    (isUniversalCocone_mapFunctor_stdSimplexCocone G D m hm)
    (simplexSubfunctorIso.{u} σ).symm

/-!
## Pushout theorem for binary unions `S₁ ⊔ S₂`
-/

section SupPushout

variable {C : Type u₂} [Category.{v₂} C] {M : ℕ} {D : CosimplicialUpTo C M}
  {B : SemiSSet.{u}} {S₁ S₂ : Subfunctor B}
  (Q₀ : SimplicialRealization D (S₁ ⊓ S₂).toFunctor)
  (Q₁ : SimplicialRealization D S₁.toFunctor)
  (Q₂ : SimplicialRealization D S₂.toFunctor)

/-- Given realizations `Q₀, Q₁, Q₂` of `S₁ ⊓ S₂, S₁, S₂` and a commutative square `j₁, j₂` into `P`,
the induced cocone on `S₁ ⊔ S₂` with apex `P`. -/
noncomputable def supCocone {P : C} (j₁ : Q₁.pt ⟶ P) (j₂ : Q₂.pt ⟶ P)
    (hw : SimplicialRealization.realizationMap Q₀ Q₁ (Subfunctor.homOfLe inf_le_left) ≫ j₁ =
      SimplicialRealization.realizationMap Q₀ Q₂ (Subfunctor.homOfLe inf_le_right) ≫ j₂) :
    SimplicialCocone D (S₁ ⊔ S₂).toFunctor P where
  ι k hk x := by
    classical
    exact if hx₁ : x.1 ∈ S₁.obj (op (Henry.SemiSimplexCategory.mk k)) then
      Q₁.cocone.ι k hk ⟨x.1, hx₁⟩ ≫ j₁
    else
      Q₂.cocone.ι k hk ⟨x.1, x.2.resolve_left hx₁⟩ ≫ j₂
  w {k m} hk hm g x := by
    classical
    have h_left : ∀ {l : ℕ} (hl : l ≤ M)
        (y : (S₁ ⊔ S₂).toFunctor.obj (op (Henry.SemiSimplexCategory.mk l)))
        (hy₁ : y.1 ∈ S₁.obj (op (Henry.SemiSimplexCategory.mk l))),
        (if h : y.1 ∈ S₁.obj (op (Henry.SemiSimplexCategory.mk l)) then
          Q₁.cocone.ι l hl ⟨y.1, h⟩ ≫ j₁
        else
          Q₂.cocone.ι l hl ⟨y.1, y.2.resolve_left h⟩ ≫ j₂) =
        Q₁.cocone.ι l hl ⟨y.1, hy₁⟩ ≫ j₁ := by
      intro l hl y hy₁
      simp [hy₁]
    have h_right : ∀ {l : ℕ} (hl : l ≤ M)
        (y : (S₁ ⊔ S₂).toFunctor.obj (op (Henry.SemiSimplexCategory.mk l)))
        (hy₂ : y.1 ∈ S₂.obj (op (Henry.SemiSimplexCategory.mk l))),
        (if h : y.1 ∈ S₁.obj (op (Henry.SemiSimplexCategory.mk l)) then
          Q₁.cocone.ι l hl ⟨y.1, h⟩ ≫ j₁
        else
          Q₂.cocone.ι l hl ⟨y.1, y.2.resolve_left h⟩ ≫ j₂) =
        Q₂.cocone.ι l hl ⟨y.1, hy₂⟩ ≫ j₂ := by
      intro l hl y hy₂
      by_cases hy₁ : y.1 ∈ S₁.obj (op (Henry.SemiSimplexCategory.mk l))
      · simp only [hy₁, ↓reduceDIte]
        let y₀ : (S₁ ⊓ S₂).toFunctor.obj (op (Henry.SemiSimplexCategory.mk l)) :=
          ⟨y.1, hy₁, hy₂⟩
        have h1 : Q₁.cocone.ι l hl ⟨y.1, hy₁⟩ =
            Q₀.cocone.ι l hl y₀ ≫
              SimplicialRealization.realizationMap Q₀ Q₁ (Subfunctor.homOfLe inf_le_left) :=
          (SimplicialRealization.ι_realizationMap Q₀ Q₁
            (Subfunctor.homOfLe inf_le_left) l hl y₀).symm
        have h2 : Q₂.cocone.ι l hl ⟨y.1, hy₂⟩ =
            Q₀.cocone.ι l hl y₀ ≫
              SimplicialRealization.realizationMap Q₀ Q₂ (Subfunctor.homOfLe inf_le_right) :=
          (SimplicialRealization.ι_realizationMap Q₀ Q₂
            (Subfunctor.homOfLe inf_le_right) l hl y₀).symm
        rw [h1, h2, Category.assoc, hw, ← Category.assoc]
      · simp [hy₁]
    rcases x.2 with hx₁ | hx₂
    · rw [h_left hm x hx₁,
        h_left (hk.trans hm) ((S₁ ⊔ S₂).toFunctor.map g.op x) (S₁.map g.op hx₁),
        ← Category.assoc, Q₁.cocone.w hk hm g ⟨x.1, hx₁⟩]
      rfl
    · rw [h_right hm x hx₂,
        h_right (hk.trans hm) ((S₁ ⊔ S₂).toFunctor.map g.op x) (S₂.map g.op hx₂),
        ← Category.assoc, Q₂.cocone.w hk hm g ⟨x.1, hx₂⟩]
      rfl

lemma supCocone_ι_of_mem_left {P : C} (j₁ : Q₁.pt ⟶ P) (j₂ : Q₂.pt ⟶ P)
    (hw : SimplicialRealization.realizationMap Q₀ Q₁ (Subfunctor.homOfLe inf_le_left) ≫ j₁ =
      SimplicialRealization.realizationMap Q₀ Q₂ (Subfunctor.homOfLe inf_le_right) ≫ j₂)
    (k : ℕ) (hk : k ≤ M)
    (x : (S₁ ⊔ S₂).toFunctor.obj (op (Henry.SemiSimplexCategory.mk k)))
    (hx₁ : x.1 ∈ S₁.obj (op (Henry.SemiSimplexCategory.mk k))) :
    (supCocone Q₀ Q₁ Q₂ j₁ j₂ hw).ι k hk x = Q₁.cocone.ι k hk ⟨x.1, hx₁⟩ ≫ j₁ := by
  dsimp [supCocone]
  simp [hx₁]

lemma supCocone_ι_of_mem_right {P : C} (j₁ : Q₁.pt ⟶ P) (j₂ : Q₂.pt ⟶ P)
    (hw : SimplicialRealization.realizationMap Q₀ Q₁ (Subfunctor.homOfLe inf_le_left) ≫ j₁ =
      SimplicialRealization.realizationMap Q₀ Q₂ (Subfunctor.homOfLe inf_le_right) ≫ j₂)
    (k : ℕ) (hk : k ≤ M)
    (x : (S₁ ⊔ S₂).toFunctor.obj (op (Henry.SemiSimplexCategory.mk k)))
    (hx₂ : x.1 ∈ S₂.obj (op (Henry.SemiSimplexCategory.mk k))) :
    (supCocone Q₀ Q₁ Q₂ j₁ j₂ hw).ι k hk x = Q₂.cocone.ι k hk ⟨x.1, hx₂⟩ ≫ j₂ := by
  dsimp [supCocone]
  by_cases hx₁ : x.1 ∈ S₁.obj (op (Henry.SemiSimplexCategory.mk k))
  · simp only [hx₁, ↓reduceDIte]
    let x₀ : (S₁ ⊓ S₂).toFunctor.obj (op (Henry.SemiSimplexCategory.mk k)) := ⟨x.1, hx₁, hx₂⟩
    have h1 : Q₁.cocone.ι k hk ⟨x.1, hx₁⟩ =
        Q₀.cocone.ι k hk x₀ ≫
          SimplicialRealization.realizationMap Q₀ Q₁ (Subfunctor.homOfLe inf_le_left) :=
      (SimplicialRealization.ι_realizationMap Q₀ Q₁
        (Subfunctor.homOfLe inf_le_left) k hk x₀).symm
    have h2 : Q₂.cocone.ι k hk ⟨x.1, hx₂⟩ =
        Q₀.cocone.ι k hk x₀ ≫
          SimplicialRealization.realizationMap Q₀ Q₂ (Subfunctor.homOfLe inf_le_right) :=
      (SimplicialRealization.ι_realizationMap Q₀ Q₂
        (Subfunctor.homOfLe inf_le_right) k hk x₀).symm
    rw [h1, h2, Category.assoc, hw, ← Category.assoc]
  · simp [hx₁]

@[simp]
lemma supCocone_ι_inl {P : C} (j₁ : Q₁.pt ⟶ P) (j₂ : Q₂.pt ⟶ P)
    (hw : SimplicialRealization.realizationMap Q₀ Q₁ (Subfunctor.homOfLe inf_le_left) ≫ j₁ =
      SimplicialRealization.realizationMap Q₀ Q₂ (Subfunctor.homOfLe inf_le_right) ≫ j₂)
    (k : ℕ) (hk : k ≤ M)
    (y : S₁.toFunctor.obj (op (Henry.SemiSimplexCategory.mk k))) :
    (supCocone Q₀ Q₁ Q₂ j₁ j₂ hw).ι k hk ⟨y.1, Or.inl y.2⟩ = Q₁.cocone.ι k hk y ≫ j₁ :=
  supCocone_ι_of_mem_left Q₀ Q₁ Q₂ j₁ j₂ hw k hk ⟨y.1, Or.inl y.2⟩ y.2

@[simp]
lemma supCocone_ι_inr {P : C} (j₁ : Q₁.pt ⟶ P) (j₂ : Q₂.pt ⟶ P)
    (hw : SimplicialRealization.realizationMap Q₀ Q₁ (Subfunctor.homOfLe inf_le_left) ≫ j₁ =
      SimplicialRealization.realizationMap Q₀ Q₂ (Subfunctor.homOfLe inf_le_right) ≫ j₂)
    (k : ℕ) (hk : k ≤ M)
    (y : S₂.toFunctor.obj (op (Henry.SemiSimplexCategory.mk k))) :
    (supCocone Q₀ Q₁ Q₂ j₁ j₂ hw).ι k hk ⟨y.1, Or.inr y.2⟩ = Q₂.cocone.ι k hk y ≫ j₂ :=
  supCocone_ι_of_mem_right Q₀ Q₁ Q₂ j₁ j₂ hw k hk ⟨y.1, Or.inr y.2⟩ y.2

/-- A commutative square from `Q₀, Q₁, Q₂` to `P` is a pushout square in `C` if and only if
`supCocone Q₀ Q₁ Q₂ j₁ j₂ hw` is a universal cocone on `S₁ ⊔ S₂`. -/
theorem isPushout_iff_isUniversalCocone_supCocone {P : C} (j₁ : Q₁.pt ⟶ P) (j₂ : Q₂.pt ⟶ P)
    (hw : SimplicialRealization.realizationMap Q₀ Q₁ (Subfunctor.homOfLe inf_le_left) ≫ j₁ =
      SimplicialRealization.realizationMap Q₀ Q₂ (Subfunctor.homOfLe inf_le_right) ≫ j₂) :
    IsPushout
      (SimplicialRealization.realizationMap Q₀ Q₁ (Subfunctor.homOfLe inf_le_left))
      (SimplicialRealization.realizationMap Q₀ Q₂ (Subfunctor.homOfLe inf_le_right))
      j₁ j₂ ↔
    IsUniversalCocone (supCocone Q₀ Q₁ Q₂ j₁ j₂ hw) := by
  let i₁ := SimplicialRealization.realizationMap Q₀ Q₁ (Subfunctor.homOfLe inf_le_left)
  let i₂ := SimplicialRealization.realizationMap Q₀ Q₂ (Subfunctor.homOfLe inf_le_right)
  constructor
  · intro sq z c
    let u₁ : Q₁.pt ⟶ z := Q₁.desc (c.precomp (Subfunctor.homOfLe le_sup_left))
    let u₂ : Q₂.pt ⟶ z := Q₂.desc (c.precomp (Subfunctor.homOfLe le_sup_right))
    have hu : i₁ ≫ u₁ = i₂ ≫ u₂ := by
      apply Q₀.hom_ext
      intro k hk x
      rw [← Category.assoc, SimplicialRealization.ι_realizationMap,
        ← Category.assoc, SimplicialRealization.ι_realizationMap]
      have h1 := Q₁.fac (c.precomp (Subfunctor.homOfLe le_sup_left)) k hk ⟨x.1, x.2.1⟩
      have h2 := Q₂.fac (c.precomp (Subfunctor.homOfLe le_sup_right)) k hk ⟨x.1, x.2.2⟩
      exact h1.trans h2.symm
    refine ⟨sq.desc u₁ u₂ hu, ?_, ?_⟩
    · intro k hk x
      rcases x.2 with hx₁ | hx₂
      · rw [supCocone_ι_of_mem_left Q₀ Q₁ Q₂ j₁ j₂ hw k hk x hx₁,
          Category.assoc, sq.inl_desc]
        exact Q₁.fac (c.precomp (Subfunctor.homOfLe le_sup_left)) k hk ⟨x.1, hx₁⟩
      · rw [supCocone_ι_of_mem_right Q₀ Q₁ Q₂ j₁ j₂ hw k hk x hx₂,
          Category.assoc, sq.inr_desc]
        exact Q₂.fac (c.precomp (Subfunctor.homOfLe le_sup_right)) k hk ⟨x.1, hx₂⟩
    · intro m hm
      apply sq.hom_ext
      · rw [sq.inl_desc]
        apply Q₁.uniq (c.precomp (Subfunctor.homOfLe le_sup_left)) (j₁ ≫ m)
        intro k hk y
        rw [← Category.assoc, ← supCocone_ι_inl Q₀ Q₁ Q₂ j₁ j₂ hw k hk y]
        exact hm k hk ⟨y.1, Or.inl y.2⟩
      · rw [sq.inr_desc]
        apply Q₂.uniq (c.precomp (Subfunctor.homOfLe le_sup_right)) (j₂ ≫ m)
        intro k hk y
        rw [← Category.assoc, ← supCocone_ι_inr Q₀ Q₁ Q₂ j₁ j₂ hw k hk y]
        exact hm k hk ⟨y.1, Or.inr y.2⟩
  · intro huniv
    apply IsPushout.of_isColimit (c := PushoutCocone.mk j₁ j₂ hw)
    apply PushoutCocone.isColimitAux'
    intro s
    let c_s := supCocone Q₀ Q₁ Q₂ s.inl s.inr s.condition
    let m : P ⟶ s.pt := (huniv c_s).choose
    have hm : ∀ (k : ℕ) (hk : k ≤ M)
        (x : (S₁ ⊔ S₂).toFunctor.obj (op (Henry.SemiSimplexCategory.mk k))),
        (supCocone Q₀ Q₁ Q₂ j₁ j₂ hw).ι k hk x ≫ m =
          (supCocone Q₀ Q₁ Q₂ s.inl s.inr s.condition).ι k hk x :=
      (huniv c_s).choose_spec.1
    have hm_uniq : ∀ (m' : P ⟶ s.pt),
        (∀ (k : ℕ) (hk : k ≤ M)
          (x : (S₁ ⊔ S₂).toFunctor.obj (op (Henry.SemiSimplexCategory.mk k))),
          (supCocone Q₀ Q₁ Q₂ j₁ j₂ hw).ι k hk x ≫ m' =
            (supCocone Q₀ Q₁ Q₂ s.inl s.inr s.condition).ι k hk x) → m' = m :=
      (huniv c_s).choose_spec.2
    have hm₁ : j₁ ≫ m = s.inl := by
      apply Q₁.hom_ext
      intro k hk y
      rw [← Category.assoc, ← supCocone_ι_inl Q₀ Q₁ Q₂ j₁ j₂ hw k hk y,
        hm k hk ⟨y.1, Or.inl y.2⟩,
        supCocone_ι_inl Q₀ Q₁ Q₂ s.inl s.inr s.condition k hk y]
    have hm₂ : j₂ ≫ m = s.inr := by
      apply Q₂.hom_ext
      intro k hk y
      rw [← Category.assoc, ← supCocone_ι_inr Q₀ Q₁ Q₂ j₁ j₂ hw k hk y,
        hm k hk ⟨y.1, Or.inr y.2⟩,
        supCocone_ι_inr Q₀ Q₁ Q₂ s.inl s.inr s.condition k hk y]
    refine ⟨m, hm₁, hm₂, ?_⟩
    intro (m' : P ⟶ s.pt) (hm'₁ : j₁ ≫ m' = s.inl) (hm'₂ : j₂ ≫ m' = s.inr)
    apply hm_uniq m'
    intro k hk x
    rcases x.2 with hx₁ | hx₂
    · rw [supCocone_ι_of_mem_left Q₀ Q₁ Q₂ j₁ j₂ hw k hk x hx₁, Category.assoc, hm'₁,
        supCocone_ι_of_mem_left Q₀ Q₁ Q₂ s.inl s.inr s.condition k hk x hx₁]
    · rw [supCocone_ι_of_mem_right Q₀ Q₁ Q₂ j₁ j₂ hw k hk x hx₂, Category.assoc, hm'₂,
        supCocone_ι_of_mem_right Q₀ Q₁ Q₂ s.inl s.inr s.condition k hk x hx₂]

/-- For any realizations `Q₀, Q₁, Q₂, Q₁₂` of `S₁ ⊓ S₂, S₁, S₂, S₁ ⊔ S₂`, the canonical square of
`realizationMap`s is a pushout square in `C`. -/
theorem isPushout_of_realizations (Q₁₂ : SimplicialRealization D (S₁ ⊔ S₂).toFunctor) :
    IsPushout
      (SimplicialRealization.realizationMap Q₀ Q₁ (Subfunctor.homOfLe inf_le_left))
      (SimplicialRealization.realizationMap Q₀ Q₂ (Subfunctor.homOfLe inf_le_right))
      (SimplicialRealization.realizationMap Q₁ Q₁₂ (Subfunctor.homOfLe le_sup_left))
      (SimplicialRealization.realizationMap Q₂ Q₁₂ (Subfunctor.homOfLe le_sup_right)) := by
  let j₁ := SimplicialRealization.realizationMap Q₁ Q₁₂ (Subfunctor.homOfLe le_sup_left)
  let j₂ := SimplicialRealization.realizationMap Q₂ Q₁₂ (Subfunctor.homOfLe le_sup_right)
  have hw : SimplicialRealization.realizationMap Q₀ Q₁ (Subfunctor.homOfLe inf_le_left) ≫ j₁ =
      SimplicialRealization.realizationMap Q₀ Q₂ (Subfunctor.homOfLe inf_le_right) ≫ j₂ := by
    rw [← SimplicialRealization.realizationMap_comp, ← SimplicialRealization.realizationMap_comp]
    rfl
  rw [isPushout_iff_isUniversalCocone_supCocone Q₀ Q₁ Q₂ j₁ j₂ hw]
  have heq : supCocone Q₀ Q₁ Q₂ j₁ j₂ hw = Q₁₂.cocone := by
    ext k hk x
    rcases x.2 with hx₁ | hx₂
    · rw [supCocone_ι_of_mem_left Q₀ Q₁ Q₂ j₁ j₂ hw k hk x hx₁,
        SimplicialRealization.ι_realizationMap]
      rfl
    · rw [supCocone_ι_of_mem_right Q₀ Q₁ Q₂ j₁ j₂ hw k hk x hx₂,
        SimplicialRealization.ι_realizationMap]
      rfl
  rw [heq]
  exact Q₁₂.isUniversal

/-- If `G : C ⥤ C'` preserves the universal cocones `Q₀, Q₁, Q₂` and maps the pushout square of
`Q₀, Q₁, Q₂, Q₁₂` to a pushout square in `C'`, then `G` also preserves the universal cocone `Q₁₂`. -/
theorem isUniversalCocone_mapFunctor_of_sup {C' : Type u₃} [Category.{v₃} C'] (G : C ⥤ C')
    (Q₁₂ : SimplicialRealization D (S₁ ⊔ S₂).toFunctor)
    (hQ₀ : IsUniversalCocone (Q₀.cocone.mapFunctor G))
    (hQ₁ : IsUniversalCocone (Q₁.cocone.mapFunctor G))
    (hQ₂ : IsUniversalCocone (Q₂.cocone.mapFunctor G))
    (hsq : IsPushout
      (G.map (SimplicialRealization.realizationMap Q₀ Q₁ (Subfunctor.homOfLe inf_le_left)))
      (G.map (SimplicialRealization.realizationMap Q₀ Q₂ (Subfunctor.homOfLe inf_le_right)))
      (G.map (SimplicialRealization.realizationMap Q₁ Q₁₂ (Subfunctor.homOfLe le_sup_left)))
      (G.map (SimplicialRealization.realizationMap Q₂ Q₁₂ (Subfunctor.homOfLe le_sup_right)))) :
    IsUniversalCocone (Q₁₂.cocone.mapFunctor G) := by
  let Q₀' := hQ₀.toRealization
  let Q₁' := hQ₁.toRealization
  let Q₂' := hQ₂.toRealization
  have hi₁ : SimplicialRealization.realizationMap Q₀' Q₁' (Subfunctor.homOfLe inf_le_left) =
      G.map (SimplicialRealization.realizationMap Q₀ Q₁ (Subfunctor.homOfLe inf_le_left)) := by
    apply Q₀'.hom_ext
    intro k hk x
    rw [SimplicialRealization.ι_realizationMap]
    change G.map (Q₁.cocone.ι k hk ⟨x.1, x.2.1⟩) =
      G.map (Q₀.cocone.ι k hk x) ≫
        G.map (SimplicialRealization.realizationMap Q₀ Q₁ (Subfunctor.homOfLe inf_le_left))
    rw [← G.map_comp, SimplicialRealization.ι_realizationMap]
    rfl
  have hi₂ : SimplicialRealization.realizationMap Q₀' Q₂' (Subfunctor.homOfLe inf_le_right) =
      G.map (SimplicialRealization.realizationMap Q₀ Q₂ (Subfunctor.homOfLe inf_le_right)) := by
    apply Q₀'.hom_ext
    intro k hk x
    rw [SimplicialRealization.ι_realizationMap]
    change G.map (Q₂.cocone.ι k hk ⟨x.1, x.2.2⟩) =
      G.map (Q₀.cocone.ι k hk x) ≫
        G.map (SimplicialRealization.realizationMap Q₀ Q₂ (Subfunctor.homOfLe inf_le_right))
    rw [← G.map_comp, SimplicialRealization.ι_realizationMap]
    rfl
  let j₁' := G.map (SimplicialRealization.realizationMap Q₁ Q₁₂ (Subfunctor.homOfLe le_sup_left))
  let j₂' := G.map (SimplicialRealization.realizationMap Q₂ Q₁₂ (Subfunctor.homOfLe le_sup_right))
  have hsq' : IsPushout
      (SimplicialRealization.realizationMap Q₀' Q₁' (Subfunctor.homOfLe inf_le_left))
      (SimplicialRealization.realizationMap Q₀' Q₂' (Subfunctor.homOfLe inf_le_right))
      j₁' j₂' := by
    rw [hi₁, hi₂]
    exact hsq
  have huniv := (isPushout_iff_isUniversalCocone_supCocone Q₀' Q₁' Q₂' j₁' j₂' hsq'.w).mp hsq'
  have heq : supCocone Q₀' Q₁' Q₂' j₁' j₂' hsq'.w = Q₁₂.cocone.mapFunctor G := by
    ext k hk x
    rcases x.2 with hx₁ | hx₂
    · rw [supCocone_ι_of_mem_left Q₀' Q₁' Q₂' j₁' j₂' hsq'.w k hk x hx₁]
      change G.map (Q₁.cocone.ι k hk ⟨x.1, hx₁⟩) ≫
          G.map (SimplicialRealization.realizationMap Q₁ Q₁₂ (Subfunctor.homOfLe le_sup_left)) =
        G.map (Q₁₂.cocone.ι k hk x)
      rw [← G.map_comp, SimplicialRealization.ι_realizationMap]
      rfl
    · rw [supCocone_ι_of_mem_right Q₀' Q₁' Q₂' j₁' j₂' hsq'.w k hk x hx₂]
      change G.map (Q₂.cocone.ι k hk ⟨x.1, hx₂⟩) ≫
          G.map (SimplicialRealization.realizationMap Q₂ Q₁₂ (Subfunctor.homOfLe le_sup_right)) =
        G.map (Q₁₂.cocone.ι k hk x)
      rw [← G.map_comp, SimplicialRealization.ι_realizationMap]
      rfl
  rw [← heq]
  exact huniv

end SupPushout

end HomotopyHypothesis.Cylinder.SimplicialCategory
