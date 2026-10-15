import HomotopyHypothesis.Cylinder.SimplicialCategory.HornFiltration
import HomotopyHypothesis.Cylinder.SimplicialCategory.SimplexLift
import HomotopyHypothesis.Cylinder.SimplicialCategory.SimplexRealization
import HomotopyHypothesis.Cylinder.SimplicialCategory.SimplexSubfunctors
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Realization.SemisimplicialComparison.CDeltaFacts
/-!
# Algebraic Kan nerves of cosimplicial objects with horn retractions

Let `D : Henry.SemiSimplexCategory ⥤ C` be a cosimplicial object of a category `C`, equipped with
realizations of the horns `Λ^{n+1}_k` along `D` and retractions of the realized horn inclusions.
Then `z ↦ (Δ ↦ (D Δ ⟶ z))` is an algebraic Kan complex: a horn is filled by composing the
retraction with the map out of the realized horn. This gives a nerve functor `C ⥤ AlgKan`.

We then study corepresentations along a functor `N : C ⥤ AlgKan`: an object `P : C` with
`u : A ⟶ N P` such that `u ≫ N.map -` is a bijection `(P ⟶ z) ≃ (A ⟶ N z)`. Corepresentations
exist for initial objects, for free objects on a realized semi-simplicial set, and are stable under
pushouts.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace HomotopyHypothesis.Coherator.Comparison

open HomotopyHypothesis.Henry HomotopyHypothesis.Cylinder.SimplicialCategory

section Nerve

variable {C : Type (u + 1)} [Category.{u} C]

/-- The truncations of a cosimplicial object. -/
@[simps]
def toUpTo (D : Henry.SemiSimplexCategory ⥤ C) (M : ℕ) : CosimplicialUpTo C M where
  obj k _ := D.obj (Henry.SemiSimplexCategory.mk k)
  map _ _ g := D.map g
  map_id k _ := D.map_id (Henry.SemiSimplexCategory.mk k)
  map_comp _ _ _ f g := D.map_comp f g

/-- The semi-simplicial set `Δ ↦ (D Δ ⟶ z)`. -/
def nerveSemiSSet (D : Henry.SemiSimplexCategory ⥤ C) (z : C) : SemiSSet.{u} where
  obj Δ := D.obj (unop Δ) ⟶ z
  map g := ↾fun f => D.map g.unop ≫ f
  map_id Δ := by
    ext f
    change D.map (𝟙 (unop Δ)) ≫ f = f
    rw [D.map_id, Category.id_comp]
  map_comp f g := by
    ext x
    change D.map (g.unop ≫ f.unop) ≫ x = D.map g.unop ≫ D.map f.unop ≫ x
    rw [D.map_comp, Category.assoc]

lemma nerveSemiSSet_map_apply (D : Henry.SemiSimplexCategory ⥤ C) (z : C)
    {Δ Δ' : Henry.SemiSimplexCategoryᵒᵖ} (g : Δ ⟶ Δ') (f : D.obj (unop Δ) ⟶ z) :
    (nerveSemiSSet D z).map g f = D.map g.unop ≫ f := rfl

/-- Functoriality of `nerveSemiSSet D` in `z`. -/
def nerveSemiSSetMap (D : Henry.SemiSimplexCategory ⥤ C) {z₁ z₂ : C} (h : z₁ ⟶ z₂) :
    nerveSemiSSet D z₁ ⟶ nerveSemiSSet D z₂ where
  app Δ := ↾fun (f : D.obj (unop Δ) ⟶ z₁) => f ≫ h
  naturality Δ Δ' g := by
    ext f
    exact Category.assoc (D.map g.unop) (f : D.obj (unop Δ) ⟶ z₁) h

lemma nerveSemiSSetMap_app_apply (D : Henry.SemiSimplexCategory ⥤ C) {z₁ z₂ : C} (h : z₁ ⟶ z₂)
    (Δ : Henry.SemiSimplexCategoryᵒᵖ) (f : D.obj (unop Δ) ⟶ z₁) :
    (nerveSemiSSetMap D h).app Δ f = f ≫ h := rfl

/-- The semi-simplicial map `Δ_n ⟶ nerveSemiSSet D z` classifying `f : D [n] ⟶ z`. -/
def simplexNat (D : Henry.SemiSimplexCategory ⥤ C) {n : ℕ} {z : C}
    (f : D.obj (Henry.SemiSimplexCategory.mk n) ⟶ z) :
    SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk n) ⟶ nerveSemiSSet D z where
  app Δ := ↾fun g => D.map (ULift.down g) ≫ f
  naturality Δ Δ' θ := by
    ext g
    change D.map (θ.unop ≫ ULift.down g) ≫ f = D.map θ.unop ≫ D.map (ULift.down g) ≫ f
    rw [D.map_comp, Category.assoc]

lemma simplexNat_app_apply (D : Henry.SemiSimplexCategory ⥤ C) {n : ℕ} {z : C}
    (f : D.obj (Henry.SemiSimplexCategory.mk n) ⟶ z) (Δ : Henry.SemiSimplexCategoryᵒᵖ)
    (g : (SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk n)).obj Δ) :
    (simplexNat D f).app Δ g = D.map (ULift.down g) ≫ f := rfl

lemma simplexNat_comp (D : Henry.SemiSimplexCategory ⥤ C) {n : ℕ} {z₁ z₂ : C}
    (f : D.obj (Henry.SemiSimplexCategory.mk n) ⟶ z₁) (h : z₁ ⟶ z₂) :
    simplexNat D f ≫ nerveSemiSSetMap D h = simplexNat D (f ≫ h) := by
  ext Δ g
  exact Category.assoc _ _ _

/-- A semi-simplicial map into `nerveSemiSSet D z` is a simplicial cocone along `D`. -/
@[simps]
def coconeOfNat (D : Henry.SemiSimplexCategory ⥤ C) (M : ℕ) {F : SemiSSet.{u}} {z : C}
    (α : F ⟶ nerveSemiSSet D z) : SimplicialCocone (toUpTo D M) F z where
  ι k _ x := α.app (op (Henry.SemiSimplexCategory.mk k)) x
  w _ _ g x := (ConcreteCategory.congr_hom (α.naturality g.op) x).symm

/-- Cosimplicial data: a cosimplicial object with realized horns and retractions of the realized
horn inclusions (stated on the legs of the horn realization). -/
structure CosimplicialData (C : Type (u + 1)) [Category.{u} C] where
  /-- the cosimplicial object -/
  D : Henry.SemiSimplexCategory ⥤ C
  /-- realizations of the horns -/
  Q_horn : ∀ (n : ℕ) (k : Fin (n + 2)),
    SimplicialRealization (toUpTo D (n + 1)) (SemiSSet.horn.{u} (n + 1) k).toFunctor
  /-- the retractions -/
  r_horn : ∀ (n : ℕ) (k : Fin (n + 2)), D.obj (Henry.SemiSimplexCategory.mk (n + 1)) ⟶ (Q_horn n k).pt
  r_horn_spec : ∀ (n : ℕ) (k : Fin (n + 2)) (m : ℕ) (hm : m ≤ n + 1)
    (x : (SemiSSet.horn.{u} (n + 1) k).toFunctor.obj (op (Henry.SemiSimplexCategory.mk m))),
    D.map (ULift.down x.1) ≫ r_horn n k = (Q_horn n k).cocone.ι m hm x

namespace CosimplicialData

variable (CD : CosimplicialData C)

/-- The map out of a realized horn classified by a horn of the nerve. -/
noncomputable def hornDesc {n : ℕ} {k : Fin (n + 2)} {z : C}
    (α : (SemiSSet.horn.{u} (n + 1) k).toFunctor ⟶ nerveSemiSSet CD.D z) :
    (CD.Q_horn n k).pt ⟶ z :=
  (CD.Q_horn n k).desc (coconeOfNat CD.D (n + 1) α)

lemma ι_hornDesc {n : ℕ} {k : Fin (n + 2)} {z : C}
    (α : (SemiSSet.horn.{u} (n + 1) k).toFunctor ⟶ nerveSemiSSet CD.D z) (m : ℕ)
    (hm : m ≤ n + 1)
    (x : (SemiSSet.horn.{u} (n + 1) k).toFunctor.obj (op (Henry.SemiSimplexCategory.mk m))) :
    (CD.Q_horn n k).cocone.ι m hm x ≫ CD.hornDesc α = α.app (op (Henry.SemiSimplexCategory.mk m)) x :=
  (CD.Q_horn n k).fac _ m hm x

lemma hornDesc_comp {n : ℕ} {k : Fin (n + 2)} {z₁ z₂ : C}
    (α : (SemiSSet.horn.{u} (n + 1) k).toFunctor ⟶ nerveSemiSSet CD.D z₁) (h : z₁ ⟶ z₂) :
    CD.hornDesc α ≫ h = CD.hornDesc (α ≫ nerveSemiSSetMap CD.D h) := by
  apply (CD.Q_horn n k).hom_ext
  intro m hm x
  rw [← Category.assoc, ι_hornDesc, ι_hornDesc]
  rfl

/-- The algebraic Kan nerve of `z`. -/
noncomputable def nerveObj (z : C) : AlgKan.{u} where
  X := nerveSemiSSet CD.D z
  fill n k α := simplexNat CD.D (CD.r_horn n k ≫ CD.hornDesc α)
  fill_spec n k α := by
    ext Δ x
    have hm : (unop Δ).obj.len ≤ n + 1 := len_le_of_hom (ULift.down x.1)
    change CD.D.map (ULift.down x.1) ≫ CD.r_horn n k ≫ CD.hornDesc α = α.app Δ x
    rw [← Category.assoc, CD.r_horn_spec n k _ hm x]
    exact CD.ι_hornDesc α _ hm x

/-- The algebraic Kan nerve functor. -/
noncomputable def nerve : C ⥤ AlgKan.{u} where
  obj := CD.nerveObj
  map h :=
    { hom := nerveSemiSSetMap CD.D h
      fill_hom := fun n k α => by
        change simplexNat CD.D (CD.r_horn n k ≫ CD.hornDesc α) ≫ nerveSemiSSetMap CD.D h =
          simplexNat CD.D (CD.r_horn n k ≫ CD.hornDesc (α ≫ nerveSemiSSetMap CD.D h))
        rw [simplexNat_comp, Category.assoc]
        exact congrArg (fun t => simplexNat CD.D (CD.r_horn n k ≫ t)) (CD.hornDesc_comp α h) }
  map_id z := by
    apply AlgKan.Hom.ext
    ext Δ f
    exact Category.comp_id _
  map_comp f g := by
    apply AlgKan.Hom.ext
    ext Δ x
    exact (Category.assoc _ _ _).symm

lemma nerve_obj_X (z : C) : (CD.nerve.obj z).X = nerveSemiSSet CD.D z := rfl

lemma nerve_map_hom {z₁ z₂ : C} (h : z₁ ⟶ z₂) :
    (CD.nerve.map h).hom = nerveSemiSSetMap CD.D h := rfl

end CosimplicialData

/-- A morphism of cosimplicial data along a functor `G`: `G` maps the cosimplicial object of
`CD₁` to that of `CD₂` and is compatible with the horn fillers. -/
structure CosimplicialMorphism {C₁ C₂ : Type (u + 1)} [Category.{u} C₁] [Category.{u} C₂]
    (G : C₁ ⥤ C₂) (CD₁ : CosimplicialData C₁) (CD₂ : CosimplicialData C₂) where
  obj_eq : ∀ Δ : Henry.SemiSimplexCategory, G.obj (CD₁.D.obj Δ) = CD₂.D.obj Δ
  map_eq : ∀ {Δ₁ Δ₂ : Henry.SemiSimplexCategory} (g : Δ₁ ⟶ Δ₂),
    G.map (CD₁.D.map g) = eqToHom (obj_eq Δ₁) ≫ CD₂.D.map g ≫ eqToHom (obj_eq Δ₂).symm
  fill_eq : ∀ (n : ℕ) (k : Fin (n + 2)) {z : C₁}
    (α : (SemiSSet.horn.{u} (n + 1) k).toFunctor ⟶ nerveSemiSSet CD₁.D z)
    (β : (SemiSSet.horn.{u} (n + 1) k).toFunctor ⟶ nerveSemiSSet CD₂.D (G.obj z)),
    (∀ (m : ℕ) (x : (SemiSSet.horn.{u} (n + 1) k).toFunctor.obj (op (Henry.SemiSimplexCategory.mk m))),
      β.app _ x = eqToHom (obj_eq _).symm ≫ G.map (α.app _ x)) →
    eqToHom (obj_eq (Henry.SemiSimplexCategory.mk (n + 1))).symm ≫
        G.map (CD₁.r_horn n k ≫ CD₁.hornDesc α) =
      CD₂.r_horn n k ≫ CD₂.hornDesc β

namespace CosimplicialMorphism

variable {C₁ C₂ : Type (u + 1)} [Category.{u} C₁] [Category.{u} C₂]
  {G : C₁ ⥤ C₂} {CD₁ : CosimplicialData C₁} {CD₂ : CosimplicialData C₂}
  (Φ : CosimplicialMorphism G CD₁ CD₂)

lemma natOn_aux {Δ₁ Δ₂ : Henry.SemiSimplexCategory} (g : Δ₂ ⟶ Δ₁) {z : C₁}
    (f : CD₁.D.obj Δ₁ ⟶ z) :
    eqToHom (Φ.obj_eq Δ₂).symm ≫ G.map (CD₁.D.map g ≫ f) =
      CD₂.D.map g ≫ eqToHom (Φ.obj_eq Δ₁).symm ≫ G.map f := by
  rw [G.map_comp, Φ.map_eq g]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- The induced map of nerves (semi-simplicial part). -/
def natOn (z : C₁) : nerveSemiSSet CD₁.D z ⟶ nerveSemiSSet CD₂.D (G.obj z) where
  app Δ := ↾fun (f : CD₁.D.obj (unop Δ) ⟶ z) => eqToHom (Φ.obj_eq (unop Δ)).symm ≫ G.map f
  naturality {Δ₁ Δ₂} g := by
    ext f
    exact Φ.natOn_aux g.unop (f : CD₁.D.obj (unop Δ₁) ⟶ z)

lemma natOn_app_apply (z : C₁) (Δ : Henry.SemiSimplexCategoryᵒᵖ) (f : CD₁.D.obj (unop Δ) ⟶ z) :
    (Φ.natOn z).app Δ f = eqToHom (Φ.obj_eq (unop Δ)).symm ≫ G.map f := rfl

/-- The natural transformation of nerves `CD₁.nerve ⟶ G ⋙ CD₂.nerve`. -/
noncomputable def mapNerve : CD₁.nerve ⟶ G ⋙ CD₂.nerve where
  app z :=
    { hom := Φ.natOn z
      fill_hom := fun n k α => by
        ext Δ g
        change eqToHom (Φ.obj_eq (unop Δ)).symm ≫
            G.map (CD₁.D.map (ULift.down g) ≫ CD₁.r_horn n k ≫ CD₁.hornDesc α) =
          CD₂.D.map (ULift.down g) ≫ CD₂.r_horn n k ≫ CD₂.hornDesc (α ≫ Φ.natOn z)
        rw [G.map_comp, Φ.map_eq, ← Φ.fill_eq n k α (α ≫ Φ.natOn z) (fun _ _ => rfl)]
        simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] }
  naturality z₁ z₂ f := by
    apply AlgKan.Hom.ext
    ext Δ x
    exact (show ∀ x' : CD₁.D.obj (unop Δ) ⟶ z₁, eqToHom (Φ.obj_eq (unop Δ)).symm ≫ G.map (x' ≫ f) =
      (eqToHom (Φ.obj_eq (unop Δ)).symm ≫ G.map x') ≫ G.map f from
        fun x' => by rw [G.map_comp, Category.assoc]) x

lemma mapNerve_app_hom (z : C₁) : (Φ.mapNerve.app z).hom = Φ.natOn z := rfl

end CosimplicialMorphism

end Nerve

/-!
## Corepresentations along a functor to algebraic Kan complexes
-/

section Corep

variable {C : Type (u + 1)} [Category.{u} C]

/-- `(P, u)` corepresents `A` along `N`: `f ↦ u ≫ N.map f` is a bijection `(P ⟶ z) ≃ (A ⟶ N z)`. -/
def IsCorep (N : C ⥤ AlgKan.{u}) (A : AlgKan.{u}) (P : C) (u : A ⟶ N.obj P) : Prop :=
  ∀ z : C, Function.Bijective (fun f : P ⟶ z => u ≫ N.map f)

namespace IsCorep

variable {N : C ⥤ AlgKan.{u}} {A : AlgKan.{u}} {P : C} {u : A ⟶ N.obj P}

/-- The map `P ⟶ z` classified by `g : A ⟶ N z`. -/
noncomputable def desc (h : IsCorep N A P u) {z : C} (g : A ⟶ N.obj z) : P ⟶ z :=
  ((h z).2 g).choose

@[reassoc]
lemma fac (h : IsCorep N A P u) {z : C} (g : A ⟶ N.obj z) : u ≫ N.map (h.desc g) = g :=
  ((h z).2 g).choose_spec

lemma hom_ext (h : IsCorep N A P u) {z : C} {f₁ f₂ : P ⟶ z}
    (e : u ≫ N.map f₁ = u ≫ N.map f₂) : f₁ = f₂ :=
  (h z).1 e

lemma eq_desc (h : IsCorep N A P u) {z : C} {g : A ⟶ N.obj z} {f : P ⟶ z}
    (e : u ≫ N.map f = g) : f = h.desc g :=
  h.hom_ext (e.trans (h.fac g).symm)

/-- Corepresentations are stable under isomorphisms of the corepresenting object. -/
lemma of_iso (h : IsCorep N A P u) {P' : C} (e : P ≅ P') :
    IsCorep N A P' (u ≫ N.map e.hom) := by
  intro z
  refine ⟨fun f₁ f₂ hf => ?_, fun g => ⟨e.inv ≫ h.desc g, ?_⟩⟩
  · have : e.hom ≫ f₁ = e.hom ≫ f₂ := h.hom_ext (by
      simpa only [Functor.map_comp, Category.assoc] using hf)
    simpa using congrArg (e.inv ≫ ·) this
  · change (u ≫ N.map e.hom) ≫ N.map (e.inv ≫ h.desc g) = g
    rw [Category.assoc, ← N.map_comp, Iso.hom_inv_id_assoc, h.fac]

/-- Corepresentations are stable under isomorphisms of the corepresented object. -/
lemma precomp_iso (h : IsCorep N A P u) {A' : AlgKan.{u}} (e : A' ≅ A) :
    IsCorep N A' P (e.hom ≫ u) := by
  intro z
  refine ⟨fun f₁ f₂ hf => h.hom_ext ?_, fun g => ⟨h.desc (e.inv ≫ g), ?_⟩⟩
  · have := congrArg (e.inv ≫ ·) hf
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using this
  · change (e.hom ≫ u) ≫ N.map (h.desc (e.inv ≫ g)) = g
    rw [Category.assoc, h.fac, Iso.hom_inv_id_assoc]

/-- Two corepresentations of the same object are isomorphic. -/
lemma exists_iso (h : IsCorep N A P u) {P' : C} {u' : A ⟶ N.obj P'} (h' : IsCorep N A P' u') :
    ∃ e : P ≅ P', u ≫ N.map e.hom = u' := by
  refine ⟨⟨h.desc u', h'.desc u, h.hom_ext ?_, h'.hom_ext ?_⟩, h.fac u'⟩
  · rw [N.map_comp, h.fac_assoc, h'.fac, N.map_id, Category.comp_id]
  · rw [N.map_comp, h'.fac_assoc, h.fac, N.map_id, Category.comp_id]

/-- An initial object corepresents an initial object. -/
lemma of_isInitial (hA : IsInitial A) (hP : IsInitial P) (u : A ⟶ N.obj P) : IsCorep N A P u :=
  fun z => ⟨fun _ _ _ => hP.hom_ext _ _, fun _ => ⟨hP.to z, hA.hom_ext _ _⟩⟩

/-- The corepresenting object of an initial object is initial. -/
noncomputable def isInitial (h : IsCorep N A P u) (hA : IsInitial A) : IsInitial P :=
  IsInitial.ofUniqueHom (fun z => h.desc (hA.to _)) (fun _ _ => h.hom_ext (hA.hom_ext _ _))

/-- Corepresentations are stable under pushouts. -/
lemma of_isPushout {A₀ A₁ A₂ A₃ : AlgKan.{u}} {a₁ : A₀ ⟶ A₁} {a₂ : A₀ ⟶ A₂} {b₁ : A₁ ⟶ A₃}
    {b₂ : A₂ ⟶ A₃} (hA : IsPushout a₁ a₂ b₁ b₂) {P₀ P₁ P₂ P₃ : C} {f₁ : P₀ ⟶ P₁} {f₂ : P₀ ⟶ P₂}
    {g₁ : P₁ ⟶ P₃} {g₂ : P₂ ⟶ P₃} (hP : IsPushout f₁ f₂ g₁ g₂) {u₀ : A₀ ⟶ N.obj P₀}
    {u₁ : A₁ ⟶ N.obj P₁} {u₂ : A₂ ⟶ N.obj P₂} {u₃ : A₃ ⟶ N.obj P₃}
    (h₀ : IsCorep N A₀ P₀ u₀) (h₁ : IsCorep N A₁ P₁ u₁) (h₂ : IsCorep N A₂ P₂ u₂)
    (c₁ : a₁ ≫ u₁ = u₀ ≫ N.map f₁) (c₂ : a₂ ≫ u₂ = u₀ ≫ N.map f₂)
    (d₁ : b₁ ≫ u₃ = u₁ ≫ N.map g₁) (d₂ : b₂ ≫ u₃ = u₂ ≫ N.map g₂) : IsCorep N A₃ P₃ u₃ := by
  intro z
  refine ⟨fun f f' (hf : u₃ ≫ N.map f = u₃ ≫ N.map f') => ?_, fun g => ?_⟩
  · apply hP.hom_ext
    · apply h₁.hom_ext
      rw [N.map_comp, N.map_comp, ← Category.assoc, ← Category.assoc, ← d₁, Category.assoc,
        Category.assoc, hf]
    · apply h₂.hom_ext
      rw [N.map_comp, N.map_comp, ← Category.assoc, ← Category.assoc, ← d₂, Category.assoc,
        Category.assoc, hf]
  · have hw : f₁ ≫ h₁.desc (b₁ ≫ g) = f₂ ≫ h₂.desc (b₂ ≫ g) := by
      apply h₀.hom_ext
      rw [N.map_comp, N.map_comp, ← Category.assoc, ← Category.assoc, ← c₁, ← c₂,
        Category.assoc, Category.assoc, h₁.fac, h₂.fac, ← Category.assoc, ← Category.assoc,
        hA.w]
    refine ⟨hP.desc _ _ hw, ?_⟩
    change u₃ ≫ N.map (hP.desc _ _ hw) = g
    apply hA.hom_ext
    · rw [← Category.assoc, d₁, Category.assoc, ← N.map_comp, hP.inl_desc, h₁.fac]
    · rw [← Category.assoc, d₂, Category.assoc, ← N.map_comp, hP.inr_desc, h₂.fac]

/-- Free objects on a realized semi-simplicial set are corepresented by the realization. -/
lemma of_isFreeOn (CD : CosimplicialData C) {M : ℕ} {F : SemiSSet.{u}} (hF : HasDimLe M F)
    (Q : SimplicialRealization (toUpTo CD.D M) F) {A : AlgKan.{u}} {η : F ⟶ A.X}
    (hA : A.IsFreeOn η) (u : A ⟶ CD.nerve.obj Q.pt)
    (hu : ∀ (k : ℕ) (hk : k ≤ M) (x : F.obj (op (Henry.SemiSimplexCategory.mk k))),
      (η ≫ u.hom).app (op (Henry.SemiSimplexCategory.mk k)) x = Q.cocone.ι k hk x) :
    IsCorep CD.nerve A Q.pt u := by
  intro z
  refine ⟨fun f₁ f₂ (hf : u ≫ CD.nerve.map f₁ = u ≫ CD.nerve.map f₂) => ?_, fun g => ?_⟩
  · apply Q.hom_ext
    intro k hk x
    have := ConcreteCategory.congr_hom
      (congr_app (congrArg (fun φ : A ⟶ CD.nerve.obj z => η ≫ φ.hom) hf)
        (op (Henry.SemiSimplexCategory.mk k))) x
    rw [← hu k hk x]
    exact this
  · refine ⟨Q.desc (coconeOfNat CD.D M (η ≫ g.hom)), ?_⟩
    apply Realization.SemisimplicialComparison.isFreeOn_hom_ext hA
    ext Δ x
    change (η ≫ u.hom).app Δ x ≫ Q.desc (coconeOfNat CD.D M (η ≫ g.hom)) = (η ≫ g.hom).app Δ x
    rw [hu _ (hF x) x]
    exact Q.fac _ _ (hF x) x

end IsCorep

end Corep

end HomotopyHypothesis.Coherator.Comparison
