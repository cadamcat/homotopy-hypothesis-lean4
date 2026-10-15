import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DV
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylD
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDBot
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDComplex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDTop
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.Inst57
import HomotopyHypothesis.Approximation.Topological.DerivedCylinderMap
import HomotopyHypothesis.Approximation.Topological.HelperStatements.SharpNormalFormUnique
import HomotopyHypothesis.Approximation.Topological.NormalForm.NF
import HomotopyHypothesis.Approximation.Topological.NormalForm.Nf2
import HomotopyHypothesis.Approximation.Topological.NormalForm.SharpMkNf
import HomotopyHypothesis.Approximation.Topological.NormalForm.VertexMapSimplexCharEqOfSharpMkEq
import HomotopyHypothesis.Approximation.Topological.Projection
/-!
# Folding the double prism over a semi-simplicial subset

Over the simplices on which the map to `X♯` is a semi-simplicial map (normal form with identity
vertex map), the derived double cylinder has a top half and a bottom half of the same shape, and
folding the top onto the bottom is a map of semi-simplicial sets.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet DV

/-- The map of the semi-simplicial category given by a strictly increasing vertex map. -/
def vhom {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1)) (hv : StrictMono v) :
    Henry.SemiSimplexCategory.mk n ⟶ Henry.SemiSimplexCategory.mk m :=
  ⟨SimplexCategory.Hom.mk ⟨v, hv.monotone⟩,
    SimplexCategory.mono_iff_injective.2 hv.injective⟩

theorem nf_sharpMk_id {X : SemiSSet.{u}} {n : ℕ} (x' : X.obj (op (Henry.SemiSimplexCategory.mk n))) :
    (nf (sharpMk id x')).m = n ∧ HEq (nf (sharpMk id x')).v (id : Fin (n + 1) → Fin (n + 1)) ∧
      HEq (nf (sharpMk id x')).x x' :=
  sharp_normalForm_unique _ _ _ _ (nf _).surj Function.surjective_id (sharpMk_nf _)

theorem strictMono_of_heq_id {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1)) (h : m = n)
    (hv : HEq v (id : Fin (n + 1) → Fin (n + 1))) : StrictMono v := by
  subst h
  rw [heq_iff_eq] at hv
  subst hv
  exact strictMono_id

theorem map_vhom_of_heq {X : SemiSSet.{u}} {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1))
    (hv : StrictMono v) (x : X.obj (op (Henry.SemiSimplexCategory.mk m)))
    (x' : X.obj (op (Henry.SemiSimplexCategory.mk n))) (h : m = n)
    (hvid : HEq v (id : Fin (n + 1) → Fin (n + 1))) (hx : HEq x x') :
    X.map (vhom v hv).op x = x' := by
  subst h
  rw [heq_iff_eq] at hvid hx
  subst hvid hx
  have : vhom _ hv = 𝟙 _ := rfl
  rw [this, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- The fold of a derived double cylinder: top vertices go to the bottom along `v`. -/
def foldV {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1)) : DV n m → DV n m
  | top i => bot (v i)
  | mid S => mid S
  | bot c => bot c

/-- The fold of the derived double cylinder of a strictly increasing vertex map. -/
def foldHom {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1)) (hv : StrictMono v) :
    (dcylDComplex v).Hom (dcylDComplex v) where
  f := foldV v
  strictMonoOn A hA := by
    intro a ha b hb hab
    cases a with
    | top i =>
      cases b with
      | top i' => exact DV.bot_lt_bot.2 (hv (DV.top_lt_top.1 hab))
      | mid S' => exact absurd hab (not_lt.2 (le_of_lt (DV.mid_lt_top _ _)))
      | bot c' => exact (hA.2.2.1 i c' ha hb).elim
    | mid S =>
      cases b with
      | top i' => exact DV.mid_lt_bot _ _
      | mid S' => exact hab
      | bot c' => exact DV.mid_lt_bot _ _
    | bot c =>
      cases b with
      | top i' => exact (hA.2.2.1 i' c hb ha).elim
      | mid S' => exact absurd hab (not_lt.2 (le_of_lt (DV.mid_lt_bot _ _)))
      | bot c' => exact hab
  map_S A hA := by
    have mem_mid : ∀ T, mid T ∈ A.image (foldV v) → mid T ∈ A := by
      intro T hT
      obtain ⟨a, ha, hfa⟩ := Finset.mem_image.1 hT
      cases a with
      | top i => simp [foldV] at hfa
      | mid S => simp only [foldV, DV.mid.injEq] at hfa; exact hfa ▸ ha
      | bot c => simp [foldV] at hfa
    have mem_top : ∀ i, top i ∉ A.image (foldV v) := by
      intro i hi
      obtain ⟨a, ha, hfa⟩ := Finset.mem_image.1 hi
      cases a <;> simp [foldV] at hfa
    have mem_bot : ∀ c, bot c ∈ A.image (foldV v) →
        bot c ∈ A ∨ ∃ i, top i ∈ A ∧ v i = c := by
      intro c hc
      obtain ⟨a, ha, hfa⟩ := Finset.mem_image.1 hc
      cases a with
      | top i => simp only [foldV, DV.bot.injEq] at hfa; exact Or.inr ⟨i, ha, hfa⟩
      | mid S => simp [foldV] at hfa
      | bot c' => simp only [foldV, DV.bot.injEq] at hfa; exact Or.inl (hfa ▸ ha)
    refine ⟨fun S hS => hA.1 S (mem_mid S hS),
      fun S S' hS hS' => hA.2.1 S S' (mem_mid S hS) (mem_mid S' hS'),
      fun i c hi _ => (mem_top i hi).elim, fun i S hi _ => (mem_top i hi).elim, ?_⟩
    intro c S hc hS
    rcases mem_bot c hc with h | ⟨i, hi, rfl⟩
    · exact hA.2.2.2.2 c S h (mem_mid S hS)
    · exact ⟨i, hA.2.2.2.1 i S hi (mem_mid S hS), rfl⟩

theorem Complex.Hom.toSemiSSet_comp_eq {V₁ V₂ V₃ V₄ : Type} [LinearOrder V₁] [LinearOrder V₂]
    [LinearOrder V₃] [LinearOrder V₄] {K₁ : Complex V₁} {K₂ : Complex V₂} {K₃ : Complex V₃}
    {K₄ : Complex V₄} (ψ₁ : K₁.Hom K₂) (ψ₂ : K₂.Hom K₄) (ψ₃ : K₁.Hom K₃) (ψ₄ : K₃.Hom K₄)
    (h : ψ₂.f ∘ ψ₁.f = ψ₄.f ∘ ψ₃.f) :
    ψ₁.toSemiSSet.{u} ≫ ψ₂.toSemiSSet = ψ₃.toSemiSSet ≫ ψ₄.toSemiSSet := by
  ext k σ
  apply ULift.ext
  apply Subtype.ext
  funext a
  exact congrFun h (σ.down.1 a)

section Fold

variable {X W J : SemiSSet.{u}} (j : J ⟶ W) (g : J ⟶ X) (φ : W ⟶ sharp X)
  (hφJ : ∀ y : J.Elements, φ.app y.obj (j.app y.obj y.val) =
    sharpMk (n := elDim y) id (g.app y.obj y.val))

/-- The functor from the simplices of `J` to those of `W`. -/
abbrev elMap : J.Elementsᵒᵖ ⥤ W.Elementsᵒᵖ := (NatTrans.mapElements j).op

include hφJ in
theorem elNF_elMap (y : J.Elementsᵒᵖ) :
    (elNF φ ((elMap j).obj y).unop).m = elDim y.unop ∧
      HEq (elNF φ ((elMap j).obj y).unop).v (id : Fin (elDim y.unop + 1) → Fin (elDim y.unop + 1)) ∧
      HEq (elNF φ ((elMap j).obj y).unop).x (g.app y.unop.obj y.unop.val) := by
  have h := nf_sharpMk_id (X := X) (n := elDim y.unop) (g.app y.unop.obj y.unop.val)
  have e : elNF φ ((elMap j).obj y).unop =
      nf (sharpMk (n := elDim y.unop) id (g.app y.unop.obj y.unop.val)) :=
    congrArg nf (hφJ y.unop)
  rw [e]
  exact h

include hφJ in
theorem elNF_elMap_strictMono (y : J.Elementsᵒᵖ) :
    StrictMono (elNF φ ((elMap j).obj y).unop).v :=
  strictMono_of_heq_id _ (elNF_elMap j g φ hφJ y).1 (elNF_elMap j g φ hφJ y).2.1

/-- The glued cylinder over `J` (the restriction of the one over `W`). -/
noncomputable abbrev cylJ : CylDatum X J.Elementsᵒᵖ := (cylDatum φ).restrict (elMap j)

/-- The fold of the cylinders over the simplices of `J`. -/
noncomputable def foldNat : (cylJ j φ).DC ⟶ (cylJ j φ).DC where
  app y := (foldHom _ (elNF_elMap_strictMono j g φ hφJ y)).toSemiSSet
  naturality y z f := by
    apply Complex.Hom.toSemiSSet_comp_eq
    funext d
    cases d with
    | top i =>
      change DV.bot ((elNF φ ((elMap j).obj z).unop).v
          ((elFace ((elMap j).map f).unop).1.toOrderHom i)) =
        DV.bot ((elι φ ((elMap j).map f).unop).1.toOrderHom
          ((elNF φ ((elMap j).obj y).unop).v i))
      congr 1
      exact congrFun (elι_spec φ ((elMap j).map f).unop).1 i
    | mid S => rfl
    | bot c => rfl

theorem botN_foldNat :
    (cylJ j φ).botN ≫ foldNat j g φ hφJ = (cylJ j φ).botN := by
  ext y k σ
  rfl

/-- The fold of the glued cylinder over `J`. -/
noncomputable def foldMap : (cylJ j φ).obj ⟶ (cylJ j φ).obj :=
  pushout.map _ _ _ _ (𝟙 X) (colimMap (foldNat j g φ hφJ)) (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp])
    (by
      apply colimit.hom_ext
      intro y
      rw [ι_colimMap_assoc, ι_colimMap, Category.id_comp, ι_colimMap, ← Category.assoc,
        ← NatTrans.comp_app, botN_foldNat])

theorem incl_foldMap :
    (cylJ j φ).incl ≫ foldMap j g φ hφJ = colimMap (foldNat j g φ hφJ) ≫ (cylJ j φ).incl :=
  pushout.inr_desc _ _ _

theorem base_foldMap : (cylJ j φ).base ≫ foldMap j g φ hφJ = (cylJ j φ).base := by
  unfold foldMap CylDatum.base pushout.map
  erw [pushout.inl_desc, Category.id_comp]

theorem foldNat_rhoN (y : J.Elementsᵒᵖ) :
    (foldNat j g φ hφJ).app y ≫ (rhoN φ).app ((elMap j).obj y) = (rhoN φ).app ((elMap j).obj y) := by
  ext k σ
  have hf : projDV (elNF φ ((elMap j).obj y).unop).v ∘
      foldV (elNF φ ((elMap j).obj y).unop).v ∘ σ.down.1 =
      projDV (elNF φ ((elMap j).obj y).unop).v ∘ σ.down.1 := by
    funext a
    simp only [Function.comp_apply]
    cases σ.down.1 a <;> rfl
  change ULift.up (affineMap (X := k.unop)
      (Y := Henry.SemiSimplexCategory.mk (elNF φ ((elMap j).obj y).unop).m)
      (projDV (elNF φ ((elMap j).obj y).unop).v ∘
        foldV (elNF φ ((elMap j).obj y).unop).v ∘ σ.down.1) ≫
      simplexChar (uliftYonedaEquiv.symm (elNF φ ((elMap j).obj y).unop).x)) = _
  rw [hf]
  rfl

theorem foldMap_toSing :
    foldMap j g φ hφJ ≫ (cylJ j φ).toSing (Functor.whiskerLeft (elMap j) (rhoN φ))
        (by
          apply NatTrans.ext
          funext i
          exact congrArg (fun τ => τ.app ((elMap j).obj i)) (botN_rhoN φ)) =
      (cylJ j φ).toSing (Functor.whiskerLeft (elMap j) (rhoN φ))
        (by
          apply NatTrans.ext
          funext i
          exact congrArg (fun τ => τ.app ((elMap j).obj i)) (botN_rhoN φ)) := by
  apply pushout.hom_ext
  · change (cylJ j φ).base ≫ _ ≫ _ = (cylJ j φ).base ≫ _
    rw [← Category.assoc, base_foldMap]
  · change (cylJ j φ).incl ≫ _ ≫ _ = (cylJ j φ).incl ≫ _
    rw [← Category.assoc, incl_foldMap, Category.assoc]
    apply colimit.hom_ext
    intro y
    rw [ι_colimMap_assoc]
    erw [CylDatum.incl_toSing]
    exact foldNat_rhoN j g φ hφJ y

end Fold

section Top

variable {X K : SemiSSet.{u}} (φ : K ⟶ sharp X)

/-- The top copies of the simplices of `K` in their cylinders. -/
noncomputable def topNatDC : Presheaf.functorToRepresentables.{u} K ⟶ dcylDFunctor φ where
  app y := dcylDTop (elNF φ y.unop).v
  naturality y z f := by
    ext k σ
    rfl

/-- The top map of `K` into its glued cylinder. -/
noncomputable def topW : K ⟶ (cylDatum φ).obj :=
  (cylDatum φ).topMap (topNatDC φ ≫ (colimit.cocone (dcylDFunctor φ)).ι ≫
    (Functor.const _).map (cylDatum φ).incl)

theorem ι_topW (y : K.Elementsᵒᵖ) :
    uliftYonedaEquiv.symm y.unop.val ≫ topW φ =
      (topNatDC φ).app y ≫ colimit.ι (dcylDFunctor φ) y ≫ (cylDatum φ).incl :=
  (cylDatum φ).ι_topMap _ y

end Top

theorem dcylDTop_fold {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1)) (hv : StrictMono v) :
    dcylDTop.{u} v ≫ (foldHom v hv).toSemiSSet =
      Henry.SemiSSet.stdSimplex.map (vhom v hv) ≫ dcylDBot v := by
  ext k σ
  rfl

section TopJ

variable {X W J : SemiSSet.{u}} (j : J ⟶ W) (g : J ⟶ X) (φ : W ⟶ sharp X)
  (hφJ : ∀ y : J.Elements, φ.app y.obj (j.app y.obj y.val) =
    sharpMk (n := elDim y) id (g.app y.obj y.val))

/-- The top copies of the simplices of `J` in their cylinders. -/
noncomputable def topNatJ : Presheaf.functorToRepresentables.{u} J ⟶ (cylJ j φ).DC where
  app y := dcylDTop (elNF φ ((elMap j).obj y).unop).v
  naturality y z f := by
    ext k σ
    rfl

/-- The top map of `J` into the glued cylinder over `J`. -/
noncomputable def topJ : J ⟶ (cylJ j φ).obj :=
  (cylJ j φ).topMap (topNatJ j φ ≫ (colimit.cocone (cylJ j φ).DC).ι ≫
    (Functor.const _).map (cylJ j φ).incl)

theorem ι_topJ (y : J.Elementsᵒᵖ) :
    uliftYonedaEquiv.symm y.unop.val ≫ topJ j φ =
      (topNatJ j φ).app y ≫ colimit.ι (cylJ j φ).DC y ≫ (cylJ j φ).incl :=
  (cylJ j φ).ι_topMap _ y

theorem incl_restrictMap :
    (cylJ j φ).incl ≫ (cylDatum φ).restrictMap (elMap j) =
      colimit.pre (dcylDFunctor φ) (elMap j) ≫ (cylDatum φ).incl :=
  pushout.inr_desc _ _ _

theorem j_topW : j ≫ topW φ = topJ j φ ≫ (cylDatum φ).restrictMap (elMap j) := by
  apply (Presheaf.colimitOfRepresentable.{u} J).hom_ext
  intro y
  have h₁ : (Presheaf.coconeOfRepresentable.{u} J).ι.app y ≫ j ≫ topW φ =
      (topNatDC φ).app ((elMap j).obj y) ≫ colimit.ι (dcylDFunctor φ) ((elMap j).obj y) ≫
        (cylDatum φ).incl := by
    have := ι_topW φ ((elMap j).obj y)
    rw [← this]
    exact uliftYonedaEquiv_symm_comp_assoc _ _ _
  have h₂ : (Presheaf.coconeOfRepresentable.{u} J).ι.app y ≫ topJ j φ ≫
      (cylDatum φ).restrictMap (elMap j) =
      ((topNatJ j φ).app y ≫ colimit.ι (cylJ j φ).DC y ≫ (cylJ j φ).incl) ≫
        (cylDatum φ).restrictMap (elMap j) := by
    rw [← ι_topJ j φ y]
    exact (Category.assoc _ _ _).symm
  have h₃ : (topNatDC φ).app ((elMap j).obj y) ≫ colimit.ι (dcylDFunctor φ) ((elMap j).obj y) ≫
        (cylDatum φ).incl =
      ((topNatJ j φ).app y ≫ colimit.ι (cylJ j φ).DC y ≫ (cylJ j φ).incl) ≫
        (cylDatum φ).restrictMap (elMap j) := by
    rw [Category.assoc, Category.assoc, incl_restrictMap]
    erw [colimit.ι_pre_assoc]
    rfl
  exact h₁.trans (h₃.trans h₂.symm)

include hφJ in
theorem topNatJ_fold (y : J.Elementsᵒᵖ) :
    (topNatJ j φ).app y ≫ (foldNat j g φ hφJ).app y =
      Henry.SemiSSet.stdSimplex.map (vhom _ (elNF_elMap_strictMono j g φ hφJ y)) ≫
        (cylJ j φ).botN.app y := by
  ext k σ
  rfl

include hφJ in
theorem topJ_fold : topJ j φ ≫ foldMap j g φ hφJ = g ≫ (cylJ j φ).base := by
  apply (Presheaf.colimitOfRepresentable.{u} J).hom_ext
  intro y
  have h₁ : (Presheaf.coconeOfRepresentable.{u} J).ι.app y ≫ topJ j φ ≫ foldMap j g φ hφJ =
      ((topNatJ j φ).app y ≫ colimit.ι (cylJ j φ).DC y ≫ (cylJ j φ).incl) ≫
        foldMap j g φ hφJ := by
    rw [← ι_topJ j φ y]
    exact (Category.assoc _ _ _).symm
  have hc : (cylJ j φ).botN.app y ≫ colimit.ι (cylJ j φ).DC y ≫ (cylJ j φ).incl =
      (cylJ j φ).xN.app y ≫ (cylJ j φ).base := by
    have := pushout.condition (f := colimit.desc (cylJ j φ).B (Cocone.mk X (cylJ j φ).xN))
      (g := colimMap (cylJ j φ).botN)
    have := congrArg (fun k => colimit.ι (cylJ j φ).B y ≫ k) this
    simp only [colimit.ι_desc_assoc, ι_colimMap_assoc] at this
    exact this.symm
  have hx := map_vhom_of_heq _ (elNF_elMap_strictMono j g φ hφJ y)
    (elNF φ ((elMap j).obj y).unop).x (g.app y.unop.obj y.unop.val)
    (elNF_elMap j g φ hφJ y).1 (elNF_elMap j g φ hφJ y).2.1 (elNF_elMap j g φ hφJ y).2.2
  have h₂ : ((topNatJ j φ).app y ≫ colimit.ι (cylJ j φ).DC y ≫ (cylJ j φ).incl) ≫
      foldMap j g φ hφJ =
      Henry.SemiSSet.stdSimplex.map (vhom _ (elNF_elMap_strictMono j g φ hφJ y)) ≫
        ((cylJ j φ).botN.app y ≫ colimit.ι (cylJ j φ).DC y ≫ (cylJ j φ).incl) := by
    rw [Category.assoc, Category.assoc, incl_foldMap, ι_colimMap_assoc, ← Category.assoc,
      topNatJ_fold j g φ hφJ y]
    exact Category.assoc _ _ _
  have h₃ : Henry.SemiSSet.stdSimplex.map (vhom _ (elNF_elMap_strictMono j g φ hφJ y)) ≫
      ((cylJ j φ).xN.app y ≫ (cylJ j φ).base) =
      (Presheaf.coconeOfRepresentable.{u} J).ι.app y ≫ g ≫ (cylJ j φ).base := by
    change Henry.SemiSSet.stdSimplex.map _ ≫ uliftYonedaEquiv.symm _ ≫ _ =
      uliftYonedaEquiv.symm y.unop.val ≫ g ≫ _
    rw [uliftYonedaEquiv_symm_comp_assoc, ← hx, uliftYonedaEquiv_symm_map_assoc]
    rfl
  exact h₁.trans (h₂.trans ((congrArg (fun k =>
    Henry.SemiSSet.stdSimplex.map (vhom _ (elNF_elMap_strictMono j g φ hφJ y)) ≫ k) hc).trans h₃))

end TopJ

section Proj

variable {X K : SemiSSet.{u}} (φ : K ⟶ sharp X)

theorem topW_toSing (F : realization.obj K ⟶ realization.obj X)
    (hφ : ∀ (n : ℕ) (y : stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶ K),
      ∃ (m : ℕ) (x : stdSimplex.obj (Henry.SemiSimplexCategory.mk m) ⟶ X)
        (v : Fin (n + 1) → Fin (m + 1)),
        φ.app (op (Henry.SemiSimplexCategory.mk n)) (uliftYonedaEquiv y) =
            sharpMk v (uliftYonedaEquiv x) ∧
          simplexChar y ≫ F = vertexMap v ≫ simplexChar x) :
    topW φ ≫ (cylDatum φ).toSing (rhoN φ) (botN_rhoN φ) = ((realAdj.{u}).homEquiv _ _) F := by
  apply (Presheaf.colimitOfRepresentable.{u} K).hom_ext
  intro y
  have h₁ : (Presheaf.coconeOfRepresentable.{u} K).ι.app y ≫ topW φ ≫
      (cylDatum φ).toSing (rhoN φ) (botN_rhoN φ) = (topNatDC φ).app y ≫ (rhoN φ).app y := by
    have := ι_topW φ y
    change uliftYonedaEquiv.symm y.unop.val ≫ _ ≫ _ = _
    rw [← Category.assoc, this]
    erw [Category.assoc, Category.assoc, CylDatum.incl_toSing]
    rfl
  refine h₁.trans ?_
  apply uliftYonedaEquiv.injective
  change ((rhoN φ).app y).app _ (uliftYonedaEquiv ((topNatDC φ).app y)) =
    (((realAdj.{u}).homEquiv _ _) F).app _ (uliftYonedaEquiv (uliftYonedaEquiv.symm y.unop.val))
  rw [Equiv.apply_symm_apply]
  have hF := Presheaf.uliftYonedaAdjunction_homEquiv_app.{u}
    (stdSimplex.{u}.leftKanExtension toTop.{u}) (stdSimplex.{u}.leftKanExtensionUnit toTop.{u})
    F (Z := y.unop.obj) y.unop.val
  refine Eq.trans ?_ hF.symm
  obtain ⟨m, x, v, h₂, h₃⟩ := hφ (elDim y.unop) (uliftYonedaEquiv.symm y.unop.val)
  rw [Equiv.apply_symm_apply] at h₂
  have h₄ := vertexMap_simplexChar_eq_of_sharpMk_eq (elNF φ y.unop).v
    (uliftYonedaEquiv.symm (elNF φ y.unop).x) v x
    (by rw [Equiv.apply_symm_apply, sharpMk_elNF]; exact h₂)
  change ULift.up (vertexMap (elNF φ y.unop).v ≫
      simplexChar (uliftYonedaEquiv.symm (elNF φ y.unop).x)) =
    ULift.up (simplexChar (uliftYonedaEquiv.symm y.unop.val) ≫ F)
  rw [h₄, h₃]

end Proj

end HomotopyHypothesis.Approximation.Topological
