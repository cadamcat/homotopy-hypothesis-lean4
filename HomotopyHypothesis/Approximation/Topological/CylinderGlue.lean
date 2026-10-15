import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DV
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylD
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDBot
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDComplex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.Inst57
import HomotopyHypothesis.Approximation.Topological.DerivedCylinderMap
import HomotopyHypothesis.Approximation.Topological.NormalForm.NF
import HomotopyHypothesis.Approximation.Topological.NormalForm.Nf2
import HomotopyHypothesis.Approximation.Topological.NormalForm.SemiSimplexHomExtOfSurjective
import HomotopyHypothesis.Approximation.Topological.NormalForm.SharpMkNf
import HomotopyHypothesis.Approximation.Topological.NormalForm.SharpNormalFormFace
import HomotopyHypothesis.Approximation.Topological.Projection
/-!
# Gluing derived double cylinders over a semi-simplicial set

For a map `φ : K ⟶ X♯`, each simplex `y` of `K` has the derived double cylinder of the vertex map
of the normal form of `φ y`; faces of `y` give maps between these cylinders. This file defines the
resulting functor on the category of simplices of `K`.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet DV

theorem Complex.Hom.toSemiSSet_congr {V V' : Type} [LinearOrder V] [LinearOrder V']
    {K : Complex V} {K' : Complex V'} (φ ψ : K.Hom K') (h : φ.f = ψ.f) :
    φ.toSemiSSet.{u} = ψ.toSemiSSet.{u} := by
  cases φ; cases ψ; cases h; rfl

theorem Complex.Hom.toSemiSSet_id {V : Type} [LinearOrder V] {K : Complex V} (φ : K.Hom K)
    (h : φ.f = id) : φ.toSemiSSet.{u} = 𝟙 _ := by
  cases φ; cases h; rfl

theorem Complex.Hom.toSemiSSet_comp {V V' V'' : Type} [LinearOrder V] [LinearOrder V']
    [LinearOrder V''] {K : Complex V} {K' : Complex V'} {K'' : Complex V''} (φ : K.Hom K')
    (ψ : K'.Hom K'') (χ : K.Hom K'') (h : χ.f = ψ.f ∘ φ.f) :
    χ.toSemiSSet.{u} = φ.toSemiSSet ≫ ψ.toSemiSSet := by
  cases φ; cases ψ; cases χ; cases h; rfl

variable {X K : SemiSSet.{u}} (φ : K ⟶ sharp X)

/-- The dimension of a simplex of `K`. -/
abbrev elDim (y : K.Elements) : ℕ := y.obj.unop.obj.len

/-- The normal form of the image of a simplex of `K` in `X♯`. -/
noncomputable def elNF (y : K.Elements) : NF X (elDim y) :=
  nf (show (sharp X).obj (op (Henry.SemiSimplexCategory.mk (elDim y))) from φ.app y.obj y.val)

theorem sharpMk_elNF (y : K.Elements) :
    sharpMk (elNF φ y).v (elNF φ y).x = φ.app y.obj y.val :=
  sharpMk_nf _

/-- The face of `Δ_n` underlying a morphism of simplices. -/
abbrev elFace {y z : K.Elements} (f : y ⟶ z) :
    Henry.SemiSimplexCategory.mk (elDim z) ⟶ Henry.SemiSimplexCategory.mk (elDim y) :=
  f.hom.unop

theorem elFace_spec {y z : K.Elements} (f : y ⟶ z) :
    (sharp X).map (elFace f).op (sharpMk (elNF φ y).v (elNF φ y).x) =
      sharpMk (elNF φ z).v (elNF φ z).x := by
  rw [sharpMk_elNF, sharpMk_elNF]
  change (sharp X).map f.hom (φ.app y.obj y.val) = φ.app z.obj z.val
  rw [← f.map_val]
  exact (congrFun (congrArg (fun k => k.hom'.toFun) (φ.naturality f.hom)) y.val).symm

/-- The increasing injection relating the normal forms of a simplex and of its face. -/
noncomputable def elι {y z : K.Elements} (f : y ⟶ z) :
    Henry.SemiSimplexCategory.mk (elNF φ z).m ⟶ Henry.SemiSimplexCategory.mk (elNF φ y).m :=
  (sharp_normalForm_face (elFace f) _ _ _ _ (elNF φ z).surj (elFace_spec φ f)).choose

theorem elι_spec {y z : K.Elements} (f : y ⟶ z) :
    (elNF φ y).v ∘ (elFace f).1.toOrderHom = (elι φ f).1.toOrderHom ∘ (elNF φ z).v ∧
      X.map (elι φ f).op (elNF φ y).x = (elNF φ z).x :=
  (sharp_normalForm_face (elFace f) _ _ _ _ (elNF φ z).surj (elFace_spec φ f)).choose_spec

/-- The embedding underlying a map of the semi-simplicial category. -/
def semiEmb {a b : ℕ} (θ : Henry.SemiSimplexCategory.mk a ⟶ Henry.SemiSimplexCategory.mk b) :
    Fin (a + 1) ↪ Fin (b + 1) :=
  ⟨θ.1.toOrderHom, (SemiSimplexCategory.strictMono θ).injective⟩

theorem semiEmb_strictMono {a b : ℕ}
    (θ : Henry.SemiSimplexCategory.mk a ⟶ Henry.SemiSimplexCategory.mk b) :
    StrictMono (semiEmb θ) := SemiSimplexCategory.strictMono θ

/-- The map between the derived double cylinders of a simplex's face and of the simplex. -/
noncomputable def dcylDElMap {y z : K.Elements} (f : y ⟶ z) :
    (dcylDComplex (elNF φ z).v).Hom (dcylDComplex (elNF φ y).v) :=
  dcylDMapHom (semiEmb (elFace f)) (semiEmb_strictMono _) (elι φ f).1.toOrderHom
    (SemiSimplexCategory.strictMono _) (elι_spec φ f).1

theorem elι_id (y : K.Elements) : elι φ (𝟙 y) = 𝟙 _ := by
  apply semiSimplex_hom_ext_of_surjective _ (elNF φ y).surj
  have := (elι_spec φ (𝟙 y)).1
  exact this.symm

theorem elι_comp {y z w : K.Elements} (f : y ⟶ z) (g : z ⟶ w) :
    elι φ (f ≫ g) = elι φ g ≫ elι φ f := by
  apply semiSimplex_hom_ext_of_surjective _ (elNF φ w).surj
  have h₁ := (elι_spec φ (f ≫ g)).1
  have h₂ := (elι_spec φ f).1
  have h₃ := (elι_spec φ g).1
  funext a
  have e₁ := congrFun h₁ a
  have e₃ := congrFun h₃ a
  simp only [Function.comp_apply] at e₁ e₃ ⊢
  rw [← e₁]
  change (elNF φ y).v ((elFace f).1.toOrderHom ((elFace g).1.toOrderHom a)) =
    (elι φ f).1.toOrderHom ((elι φ g).1.toOrderHom ((elNF φ w).v a))
  rw [← e₃]
  have e₂ := congrFun h₂ ((elFace g).1.toOrderHom a)
  simpa only [Function.comp_apply] using e₂

/-- The functor gluing derived double cylinders over the simplices of `K`. -/
noncomputable def dcylDFunctor : K.Elementsᵒᵖ ⥤ SemiSSet.{u} where
  obj y := dcylD (elNF φ y.unop).v
  map g := (dcylDElMap φ g.unop).toSemiSSet
  map_id y := by
    apply Complex.Hom.toSemiSSet_id
    funext d
    cases d with
    | top i => rfl
    | mid S =>
      change mid (S.map (semiEmb (𝟙 _))) = mid S
      congr 1
      ext a; simp [semiEmb]
    | bot c =>
      change bot ((elι φ (𝟙 y.unop)).1.toOrderHom c) = bot c
      rw [elι_id]; rfl
  map_comp g₁ g₂ := by
    apply Complex.Hom.toSemiSSet_comp
    funext d
    cases d with
    | top i => rfl
    | mid S =>
      change mid (S.map (semiEmb _)) = mid ((S.map (semiEmb _)).map (semiEmb _))
      congr 1
      rw [Finset.map_map]
      rfl
    | bot c =>
      change bot ((elι φ (g₂.unop ≫ g₁.unop)).1.toOrderHom c) = bot _
      rw [elι_comp]; rfl

/-- The bottoms of the glued cylinders: the carrier simplices `Δ_m` of the normal forms. -/
noncomputable def botFunctor : K.Elementsᵒᵖ ⥤ SemiSSet.{u} where
  obj y := Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk (elNF φ y.unop).m)
  map g := Henry.SemiSSet.stdSimplex.map (elι φ g.unop)
  map_id y := by
    change Henry.SemiSSet.stdSimplex.map (elι φ (𝟙 y.unop)) = _
    rw [elι_id, CategoryTheory.Functor.map_id]
  map_comp g₁ g₂ := by
    change Henry.SemiSSet.stdSimplex.map (elι φ (g₂.unop ≫ g₁.unop)) = _
    rw [elι_comp, CategoryTheory.Functor.map_comp]

/-- The inclusion of the bottoms into the cylinders. -/
noncomputable def botNat : botFunctor.{u} φ ⟶ dcylDFunctor φ where
  app y := dcylDBot _
  naturality y z g := by
    ext k σ
    rfl

/-- The carrier simplices of the normal forms, as a cocone over the bottoms with point `X`. -/
noncomputable def carrierNat : botFunctor.{u} φ ⟶ (Functor.const _).obj X where
  app y := uliftYonedaEquiv.symm (elNF φ y.unop).x
  naturality y z g := by
    change uliftYoneda.map (elι φ g.unop) ≫ uliftYonedaEquiv.symm (elNF φ z.unop).x =
      uliftYonedaEquiv.symm (elNF φ y.unop).x ≫ 𝟙 X
    rw [Category.comp_id]
    have := uliftYonedaEquiv_symm_map (F := X) (elι φ g.unop).op (elNF φ z.unop).x
    rw [(elι_spec φ g.unop).2] at this
    exact this.symm

/-- A gluing datum of cylinders under `X`: cylinders and their bottoms indexed by `I`, the
inclusion of the bottoms, and the carriers of the bottoms in `X`. -/
structure CylDatum (X : SemiSSet.{u}) (I : Type u) [Category.{0} I] where
  /-- the cylinders -/
  DC : I ⥤ SemiSSet.{u}
  /-- their bottoms -/
  B : I ⥤ SemiSSet.{u}
  /-- the inclusion of the bottoms into the cylinders -/
  botN : B ⟶ DC
  /-- the carriers of the bottoms in `X` -/
  xN : B ⟶ (Functor.const I).obj X

namespace CylDatum

variable {I : Type u} [Category.{0} I] (D : CylDatum X I)

/-- The glued cylinder: the colimit of the cylinders, with their bottoms glued to `X`. -/
noncomputable def obj : SemiSSet.{u} :=
  pushout (colimit.desc D.B (Cocone.mk X D.xN)) (colimMap D.botN)

/-- The inclusion of `X` into the glued cylinder. -/
noncomputable def base : X ⟶ D.obj := pushout.inl _ _

/-- The inclusion of the colimit of the cylinders into the glued cylinder. -/
noncomputable def incl : colimit D.DC ⟶ D.obj := pushout.inr _ _

/-- Restriction of a gluing datum along a functor of index categories. -/
noncomputable abbrev restrict {I' : Type u} [Category.{0} I'] (E : I' ⥤ I) : CylDatum X I' where
  DC := E ⋙ D.DC
  B := E ⋙ D.B
  botN := Functor.whiskerLeft E D.botN
  xN := Functor.whiskerLeft E D.xN

/-- The map of glued cylinders induced by restriction along a functor. -/
noncomputable def restrictMap {I' : Type u} [Category.{0} I'] (E : I' ⥤ I) :
    (D.restrict E).obj ⟶ D.obj :=
  pushout.map _ _ _ _ (𝟙 X) (colimit.pre D.DC E) (colimit.pre D.B E)
    (by
      apply colimit.hom_ext
      intro k
      rw [Category.comp_id, colimit.ι_desc, colimit.ι_pre_assoc, colimit.ι_desc]
      rfl)
    (by
      apply colimit.hom_ext
      intro k
      rw [ι_colimMap_assoc, colimit.ι_pre, colimit.ι_pre_assoc, ι_colimMap]
      rfl)

theorem base_restrictMap {I' : Type u} [Category.{0} I'] (E : I' ⥤ I) :
    (D.restrict E).base ≫ D.restrictMap E = D.base := by
  simp only [base, restrictMap, pushout.map, Category.id_comp]
  apply pushout.inl_desc

end CylDatum

/-- The gluing datum of the derived double cylinders over the simplices of `K`. -/
noncomputable def cylDatum : CylDatum X K.Elementsᵒᵖ where
  DC := dcylDFunctor φ
  B := botFunctor φ
  botN := botNat φ
  xN := carrierNat φ

/-- The characteristic map of a face of a simplex. -/
theorem affineMap_simplexChar_map {Y : SemiSSet.{u}} {m m' : ℕ}
    (ι : Henry.SemiSimplexCategory.mk m' ⟶ Henry.SemiSimplexCategory.mk m)
    (x : Y.obj (op (Henry.SemiSimplexCategory.mk m))) :
    affineMap ι.1.toOrderHom ≫ simplexChar (uliftYonedaEquiv.symm x) =
      simplexChar (uliftYonedaEquiv.symm (Y.map ι.op x)) := by
  rw [← toTop_map_eq_affineMap]
  unfold simplexChar
  have hn : toTop.map ι ≫ (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app _ =
      (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app _ ≫
        realization.map (Henry.SemiSSet.stdSimplex.map ι) :=
    (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).naturality ι
  calc toTop.map ι ≫ (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app _ ≫
        realization.map (uliftYonedaEquiv.symm x)
      = (toTop.map ι ≫ (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app _) ≫
          realization.map (uliftYonedaEquiv.symm x) := (Category.assoc _ _ _).symm
    _ = ((stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app _ ≫
          realization.map (Henry.SemiSSet.stdSimplex.map ι)) ≫
          realization.map (uliftYonedaEquiv.symm x) :=
        congrArg (· ≫ realization.map (uliftYonedaEquiv.symm x)) hn
    _ = (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app _ ≫
          realization.map (Henry.SemiSSet.stdSimplex.map ι ≫ uliftYonedaEquiv.symm x) := by
        rw [CategoryTheory.Functor.map_comp]; exact Category.assoc _ _ _
    _ = _ := by
        congr 2
        exact (uliftYonedaEquiv_symm_map ι.op x).symm

/-- The vertex projection of a derived double cylinder: top and middle vertices to the image of
(the last vertex of) their face, bottom vertices to themselves. -/
def projDV {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1)) : DV n m → Fin (m + 1)
  | top i => v i
  | mid S => if h : S.Nonempty then v (S.max' h) else v 0
  | bot c => c

/-- The projection of the cylinder of a simplex of `K` to `‖X‖`, as a map to the singular
simplices of `‖X‖`. -/
noncomputable def rhoNat (y : K.Elementsᵒᵖ) :
    (dcylDFunctor φ).obj y ⟶
      (Presheaf.restrictedULiftYoneda.{u} toTop.{u}).obj (realization.obj X) where
  app k := TypeCat.ofHom fun σ => ULift.up
    (affineMap (X := k.unop) (Y := Henry.SemiSimplexCategory.mk (elNF φ y.unop).m)
      (projDV (elNF φ y.unop).v ∘ σ.down.1) ≫
      simplexChar (uliftYonedaEquiv.symm (elNF φ y.unop).x))
  naturality k k' θ := by
    ext σ
    change ULift.up (affineMap (X := k'.unop) (Y := Henry.SemiSimplexCategory.mk (elNF φ y.unop).m)
        (projDV (elNF φ y.unop).v ∘ σ.down.1 ∘ θ.unop.1.toOrderHom) ≫ _) =
      ULift.up (toTop.map θ.unop ≫ affineMap (X := k.unop)
        (Y := Henry.SemiSimplexCategory.mk (elNF φ y.unop).m)
        (projDV (elNF φ y.unop).v ∘ σ.down.1) ≫ _)
    rw [toTop_map_eq_affineMap, ← Category.assoc, affineMap_comp]
    rfl

theorem rhoNat_naturality {y z : K.Elementsᵒᵖ} (g : y ⟶ z) :
    (dcylDFunctor φ).map g ≫ rhoNat φ z = rhoNat φ y := by
  ext k σ
  change ULift.up (affineMap (X := k.unop) (Y := Henry.SemiSimplexCategory.mk (elNF φ z.unop).m)
      (projDV (elNF φ z.unop).v ∘ DV.mapV (semiEmb (elFace g.unop))
        (elι φ g.unop).1.toOrderHom ∘ σ.down.1) ≫
      simplexChar (uliftYonedaEquiv.symm (elNF φ z.unop).x)) =
    ULift.up (affineMap (X := k.unop) (Y := Henry.SemiSimplexCategory.mk (elNF φ y.unop).m)
      (projDV (elNF φ y.unop).v ∘ σ.down.1) ≫
      simplexChar (uliftYonedaEquiv.symm (elNF φ y.unop).x))
  have hv := (elι_spec φ g.unop).1
  have key : projDV (elNF φ z.unop).v ∘ DV.mapV (semiEmb (elFace g.unop))
        (elι φ g.unop).1.toOrderHom ∘ σ.down.1 =
      (elι φ g.unop).1.toOrderHom ∘ projDV (elNF φ y.unop).v ∘ σ.down.1 := by
    funext a
    have hmem : σ.down.1 a ∈ Finset.univ.image σ.down.1 := Finset.mem_image_of_mem _ (by simp)
    simp only [Function.comp_apply]
    cases h : σ.down.1 a with
    | top i =>
      simpa [DV.mapV, projDV, semiEmb] using congrFun hv i
    | mid S =>
      have hS : S.Nonempty := σ.down.2.2.1 S (h ▸ hmem)
      have hS' : (S.map (semiEmb (elFace g.unop))).Nonempty := hS.map
      simp only [DV.mapV, projDV, dif_pos hS, dif_pos hS']
      have hmax : (S.map (semiEmb (elFace g.unop))).max' hS' =
          semiEmb (elFace g.unop) (S.max' hS) := by
        simp only [Finset.map_eq_image]
        exact Finset.max'_image (semiEmb_strictMono _).monotone _ _
      rw [hmax]
      simpa [semiEmb] using congrFun hv (S.max' hS)
    | bot c => rfl
  rw [key, ← affineMap_comp, Category.assoc, affineMap_simplexChar_map, (elι_spec φ g.unop).2]

/-- The realization adjunction (left Kan extension along the Yoneda embedding). -/
noncomputable abbrev realAdj :=
  Presheaf.uliftYonedaAdjunction.{u} (stdSimplex.{u}.leftKanExtension toTop.{u})
    (stdSimplex.{u}.leftKanExtensionUnit toTop.{u})

/-- The singular simplices of a space, as a semi-simplicial set. -/
noncomputable abbrev Sing (E : TopCat.{u}) : SemiSSet.{u} :=
  (Presheaf.restrictedULiftYoneda.{u} toTop.{u}).obj E

/-- The unit of the realization adjunction. -/
noncomputable abbrev unitX (X : SemiSSet.{u}) : X ⟶ Sing (realization.obj X) :=
  (realAdj.{u}).unit.app X

theorem realization_map_homEquiv_symm {A B : SemiSSet.{u}} {E : TopCat.{u}} (f : A ⟶ B)
    (g : B ⟶ Sing E) :
    realization.map f ≫ ((realAdj.{u}).homEquiv B E).symm g =
      ((realAdj.{u}).homEquiv A E).symm (f ≫ g) :=
  ((realAdj.{u}).homEquiv_naturality_left_symm f g).symm

theorem homEquiv_symm_unitX (X : SemiSSet.{u}) :
    ((realAdj.{u}).homEquiv X (realization.obj X)).symm (unitX X) = 𝟙 _ := by
  rw [Adjunction.homEquiv_counit]
  exact (realAdj.{u}).left_triangle_components X

/-- The projections of the cylinders over the simplices of `K` to the singular simplices of
`‖X‖`. -/
noncomputable def rhoN : dcylDFunctor φ ⟶ (Functor.const K.Elementsᵒᵖ).obj (Sing (realization.obj X)) where
  app y := rhoNat φ y
  naturality y z g := by
    rw [rhoNat_naturality]
    exact (Category.comp_id _).symm

theorem botN_rhoN :
    botNat φ ≫ rhoN φ = carrierNat φ ≫ (Functor.const K.Elementsᵒᵖ).map (unitX X) := by
  ext y k σ
  change ULift.up (affineMap (X := k.unop)
      (Y := Henry.SemiSimplexCategory.mk (elNF φ y.unop).m)
      (projDV (elNF φ y.unop).v ∘ (fun c => DV.bot c) ∘ σ.down.1.toOrderHom) ≫
      simplexChar (uliftYonedaEquiv.symm (elNF φ y.unop).x)) =
    ((unitX X).app k) ((uliftYonedaEquiv.symm (elNF φ y.unop).x).app k σ)
  have hu := Presheaf.uliftYonedaAdjunction_unit_app_app.{u}
    (stdSimplex.{u}.leftKanExtension toTop.{u}) (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}) X
    (Z := k) (X.map σ.down.op (elNF φ y.unop).x)
  have h := affineMap_simplexChar_map (Y := X) (m' := k.unop.obj.len) σ.down (elNF φ y.unop).x
  exact (congrArg ULift.up h).trans hu.symm

namespace CylDatum

variable {I : Type u} [Category.{0} I] (D : CylDatum X I)

/-- The map of the glued cylinder to the singular simplices of `‖X‖`. -/
noncomputable def toSing (R : D.DC ⟶ (Functor.const I).obj (Sing (realization.obj X)))
    (hR : D.botN ≫ R = D.xN ≫ (Functor.const I).map (unitX X)) :
    D.obj ⟶ Sing (realization.obj X) :=
  pushout.desc (unitX X) (colimit.desc D.DC (Cocone.mk _ R)) (by
    apply colimit.hom_ext
    intro i
    erw [colimit.ι_desc_assoc, ι_colimMap_assoc, colimit.ι_desc]
    exact (congrArg (fun τ => τ.app i) hR).symm)

theorem base_toSing (R : D.DC ⟶ (Functor.const I).obj (Sing (realization.obj X)))
    (hR : D.botN ≫ R = D.xN ≫ (Functor.const I).map (unitX X)) :
    D.base ≫ D.toSing R hR = unitX X :=
  pushout.inl_desc _ _ _

theorem incl_toSing (R : D.DC ⟶ (Functor.const I).obj (Sing (realization.obj X)))
    (hR : D.botN ≫ R = D.xN ≫ (Functor.const I).map (unitX X)) (i : I) :
    colimit.ι D.DC i ≫ D.incl ≫ D.toSing R hR = R.app i := by
  change colimit.ι D.DC i ≫ pushout.inr _ _ ≫ pushout.desc _ _ _ = _
  rw [pushout.inr_desc, colimit.ι_desc]

/-- The projection of the glued cylinder to `‖X‖`, from compatible projections of the cylinders. -/
noncomputable def proj (R : D.DC ⟶ (Functor.const I).obj (Sing (realization.obj X)))
    (hR : D.botN ≫ R = D.xN ≫ (Functor.const I).map (unitX X)) :
    realization.obj D.obj ⟶ realization.obj X :=
  ((realAdj.{u}).homEquiv _ _).symm (D.toSing R hR)

theorem base_proj (R : D.DC ⟶ (Functor.const I).obj (Sing (realization.obj X)))
    (hR : D.botN ≫ R = D.xN ≫ (Functor.const I).map (unitX X)) :
    realization.map D.base ≫ D.proj R hR = 𝟙 _ := by
  unfold proj
  rw [realization_map_homEquiv_symm, base_toSing, homEquiv_symm_unitX]
  rfl

end CylDatum

namespace CylDatum

variable {I : Type u} [Category.{0} I] (D : CylDatum X I)

/-- The map from a semi-simplicial set to a glued cylinder given by maps of its simplices into the
cylinders. -/
noncomputable def topMap {L : SemiSSet.{u}}
    (T : Presheaf.functorToRepresentables.{u} L ⟶ (Functor.const _).obj D.obj) : L ⟶ D.obj :=
  (Presheaf.colimitOfRepresentable.{u} L).desc (Cocone.mk _ T)

theorem ι_topMap {L : SemiSSet.{u}}
    (T : Presheaf.functorToRepresentables.{u} L ⟶ (Functor.const _).obj D.obj)
    (y : L.Elementsᵒᵖ) :
    uliftYonedaEquiv.symm y.unop.val ≫ D.topMap T = T.app y :=
  (Presheaf.colimitOfRepresentable.{u} L).fac _ y

theorem restrictMap_toSing {I' : Type u} [Category.{0} I'] (E : I' ⥤ I)
    (R : D.DC ⟶ (Functor.const I).obj (Sing (realization.obj X)))
    (hR : D.botN ≫ R = D.xN ≫ (Functor.const I).map (unitX X)) :
    D.restrictMap E ≫ D.toSing R hR =
      (D.restrict E).toSing (Functor.whiskerLeft E R) (by
        apply NatTrans.ext
        funext i
        exact congrArg (fun τ => τ.app (E.obj i)) hR) := by
  apply pushout.hom_ext
  · unfold restrictMap toSing pushout.map
    erw [pushout.inl_desc_assoc, Category.id_comp, pushout.inl_desc, pushout.inl_desc]
  · unfold restrictMap toSing pushout.map
    erw [pushout.inr_desc_assoc, Category.assoc, pushout.inr_desc, pushout.inr_desc]
    apply colimit.hom_ext
    intro i
    erw [colimit.ι_pre_assoc, colimit.ι_desc, colimit.ι_desc]
    rfl

end CylDatum

end HomotopyHypothesis.Approximation.Topological
