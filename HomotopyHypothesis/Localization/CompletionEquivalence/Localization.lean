import Mathlib.CategoryTheory.Presentable.OrthogonalReflection
import Mathlib.CategoryTheory.Presentable.Presheaf
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.SmallObject.Basic
import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.Packages.General.CompletionIsSemiModelCategory
import HomotopyHypothesis.Blueprint.Henry.Packages.General.RelHomotopicEquivalence
import HomotopyHypothesis.Blueprint.Henry.Packages.General.WeakEquivalenceCobaseChange
import HomotopyHypothesis.Blueprint.Henry.Packages.General.WeakEquivalenceIff
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Category.SemiModelStructure.CylinderFacts
import HomotopyHypothesis.Category.SemiModelStructure.Factorization
import HomotopyHypothesis.Category.SemiModelStructure.Filtered
import HomotopyHypothesis.Category.SemiModelStructure.Flat
import HomotopyHypothesis.Category.SemiModelStructure.LeftCancel
import HomotopyHypothesis.Category.SemiModelStructure.Transfinite
import HomotopyHypothesis.Category.SemiModelConstruction.RelativeHomotopy
import HomotopyHypothesis.Category.SemiModelConstruction.WeakEquivalences
import HomotopyHypothesis.Category.SemiModelConstruction.YonedaLifting
universe w v u v' u' v₁ u₁ v₂ u₂

open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace HomotopyHypothesis.Localization.CompletionEquivalence

private theorem presheafLocallyPresentable (C : Type w) [SmallCategory C] :
    IsLocallyPresentable.{w} (Cᵒᵖ ⥤ Type w) := by
  infer_instance

private theorem presheafLocallyPresentableEssentiallySmall (C : Type u) [Category.{v} C]
    [EssentiallySmall.{w} C] : IsLocallyPresentable.{w} (Cᵒᵖ ⥤ Type w) := by
  let e := equivSmallModel.{w} C
  let eP := Functor.asEquivalence
    ((Functor.whiskeringLeft Cᵒᵖ (SmallModel C)ᵒᵖ (Type w)).obj e.op.functor)
  have hsmall : IsLocallyPresentable.{w} ((SmallModel C)ᵒᵖ ⥤ Type w) := by
    infer_instance
  exact eP.isLocallyPresentable

private theorem squareEssentiallySmall (C : Type u) [Category.{v} C]
    [EssentiallySmall.{w} C] : EssentiallySmall.{w} (CategoryTheory.Square C) := by
  let e₁ : Arrow C ≌ Arrow (SmallModel C) :=
    Functor.mapArrowEquivalence (equivSmallModel C)
  let e₂ : Arrow (Arrow C) ≌ Arrow (Arrow (SmallModel C)) :=
    Functor.mapArrowEquivalence e₁
  have hsmall : EssentiallySmall.{w} (Arrow (Arrow (SmallModel C))) :=
    essentiallySmall_of_small_of_locallySmall _
  have h₁ : EssentiallySmall.{w} (Arrow (Arrow C)) :=
    (essentiallySmall_congr e₂).2 hsmall
  exact (essentiallySmall_congr (CategoryTheory.Square.arrowArrowEquivalence)).2 h₁

private def initialObjects (C : Type u) [Category.{v} C] : ObjectProperty C :=
  fun X => Nonempty (IsInitial X)

private instance initialObjects_closedUnderIsomorphisms (C : Type u) [Category.{v} C] :
    (initialObjects C).IsClosedUnderIsomorphisms where
  of_iso {X Y} e h := by
    obtain ⟨hX⟩ := h
    exact ⟨hX.ofIso e⟩

private theorem initialObjects_essentiallySmall (C : Type u) [Category.{v} C]
    [EssentiallySmall.{w} C] : ObjectProperty.EssentiallySmall.{w} (initialObjects C) := by
  exact ObjectProperty.EssentiallySmall.of_le (P := initialObjects C) (Q := ⊤)
    (by intro X hX; trivial)

private def completionPushoutSquares (C : Type u) [Category.{v} C]
    [CategoryWithCofibrations C] : ObjectProperty (Square C) :=
  fun s => s.IsPushout ∧ cofibrations C s.f₁₂

private theorem completionPushoutSquares_essentiallySmall (C : Type u) [Category.{v} C]
    [CategoryWithCofibrations C] [EssentiallySmall.{w} C] :
    ObjectProperty.EssentiallySmall.{w} (completionPushoutSquares C) := by
  letI : EssentiallySmall.{w} (Square C) := squareEssentiallySmall C
  exact ObjectProperty.EssentiallySmall.of_le (P := completionPushoutSquares C) (Q := ⊤)
    (by intro s hs; trivial)

private instance initialObjects_fullSubcategory_essentiallySmall (C : Type u)
    [Category.{v} C] [EssentiallySmall.{w} C] :
    EssentiallySmall.{w} ((initialObjects C).FullSubcategory) := by
  letI : ObjectProperty.EssentiallySmall.{w} (initialObjects C) := initialObjects_essentiallySmall C
  infer_instance

private instance completionPushoutSquares_fullSubcategory_essentiallySmall (C : Type u)
    [Category.{v} C] [CategoryWithCofibrations C] [EssentiallySmall.{w} C] :
    EssentiallySmall.{w} ((completionPushoutSquares C).FullSubcategory) := by
  letI : EssentiallySmall.{w} (Square C) := squareEssentiallySmall C
  letI : LocallySmall.{w} (Square C) := inferInstance
  letI : ObjectProperty.EssentiallySmall.{w} (completionPushoutSquares C) :=
    completionPushoutSquares_essentiallySmall C
  infer_instance

private structure SmallRepresentatives {D : Type u} [Category.{v} D]
    (P : ObjectProperty D) where
  index : Type w
  object : index → D
  cover : P = (ObjectProperty.ofObj object).isoClosure

private noncomputable def smallRepresentatives {D : Type u} [Category.{v} D]
    (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
    [ObjectProperty.EssentiallySmall.{w} P] : SmallRepresentatives.{w} P := by
  let h := ObjectProperty.EssentiallySmall.exists_eq_isoClosure_ofObj P
  let ι := Classical.choose h
  let hι := Classical.choose_spec h
  let X := Classical.choose hι
  exact ⟨ι, X, Classical.choose_spec hι⟩

section SmallYoneda

variable (C : Type u) [Category.{v} C] [LocallySmall.{w} C]

private noncomputable def smallYonedaEquivalence :
    (ShrinkHoms C)ᵒᵖ ⥤ Type w ≌ Cᵒᵖ ⥤ Type w := by
  let e := ShrinkHoms.equivalence C
  exact Functor.asEquivalence
    ((Functor.whiskeringLeft Cᵒᵖ (ShrinkHoms C)ᵒᵖ (Type w)).obj e.op.functor)

private noncomputable def smallYoneda : C ⥤ Cᵒᵖ ⥤ Type w :=
  (ShrinkHoms.equivalence C).functor ⋙ yoneda ⋙ (smallYonedaEquivalence C).functor

private noncomputable def smallYonedaEquiv (X : C) (P : Cᵒᵖ ⥤ Type w) :
    ((smallYoneda C).obj X ⟶ P) ≃ P.obj (op X) := by
  let e := ShrinkHoms.equivalence C
  let eP := smallYonedaEquivalence C
  let h := eP.toAdjunction.homEquiv
    (yoneda.obj (e.functor.obj X)) P
  let hy := CategoryTheory.yonedaEquiv (X := e.functor.obj X)
    (F := eP.inverse.obj P)
  let hc := (eP.counitIso.app P).app (op X)
  exact h.trans (hy.trans hc.toEquiv)

private theorem smallYonedaEquiv_map {A B : C} (f : A ⟶ B) (P : Cᵒᵖ ⥤ Type w)
    (g : (smallYoneda C).obj B ⟶ P) :
    smallYonedaEquiv C A P ((smallYoneda C).map f ≫ g) =
      P.map f.op (smallYonedaEquiv C B P g) := by
  let e := ShrinkHoms.equivalence C
  let eP := smallYonedaEquivalence C
  let hc := eP.counitIso.app P
  let f' := e.functor.map f
  let ψ := eP.toAdjunction.homEquiv (yoneda.obj (e.functor.obj B)) P g
  have hAdj := eP.toAdjunction.homEquiv_naturality_left
    (yoneda.map f') g
  change (hc.app (op A)).toEquiv
      (CategoryTheory.yonedaEquiv
        (eP.toAdjunction.homEquiv (yoneda.obj (e.functor.obj A)) P
          (eP.functor.map (yoneda.map f') ≫ g))) =
    P.map f.op ((hc.app (op B)).toEquiv (CategoryTheory.yonedaEquiv ψ))
  rw [hAdj, ← CategoryTheory.yonedaEquiv_naturality ψ f']
  have hn := (hc.hom.naturality f.op)
  change hc.hom.app (op A)
      (((eP.inverse ⋙ eP.functor).obj P).map f.op (CategoryTheory.yonedaEquiv ψ)) =
    P.map f.op (hc.hom.app (op B) (CategoryTheory.yonedaEquiv ψ))
  have hnapp := ConcreteCategory.congr_hom hn (CategoryTheory.yonedaEquiv ψ)
  change hc.hom.app (op A)
      (((eP.inverse ⋙ eP.functor).obj P).map f.op (CategoryTheory.yonedaEquiv ψ)) =
    P.map f.op (hc.hom.app (op B) (CategoryTheory.yonedaEquiv ψ)) at hnapp
  exact hnapp

private theorem smallYonedaEquiv_comp_right (A : C) {P Q : Cᵒᵖ ⥤ Type w}
    (φ : P ⟶ Q) (g : (smallYoneda C).obj A ⟶ P) :
    smallYonedaEquiv C A Q (g ≫ φ) = φ.app (op A) (smallYonedaEquiv C A P g) := by
  let e := ShrinkHoms.equivalence C
  let eP := smallYonedaEquivalence C
  let y := yoneda.obj (e.functor.obj A)
  let ψ := eP.toAdjunction.homEquiv y P g
  have hAdj := eP.toAdjunction.homEquiv_naturality_right g φ
  have hYon : CategoryTheory.yonedaEquiv
      (eP.toAdjunction.homEquiv y Q (g ≫ φ)) =
        (eP.inverse.map φ).app (op (e.functor.obj A)) (CategoryTheory.yonedaEquiv ψ) := by
    rw [hAdj]
    rfl
  change ((eP.counitIso.app Q).app (op A)).toEquiv
      (CategoryTheory.yonedaEquiv (eP.toAdjunction.homEquiv y Q (g ≫ φ))) =
    φ.app (op A) (((eP.counitIso.app P).app (op A)).toEquiv (CategoryTheory.yonedaEquiv ψ))
  rw [hYon]
  have hPoint := congrArg
    (fun t => t.app (op A) (CategoryTheory.yonedaEquiv ψ))
    (eP.counitIso.hom.naturality φ)
  change (eP.counitIso.app Q).hom.app (op A)
      ((eP.inverse.map φ).app (op (e.functor.obj A)) (CategoryTheory.yonedaEquiv ψ)) =
    φ.app (op A) ((eP.counitIso.app P).hom.app (op A) (CategoryTheory.yonedaEquiv ψ)) at hPoint
  change (eP.counitIso.app Q).hom.app (op A)
      ((eP.inverse.map φ).app (op (e.functor.obj A)) (CategoryTheory.yonedaEquiv ψ)) =
    φ.app (op A) ((eP.counitIso.app P).hom.app (op A) (CategoryTheory.yonedaEquiv ψ))
  exact hPoint

end SmallYoneda

section TestMaps

variable (C : Type u) [Category.{v} C] [CategoryWithCofibrations C]
  [LocallySmall.{w} C]

private noncomputable def initialTestFunctor :
    (initialObjects C).FullSubcategory ⥤ Arrow (Cᵒᵖ ⥤ Type w) where
  obj I := Arrow.mk (initial.to ((smallYoneda C).obj I.1))
  map {I J} φ := Arrow.homMk (𝟙 _) ((smallYoneda C).map φ.hom) (by
    apply (initialIsInitial : IsInitial (⊥_ (Cᵒᵖ ⥤ Type w))).hom_ext)
  map_id := by intro I; ext <;> simp
  map_comp := by intro I J K f g; ext <;> simp [Category.assoc]

private noncomputable def completionSquareTestMap (s : Square C) :
    pushout ((smallYoneda C).map s.f₁₂) ((smallYoneda C).map s.f₁₃) ⟶
      (smallYoneda C).obj s.X₄ := by
  let Y := smallYoneda C
  let f := Y.map s.f₁₂
  let g := Y.map s.f₁₃
  let h := Y.map s.f₂₄
  let j := Y.map s.f₃₄
  have comm : f ≫ h = g ≫ j := by
    simpa only [Functor.map_comp] using congrArg Y.map s.fac
  exact pushout.desc h j comm

private noncomputable def completionSquareTestArrow (s : Square C) :
    Arrow (Cᵒᵖ ⥤ Type w) := Arrow.mk (completionSquareTestMap C s)

private theorem completionSquareTestMap_inl (s : Square C) :
    pushout.inl ((smallYoneda C).map s.f₁₂) ((smallYoneda C).map s.f₁₃) ≫
      completionSquareTestMap C s = (smallYoneda C).map s.f₂₄ := by
  change pushout.inl _ _ ≫ pushout.desc _ _ _ = _
  exact pushout.inl_desc _ _ _

private theorem completionSquareTestMap_inr (s : Square C) :
    pushout.inr ((smallYoneda C).map s.f₁₂) ((smallYoneda C).map s.f₁₃) ≫
      completionSquareTestMap C s = (smallYoneda C).map s.f₃₄ := by
  change pushout.inr _ _ ≫ pushout.desc _ _ _ = _
  exact pushout.inr_desc _ _ _

private theorem completionSquareTestMap_inl_assoc (s : Square C)
    {Z : Cᵒᵖ ⥤ Type w} (g : (smallYoneda C).obj s.X₄ ⟶ Z) :
    pushout.inl ((smallYoneda C).map s.f₁₂) ((smallYoneda C).map s.f₁₃) ≫
      completionSquareTestMap C s ≫ g = (smallYoneda C).map s.f₂₄ ≫ g := by
  rw [← Category.assoc, completionSquareTestMap_inl]

private theorem completionSquareTestMap_inr_assoc (s : Square C)
    {Z : Cᵒᵖ ⥤ Type w} (g : (smallYoneda C).obj s.X₄ ⟶ Z) :
    pushout.inr ((smallYoneda C).map s.f₁₂) ((smallYoneda C).map s.f₁₃) ≫
      completionSquareTestMap C s ≫ g = (smallYoneda C).map s.f₃₄ ≫ g := by
  rw [← Category.assoc, completionSquareTestMap_inr]

private noncomputable def completionSquareTestFunctor :
    Square C ⥤ Arrow (Cᵒᵖ ⥤ Type w) where
  obj := completionSquareTestArrow C
  map {s t} φ := by
    let Y := smallYoneda C
    let i₁ := Y.map φ.τ₂
    let i₂ := Y.map φ.τ₃
    let i₃ := Y.map φ.τ₁
    let h₁ : Y.map s.f₁₂ ≫ i₁ = i₃ ≫ Y.map t.f₁₂ := by
      simpa only [Functor.map_comp, Functor.map_id] using congrArg Y.map φ.comm₁₂
    let h₂ : Y.map s.f₁₃ ≫ i₂ = i₃ ≫ Y.map t.f₁₃ := by
      simpa only [Functor.map_comp, Functor.map_id] using congrArg Y.map φ.comm₁₃
    exact Arrow.homMk
      (pushout.map (Y.map s.f₁₂) (Y.map s.f₁₃) (Y.map t.f₁₂) (Y.map t.f₁₃)
        i₁ i₂ i₃ h₁ h₂)
      (Y.map φ.τ₄) (by
        apply pushout.hom_ext
        · change pushout.inl _ _ ≫
            pushout.map _ _ _ _ i₁ i₂ i₃ h₁ h₂ ≫ completionSquareTestMap C t =
              pushout.inl _ _ ≫ completionSquareTestMap C s ≫ Y.map φ.τ₄
          rw [pushout.map, pushout.inl_desc_assoc]
          conv_lhs => rw [Category.assoc]
          rw [completionSquareTestMap_inl, completionSquareTestMap_inl_assoc]
          simpa only [Functor.map_comp] using congrArg Y.map φ.comm₂₄.symm
        · change pushout.inr _ _ ≫
            pushout.map _ _ _ _ i₁ i₂ i₃ h₁ h₂ ≫ completionSquareTestMap C t =
              pushout.inr _ _ ≫ completionSquareTestMap C s ≫ Y.map φ.τ₄
          rw [pushout.map, pushout.inr_desc_assoc]
          conv_lhs => rw [Category.assoc]
          rw [completionSquareTestMap_inr, completionSquareTestMap_inr_assoc]
          simpa only [Functor.map_comp] using congrArg Y.map φ.comm₃₄.symm)
  map_id := by
    intro s
    let Y := smallYoneda C
    apply Arrow.hom_ext
    · have h₁ : Y.map s.f₁₂ ≫ Y.map (𝟙 s.X₂) =
          Y.map (𝟙 s.X₁) ≫ Y.map s.f₁₂ := by simp
      have h₂ : Y.map s.f₁₃ ≫ Y.map (𝟙 s.X₃) =
          Y.map (𝟙 s.X₁) ≫ Y.map s.f₁₃ := by simp
      change pushout.map (Y.map s.f₁₂) (Y.map s.f₁₃) (Y.map s.f₁₂) (Y.map s.f₁₃)
        (Y.map (𝟙 s.X₂)) (Y.map (𝟙 s.X₃)) (Y.map (𝟙 s.X₁)) h₁ h₂ = 𝟙 _
      simpa using (pushout.map_id (f := Y.map s.f₁₂) (g := Y.map s.f₁₃))
    · change Y.map (𝟙 s.X₄) = 𝟙 _
      exact Y.map_id _
  map_comp := by
    intro s t r f g
    let Y := smallYoneda C
    apply Arrow.hom_ext
    · let h₁ : Y.map s.f₁₂ ≫ Y.map f.τ₂ = Y.map f.τ₁ ≫ Y.map t.f₁₂ := by
        simpa only [Functor.map_comp] using congrArg Y.map f.comm₁₂
      let h₂ : Y.map s.f₁₃ ≫ Y.map f.τ₃ = Y.map f.τ₁ ≫ Y.map t.f₁₃ := by
        simpa only [Functor.map_comp] using congrArg Y.map f.comm₁₃
      let h₃ : Y.map t.f₁₂ ≫ Y.map g.τ₂ = Y.map g.τ₁ ≫ Y.map r.f₁₂ := by
        simpa only [Functor.map_comp] using congrArg Y.map g.comm₁₂
      let h₄ : Y.map t.f₁₃ ≫ Y.map g.τ₃ = Y.map g.τ₁ ≫ Y.map r.f₁₃ := by
        simpa only [Functor.map_comp] using congrArg Y.map g.comm₁₃
      let h₅ : Y.map s.f₁₂ ≫ Y.map (f.τ₂ ≫ g.τ₂) =
          Y.map (f.τ₁ ≫ g.τ₁) ≫ Y.map r.f₁₂ := by
        have h₅' : s.f₁₂ ≫ (f.τ₂ ≫ g.τ₂) = (f.τ₁ ≫ g.τ₁) ≫ r.f₁₂ := by
          change s.f₁₂ ≫ (f ≫ g).τ₂ = (f ≫ g).τ₁ ≫ r.f₁₂
          exact (f ≫ g).comm₁₂
        simpa only [Functor.map_comp] using congrArg Y.map h₅'
      let h₆ : Y.map s.f₁₃ ≫ Y.map (f.τ₃ ≫ g.τ₃) =
          Y.map (f.τ₁ ≫ g.τ₁) ≫ Y.map r.f₁₃ := by
        have h₆' : s.f₁₃ ≫ (f.τ₃ ≫ g.τ₃) = (f.τ₁ ≫ g.τ₁) ≫ r.f₁₃ := by
          change s.f₁₃ ≫ (f ≫ g).τ₃ = (f ≫ g).τ₁ ≫ r.f₁₃
          exact (f ≫ g).comm₁₃
        simpa only [Functor.map_comp] using congrArg Y.map h₆'
      change pushout.map (Y.map s.f₁₂) (Y.map s.f₁₃) (Y.map r.f₁₂) (Y.map r.f₁₃)
          (Y.map (f.τ₂ ≫ g.τ₂)) (Y.map (f.τ₃ ≫ g.τ₃)) (Y.map (f.τ₁ ≫ g.τ₁)) h₅ h₆ =
        pushout.map (Y.map s.f₁₂) (Y.map s.f₁₃) (Y.map t.f₁₂) (Y.map t.f₁₃)
          (Y.map f.τ₂) (Y.map f.τ₃) (Y.map f.τ₁) h₁ h₂ ≫
        pushout.map (Y.map t.f₁₂) (Y.map t.f₁₃) (Y.map r.f₁₂) (Y.map r.f₁₃)
          (Y.map g.τ₂) (Y.map g.τ₃) (Y.map g.τ₁) h₃ h₄
      simpa only [Functor.map_comp] using
        (pushout.map_comp (Y.map f.τ₁) (Y.map g.τ₁) (Y.map f.τ₂) (Y.map g.τ₂)
          (Y.map f.τ₃) (Y.map g.τ₃) h₁ h₂ h₃ h₄).symm
    · exact Y.map_comp _ _

private noncomputable def initialTestSmallFunctor (C : Type u) [Category.{v} C]
    [CategoryWithCofibrations C] [LocallySmall.{w} C] [EssentiallySmall.{w} C] :
    SmallModel.{w} ((initialObjects C).FullSubcategory) ⥤ Arrow (Cᵒᵖ ⥤ Type w) := by
  exact (equivSmallModel.{w} ((initialObjects C).FullSubcategory)).inverse ⋙ initialTestFunctor C

private noncomputable def squareTestSmallFunctor (C : Type u) [Category.{v} C]
    [CategoryWithCofibrations C] [LocallySmall.{w} C] [EssentiallySmall.{w} C] :
    SmallModel.{w} ((completionPushoutSquares C).FullSubcategory) ⥤ Arrow (Cᵒᵖ ⥤ Type w) := by
  exact (equivSmallModel.{w} ((completionPushoutSquares C).FullSubcategory)).inverse ⋙
    (completionPushoutSquares C).ι ⋙ completionSquareTestFunctor C

private noncomputable def completionTestArrows (C : Type u) [Category.{v} C]
    [CategoryWithCofibrations C] [LocallySmall.{w} C] [EssentiallySmall.{w} C] :
    Sum (SmallModel.{w} ((initialObjects C).FullSubcategory))
      (SmallModel.{w} ((completionPushoutSquares C).FullSubcategory)) → Arrow (Cᵒᵖ ⥤ Type w) :=
  Sum.elim (initialTestSmallFunctor C).obj (squareTestSmallFunctor C).obj

private instance completionTestArrows_small (C : Type u) [Category.{v} C]
    [CategoryWithCofibrations C] [LocallySmall.{w} C] [EssentiallySmall.{w} C] :
    Small.{w} (Sum (SmallModel.{w} ((initialObjects C).FullSubcategory))
      (SmallModel.{w} ((completionPushoutSquares C).FullSubcategory))) := by
  infer_instance

private noncomputable def completionTestProperty (C : Type u) [Category.{v} C]
    [CategoryWithCofibrations C] [LocallySmall.{w} C] [EssentiallySmall.{w} C] :
    MorphismProperty (Cᵒᵖ ⥤ Type w) :=
  MorphismProperty.ofHoms (fun i => (completionTestArrows C i).hom)

private instance completionTestProperty_small (C : Type u) [Category.{v} C]
    [CategoryWithCofibrations C] [LocallySmall.{w} C] [EssentiallySmall.{w} C] :
    MorphismProperty.IsSmall.{w} (completionTestProperty C) := by
  unfold completionTestProperty
  infer_instance

private noncomputable def pushoutHomEquiv {A B X : C} (i : A ⟶ B) (j : A ⟶ X)
    (P : Cᵒᵖ ⥤ Type w) :
    (pushout ((smallYoneda C).map i) ((smallYoneda C).map j) ⟶ P) ≃
      {p : ((smallYoneda C).obj B ⟶ P) × ((smallYoneda C).obj X ⟶ P) //
        (smallYoneda C).map i ≫ p.1 = (smallYoneda C).map j ≫ p.2} where
  toFun g :=
    ⟨⟨pushout.inl _ _ ≫ g, pushout.inr _ _ ≫ g⟩, by
      calc
        (smallYoneda C).map i ≫ (pushout.inl _ _ ≫ g) =
            ((smallYoneda C).map i ≫ pushout.inl _ _) ≫ g := by simp [Category.assoc]
        _ = ((smallYoneda C).map j ≫ pushout.inr _ _) ≫ g := by rw [pushout.condition]
        _ = (smallYoneda C).map j ≫ (pushout.inr _ _ ≫ g) := by simp [Category.assoc]⟩
  invFun p := pushout.desc p.1.1 p.1.2 p.2
  left_inv g := by
    apply pushout.hom_ext
    · exact pushout.inl_desc _ _ _
    · exact pushout.inr_desc _ _ _
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact pushout.inl_desc _ _ _
    · exact pushout.inr_desc _ _ _

private noncomputable def pushoutHomElementsEquiv (s : Square C)
    (P : Cᵒᵖ ⥤ Type w) :
    {p : ((smallYoneda C).obj s.X₂ ⟶ P) × ((smallYoneda C).obj s.X₃ ⟶ P) //
        (smallYoneda C).map s.f₁₂ ≫ p.1 = (smallYoneda C).map s.f₁₃ ≫ p.2} ≃
      Types.PullbackObj (P.map s.f₁₂.op) (P.map s.f₁₃.op) where
  toFun p :=
    ⟨⟨smallYonedaEquiv C s.X₂ P p.1.1, smallYonedaEquiv C s.X₃ P p.1.2⟩, by
      have h := congrArg (smallYonedaEquiv C s.X₁ P) p.2
      simpa only [smallYonedaEquiv_map] using h⟩
  invFun q :=
    ⟨⟨(smallYonedaEquiv C s.X₂ P).symm q.1.1,
      (smallYonedaEquiv C s.X₃ P).symm q.1.2⟩, by
      apply (smallYonedaEquiv C s.X₁ P).injective
      simpa only [smallYonedaEquiv_map, Equiv.apply_symm_apply] using q.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> simp
  right_inv q := by
    apply Subtype.ext
    apply Prod.ext <;> simp

private theorem bijective_conjugate_iff {α β γ δ : Type*} (e₁ : α ≃ β) (e₂ : γ ≃ δ)
    (f : α → γ) : Function.Bijective f ↔ Function.Bijective (fun b => e₂ (f (e₁.symm b))) := by
  constructor
  · rintro ⟨hinj, hsurj⟩
    constructor
    · intro b₁ b₂ h
      apply e₁.symm.injective
      apply hinj
      apply e₂.injective
      simpa using h
    · intro d
      obtain ⟨c, hc⟩ := hsurj (e₂.symm d)
      refine ⟨e₁ c, ?_⟩
      simp [hc]
  · rintro ⟨hinj, hsurj⟩
    constructor
    · intro a₁ a₂ h
      apply e₁.injective
      apply hinj
      simpa using congrArg e₂ h
    · intro c
      obtain ⟨b, hb⟩ := hsurj (e₂ c)
      refine ⟨e₁.symm b, ?_⟩
      apply e₂.injective
      simpa using hb

private theorem completionSquareTest_isLocal_iff (s : Square C) (P : Cᵒᵖ ⥤ Type w) :
    Function.Bijective (fun g : (smallYoneda C).obj s.X₄ ⟶ P =>
      completionSquareTestMap C s ≫ g) ↔
    IsPullback (P.map s.f₂₄.op) (P.map s.f₃₄.op) (P.map s.f₁₂.op) (P.map s.f₁₃.op) := by
  let e₄ := smallYonedaEquiv C s.X₄ P
  let ePush := (pushoutHomEquiv C s.f₁₂ s.f₁₃ P).trans
    (pushoutHomElementsEquiv C s P)
  let pre : ((smallYoneda C).obj s.X₄ ⟶ P) →
      (pushout ((smallYoneda C).map s.f₁₂) ((smallYoneda C).map s.f₁₃) ⟶ P) :=
    fun g => completionSquareTestMap C s ≫ g
  let c : PullbackCone (P.map s.f₁₂.op) (P.map s.f₁₃.op) :=
    PullbackCone.mk (P.map s.f₂₄.op) (P.map s.f₃₄.op) (by
      simpa only [op_comp, Functor.map_comp] using
        congrArg (fun f => P.map f.op) s.fac)
  have hConj : Function.Bijective pre ↔
      Function.Bijective (fun x => ePush (pre (e₄.symm x))) :=
    bijective_conjugate_iff e₄ ePush pre
  have hMap : (fun x => ePush (pre (e₄.symm x))) = c.toPullbackObj := by
    funext x
    apply Subtype.ext
    apply Prod.ext
    · simp [ePush, pre, pushoutHomEquiv, pushoutHomElementsEquiv,
        completionSquareTestMap_inl_assoc, smallYonedaEquiv_map, e₄, c,
        PullbackCone.toPullbackObj]
      rfl
    · simp [ePush, pre, pushoutHomEquiv, pushoutHomElementsEquiv,
        completionSquareTestMap_inr_assoc, smallYonedaEquiv_map, e₄, c,
        PullbackCone.toPullbackObj]
      rfl
  have hPullback : IsPullback (P.map s.f₂₄.op) (P.map s.f₃₄.op)
      (P.map s.f₁₂.op) (P.map s.f₁₃.op) ↔ Function.Bijective c.toPullbackObj := by
    constructor
    · intro h
      exact (PullbackCone.isLimitEquivBijective c) h.isLimit
    · intro h
      exact IsPullback.of_isLimit ((PullbackCone.isLimitEquivBijective c).symm h)
  exact hConj.trans (by rw [hMap]; exact hPullback.symm)

private theorem initialTest_isLocal_iff (I : (initialObjects C).FullSubcategory)
    (P : Cᵒᵖ ⥤ Type w) :
    Function.Bijective (fun g : (smallYoneda C).obj I.1 ⟶ P =>
      initial.to ((smallYoneda C).obj I.1) ≫ g) ↔
      Nonempty (Unique (P.obj (op I.1))) := by
  let R := (smallYoneda C).obj I.1
  let e := smallYonedaEquiv C I.1 P
  let Z₀ := (⊥_ (Cᵒᵖ ⥤ Type w))
  let hZ₀ : IsInitial Z₀ := initialIsInitial
  let f₀ : Z₀ ⟶ R := initial.to R
  let q : Z₀ ⟶ P := hZ₀.to P
  have hQ : Unique (Z₀ ⟶ P) := ⟨⟨q⟩, fun h => hZ₀.hom_ext _ _⟩
  change Function.Bijective (fun g : R ⟶ P => f₀ ≫ g) ↔ _
  constructor
  · intro hb
    have hne : Nonempty (R ⟶ P) := by
      obtain ⟨g, _⟩ := hb.2 q
      exact ⟨g⟩
    have hsub : Subsingleton (R ⟶ P) := ⟨fun g₁ g₂ => hb.1
      ((hQ.uniq (f₀ ≫ g₁)).trans (hQ.uniq (f₀ ≫ g₂)).symm)⟩
    let hHom : Unique (R ⟶ P) :=
      ⟨⟨Classical.choice hne⟩, fun g => hsub.elim g _⟩
    let hP : Unique (P.obj (op I.1)) :=
      ⟨⟨e hHom.default⟩, fun x => by
        simpa using congrArg e (hHom.uniq (e.symm x))⟩
    exact ⟨hP⟩
  · rintro ⟨hP⟩
    let hHom : Unique (R ⟶ P) :=
      ⟨⟨e.symm hP.default⟩, fun g => e.injective
        ((hP.uniq (e g)).trans (Equiv.apply_symm_apply e hP.default).symm)⟩
    constructor
    · intro g₁ g₂ _
      exact (hHom.uniq g₁).trans (hHom.uniq g₂).symm
    · intro g
      refine ⟨hHom.default, ?_⟩
      exact (hQ.uniq (f₀ ≫ hHom.default)).trans (hQ.uniq g).symm

private def targetObjects (P : Cᵒᵖ ⥤ Type w) : ObjectProperty (Cᵒᵖ ⥤ Type w) :=
  ObjectProperty.singleton P

private def targetIsoLocal (P : Cᵒᵖ ⥤ Type w) : MorphismProperty (Cᵒᵖ ⥤ Type w) :=
  (targetObjects C P).isoClosure.isLocal

private theorem targetIsoLocal_iff (P : Cᵒᵖ ⥤ Type w) {X Y : Cᵒᵖ ⥤ Type w}
    (f : X ⟶ Y) : targetIsoLocal C P f ↔ Function.Bijective (fun g : Y ⟶ P => f ≫ g) := by
  change ((targetObjects C P).isoClosure.isLocal f) ↔ _
  rw [ObjectProperty.isoClosure_isLocal]
  change (targetObjects C P).isLocal f ↔ _
  constructor
  · intro h
    exact h P (by simp [targetObjects])
  · intro h Z hZ
    have hEq : P = Z := (ObjectProperty.singleton_iff P Z).mp hZ
    subst Z
    exact h

private theorem targetIsoLocal_arrowIso (P : Cᵒᵖ ⥤ Type w) {X Y X' Y' : Cᵒᵖ ⥤ Type w}
    {f : X ⟶ Y} {g : X' ⟶ Y'} (e : Arrow.mk f ≅ Arrow.mk g) :
    targetIsoLocal C P f ↔ targetIsoLocal C P g :=
  MorphismProperty.arrow_mk_iso_iff ((targetObjects C P).isoClosure.isLocal) e

private theorem completionTestProperty_local_iff (C : Type u) [Category.{v} C]
    [CategoryWithCofibrations C] [LocallySmall.{w} C] [EssentiallySmall.{w} C]
    (P : Cᵒᵖ ⥤ Type w) :
    (completionTestProperty C).isLocal P ↔
      ∀ i, targetIsoLocal C P (completionTestArrows C i).hom := by
  rw [MorphismProperty.isLocal_iff]
  constructor
  · intro h i
    apply (targetIsoLocal_iff C P (completionTestArrows C i).hom).2
    exact h (completionTestArrows C i).hom ⟨i⟩
  · intro h X Y f hf
    rcases hf with ⟨i⟩
    exact (targetIsoLocal_iff C P (completionTestArrows C i).hom).1 (h i)

private theorem completionPresheaf_iff_testLocal (C : Type u) [Category.{v} C]
    [CategoryWithCofibrations C] [EssentiallySmall.{w} C] (P : Cᵒᵖ ⥤ Type w) :
    HomotopyHypothesis.Henry.IsCompletionPresheaf.{w} C P ↔
      (completionTestProperty C).isLocal P := by
  letI : LocallySmall.{w} C := inferInstance
  constructor
  · intro h
    apply (completionTestProperty_local_iff C P).2
    intro i
    cases i with
    | inl i =>
        let I := (equivSmallModel.{w} ((initialObjects C).FullSubcategory)).inverse.obj i
        have hI : IsInitial I.1 := Classical.choice I.2
        apply (targetIsoLocal_iff C P ((initialTestFunctor C).obj I).hom).2
        exact (initialTest_isLocal_iff C I P).2 (h.1 hI)
    | inr i =>
        let S := (equivSmallModel.{w} ((completionPushoutSquares C).FullSubcategory)).inverse.obj i
        apply (targetIsoLocal_iff C P
          ((completionSquareTestFunctor C).obj S.1).hom).2
        exact (completionSquareTest_isLocal_iff C S.1 P).2
          (h.2 S.1.f₁₂ S.1.f₁₃ S.1.f₂₄ S.1.f₃₄ S.2.1 S.2.2)
  · intro h
    apply (completionTestProperty_local_iff C P).1 at h
    constructor
    · intro I hI
      let obj : (initialObjects C).FullSubcategory := ⟨I, ⟨hI⟩⟩
      let e := equivSmallModel.{w} ((initialObjects C).FullSubcategory)
      let i := e.functor.obj obj
      let rep := e.inverse.obj i
      let eObj : obj ≅ rep := e.unitIso.app obj
      let eTest := (initialTestFunctor C).mapIso eObj
      have hRep := h (Sum.inl i)
      have hI' : targetIsoLocal C P ((initialTestFunctor C).obj obj).hom :=
        (targetIsoLocal_arrowIso C P eTest).mpr hRep
      exact (initialTest_isLocal_iff C obj P).1
        ((targetIsoLocal_iff C P ((initialTestFunctor C).obj obj).hom).1 hI')
    · intro A B X Q i f k j hPO hcof
      let sq : Square C := ⟨i, f, k, j, hPO.w⟩
      let obj : (completionPushoutSquares C).FullSubcategory := ⟨sq, ⟨hPO, hcof⟩⟩
      let e := equivSmallModel.{w} ((completionPushoutSquares C).FullSubcategory)
      let idx := e.functor.obj obj
      let rep := e.inverse.obj idx
      let eObj : obj ≅ rep := e.unitIso.app obj
      let eSq : sq ≅ rep.1 := ((completionPushoutSquares C).ι.mapIso eObj)
      let eTest := (completionSquareTestFunctor C).mapIso eSq
      have hRep := h (Sum.inr idx)
      have hSq : targetIsoLocal C P ((completionSquareTestFunctor C).obj sq).hom :=
        (targetIsoLocal_arrowIso C P eTest).mpr hRep
      exact (completionSquareTest_isLocal_iff C sq P).1
        ((targetIsoLocal_iff C P ((completionSquareTestFunctor C).obj sq).hom).1 hSq)

private theorem completionProperty_eq_testLocal (C : Type u) [Category.{v} C]
    [CategoryWithCofibrations C] [EssentiallySmall.{w} C] :
    HomotopyHypothesis.Henry.IsCompletionPresheaf.{w} C = (completionTestProperty C).isLocal := by
  funext P
  exact propext (completionPresheaf_iff_testLocal C P)

private noncomputable def fullSubcategoryEquivOfEq {E : Type u'} [Category.{v'} E]
    {P Q : ObjectProperty E} (h : P = Q) : P.FullSubcategory ≌ Q.FullSubcategory := by
  let hPQ : P ≤ Q := fun X hX => h ▸ hX
  let F := ObjectProperty.ιOfLE hPQ
  have hess : Q ≤ P.isoClosure := by
    intro X hX
    have hX' : P X := by rw [h]; exact hX
    exact ⟨X, hX', ⟨Iso.refl X⟩⟩
  haveI : F.IsEquivalence := (ObjectProperty.isEquivalence_ιOfLE_iff hPQ).2 hess
  exact Functor.asEquivalence F

private theorem completionTestInclusion_isRightAdjoint (C : Type u) [Category.{v} C]
    [CategoryWithCofibrations C] [EssentiallySmall.{w} C] :
    (ObjectProperty.ι (completionTestProperty C).isLocal).IsRightAdjoint := by
  letI : LocallySmall.{w} C := inferInstance
  letI : IsLocallyPresentable.{w} (Cᵒᵖ ⥤ Type w) :=
    presheafLocallyPresentableEssentiallySmall C
  obtain ⟨κ₀, hκ₀, hLocPres⟩ :=
    IsLocallyPresentable.exists_cardinal.{w} (Cᵒᵖ ⥤ Type w)
  letI : Fact κ₀.IsRegular := hκ₀
  letI : IsCardinalLocallyPresentable (Cᵒᵖ ⥤ Type w) κ₀ := hLocPres
  let T := completionTestArrows C
  let endpoints : ObjectProperty (Cᵒᵖ ⥤ Type w) :=
    ObjectProperty.ofObj (fun i => (T i).left) ⊔ ObjectProperty.ofObj (fun i => (T i).right)
  obtain ⟨κ₁, hκ₁, hEndpoints₁⟩ := ObjectProperty.le_isCardinalPresentable endpoints
  let κ := κ₀ ⊔ κ₁
  let hκ : Fact κ.IsRegular := ⟨iteInduction (fun _ ↦ Fact.out) (fun _ ↦ Fact.out)⟩
  letI := hκ
  letI : IsCardinalLocallyPresentable (Cᵒᵖ ⥤ Type w) κ :=
    IsCardinalLocallyPresentable.of_le (Cᵒᵖ ⥤ Type w) (by dsimp [κ]; exact le_sup_left)
  have hEndpoints : endpoints ≤ isCardinalPresentable (Cᵒᵖ ⥤ Type w) κ :=
    hEndpoints₁.trans <| isCardinalPresentable_monotone _ (by dsimp [κ]; exact le_sup_right)
  have hW : ∀ ⦃X Y : Cᵒᵖ ⥤ Type w⦄ (f : X ⟶ Y), completionTestProperty C f →
      IsCardinalPresentable X κ ∧ IsCardinalPresentable Y κ := by
    intro X Y f hf
    rcases hf with ⟨i⟩
    have hX : endpoints (completionTestArrows C i).left := by
      change ObjectProperty.ofObj (fun j => (T j).left) (T i).left ∨ _
      exact Or.inl (ObjectProperty.ofObj_apply (fun j => (T j).left) i)
    have hY : endpoints (completionTestArrows C i).right := by
      change _ ∨ ObjectProperty.ofObj (fun j => (T j).right) (T i).right
      exact Or.inr (ObjectProperty.ofObj_apply (fun j => (T j).right) i)
    exact ⟨hEndpoints _ hX, hEndpoints _ hY⟩
  exact MorphismProperty.isRightAdjoint_ι_isLocal (completionTestProperty C) κ hW

end TestMaps

section CompletionRestrictionAdjunction

variable {C : Type u₁} [Category.{v₁} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C]
  {D : Type u₂} [Category.{v₂} D] [CategoryWithCofibrations D]
  [CategoryWithWeakEquivalences D]

theorem completionRestriction_isRightAdjoint_proof [EssentiallySmall.{w} C]
    [EssentiallySmall.{w} D] {F : C ⥤ D}
    (hF : HomotopyHypothesis.Henry.IsCofibrationMorphism F) :
    (HomotopyHypothesis.Henry.Completion.restriction.{w} F hF).IsRightAdjoint := by
  let W_D := completionTestProperty D
  let P_D := HomotopyHypothesis.Henry.IsCompletionPresheaf.{w} D
  let hPropD := completionProperty_eq_testLocal D
  let hPQ : P_D ≤ W_D.isLocal := fun X hX => hPropD ▸ hX
  have hEss : W_D.isLocal ≤ ObjectProperty.isoClosure P_D := by
    intro X hX
    have hPX : HomotopyHypothesis.Henry.IsCompletionPresheaf.{w} D X := by
      rw [hPropD]
      exact hX
    exact ⟨X, hPX, ⟨Iso.refl X⟩⟩
  haveI : (ObjectProperty.ιOfLE hPQ).IsEquivalence :=
    (ObjectProperty.isEquivalence_ιOfLE_iff hPQ).2 hEss
  let e_D : HomotopyHypothesis.Henry.Completion.{w} D ≌ W_D.isLocal.FullSubcategory :=
    Functor.asEquivalence (ObjectProperty.ιOfLE hPQ)
  let ι_W := ObjectProperty.ι W_D.isLocal
  let ι_C := ObjectProperty.ι (HomotopyHypothesis.Henry.IsCompletionPresheaf.{w} C)
  let ι_D := ObjectProperty.ι (HomotopyHypothesis.Henry.IsCompletionPresheaf.{w} D)
  letI : ι_W.IsRightAdjoint := completionTestInclusion_isRightAdjoint D
  let adj_W := Adjunction.ofIsRightAdjoint ι_W
  let adj_e := e_D.symm.toAdjunction
  let adj_reflect := adj_W.comp adj_e
  let reflectD := ι_W.leftAdjoint ⋙ e_D.symm.functor
  letI : ∀ (G : Cᵒᵖ ⥤ Type w), F.op.HasLeftKanExtension G := by
    intro G
    have hPointwise : F.op.HasPointwiseLeftKanExtension G := by
      intro Y
      letI : HasColimitsOfShape (CostructuredArrow F.op Y) (Type w) :=
        Limits.hasColimitsOfShape_of_essentiallySmall (CostructuredArrow F.op Y) (Type w)
      infer_instance
    letI : F.op.HasPointwiseLeftKanExtension G := hPointwise
    infer_instance
  let L₀ := F.op.lan ⋙ reflectD
  let R₀ := e_D.functor ⋙ ι_W ⋙
    (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj F.op
  let L := ι_C ⋙ L₀
  let R := HomotopyHypothesis.Henry.Completion.restriction.{w} F hF
  let rawRestr := (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj F.op
  let adj_lan := F.op.lanAdjunction (Type w)
  let adj₀ := adj_lan.comp adj_reflect
  let commIncl : e_D.functor ⋙ ι_W ≅ ι_D :=
    ObjectProperty.ιOfLECompιIso hPQ
  have commRestr : R ⋙ ι_C ≅ ι_D ⋙ rawRestr := by
    dsimp [R, HomotopyHypothesis.Henry.Completion.restriction, rawRestr]
    exact ObjectProperty.liftCompιIso _ _ _
  let comm₁ : ι_C ⋙ L₀ ≅ L ⋙ 𝟭 _ :=
    (Functor.rightUnitor (ι_C ⋙ L₀)).symm
  let comm₂ : (𝟭 _ : HomotopyHypothesis.Henry.Completion.{w} D ⥤ _ ) ⋙ R₀ ≅
      R ⋙ ι_C :=
    Functor.leftUnitor R₀ ≪≫ Functor.isoWhiskerRight commIncl rawRestr ≪≫ commRestr.symm
  have hιC : ι_C.FullyFaithful := by
    dsimp [ι_C]
    exact ObjectProperty.fullyFaithfulι _
  have hιD : (𝟭 (HomotopyHypothesis.Henry.Completion.{w} D)).FullyFaithful :=
    Functor.FullyFaithful.id _
  let adj := adj₀.restrictFullyFaithful hιC hιD comm₁ comm₂
  exact ⟨L, ⟨adj⟩⟩

end CompletionRestrictionAdjunction

section CompletionRestrictionQuillen

open HomotopyHypothesis.Henry

variable {C : Type u₁} [Category.{v₁} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HomotopyHypothesis.Henry.IsCylinderCategory C]
  {D : Type u₂} [Category.{v₂} D] [CategoryWithCofibrations D]
  [CategoryWithWeakEquivalences D] [HomotopyHypothesis.Henry.IsCylinderCategory D]
  [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]

private theorem completionLocallyPresentable :
    IsLocallyPresentable.{w} (HomotopyHypothesis.Henry.Completion.{w} C) := by
  letI : LocallySmall.{w} C := inferInstance
  letI : IsLocallyPresentable.{w} (Cᵒᵖ ⥤ Type w) :=
    presheafLocallyPresentableEssentiallySmall C
  obtain ⟨κ₀, hκ₀, hLocPres⟩ := IsLocallyPresentable.exists_cardinal.{w} (Cᵒᵖ ⥤ Type w)
  letI : Fact κ₀.IsRegular := hκ₀
  letI : IsCardinalLocallyPresentable (Cᵒᵖ ⥤ Type w) κ₀ := hLocPres
  let W := completionTestProperty C
  let T := completionTestArrows C
  let endpoints : ObjectProperty (Cᵒᵖ ⥤ Type w) :=
    ObjectProperty.ofObj (fun i => (T i).left) ⊔ ObjectProperty.ofObj (fun i => (T i).right)
  obtain ⟨κ₁, hκ₁, hEndpoints₁⟩ := ObjectProperty.le_isCardinalPresentable endpoints
  let κ := κ₀ ⊔ κ₁
  let hκ : Fact κ.IsRegular := ⟨iteInduction (fun _ ↦ Fact.out) (fun _ ↦ Fact.out)⟩
  letI := hκ
  letI : IsCardinalLocallyPresentable (Cᵒᵖ ⥤ Type w) κ :=
    IsCardinalLocallyPresentable.of_le (Cᵒᵖ ⥤ Type w) (by dsimp [κ]; exact le_sup_left)
  have hEndpoints : endpoints ≤ isCardinalPresentable (Cᵒᵖ ⥤ Type w) κ :=
    hEndpoints₁.trans <| isCardinalPresentable_monotone _ (by dsimp [κ]; exact le_sup_right)
  have hW : ∀ ⦃X Y : Cᵒᵖ ⥤ Type w⦄ (f : X ⟶ Y), completionTestProperty C f →
      IsCardinalPresentable X κ ∧ IsCardinalPresentable Y κ := by
    intro X Y f hf
    rcases hf with ⟨i⟩
    have hX : endpoints (completionTestArrows C i).left := by
      change ObjectProperty.ofObj (fun j => (T j).left) (T i).left ∨ _
      exact Or.inl (ObjectProperty.ofObj_apply (fun j => (T j).left) i)
    have hY : endpoints (completionTestArrows C i).right := by
      change _ ∨ ObjectProperty.ofObj (fun j => (T j).right) (T i).right
      exact Or.inr (ObjectProperty.ofObj_apply (fun j => (T j).right) i)
    exact ⟨hEndpoints _ hX, hEndpoints _ hY⟩
  have hLocalCard : IsCardinalLocallyPresentable W.isLocal.FullSubcategory κ :=
    MorphismProperty.isLocallyPresentable_isLocal W κ hW
  have hLocal : IsLocallyPresentable.{w} W.isLocal.FullSubcategory :=
    ⟨κ, hκ, hLocalCard⟩
  let e := fullSubcategoryEquivOfEq (completionProperty_eq_testLocal C)
  exact e.symm.isLocallyPresentable

private def completionCofibrationArrows (C₀ : Type u₁) [Category.{v₁} C₀]
    [CategoryWithCofibrations C₀] : ObjectProperty (Arrow C₀) :=
  fun i => cofibrations C₀ i.hom

private instance completionCofibrationArrows_closed (C₀ : Type u₁) [Category.{v₁} C₀]
    [CategoryWithCofibrations C₀] [IsCofibrationCategory C₀] :
    (completionCofibrationArrows C₀).IsClosedUnderIsomorphisms where
  of_iso {i j} e hi := by
    let l : i.left ≅ j.left := asIso e.hom.left
    let r : i.right ≅ j.right := asIso e.hom.right
    have hnat : l.hom ≫ j.hom = i.hom ≫ r.hom := by
      change e.hom.left ≫ j.hom = i.hom ≫ e.hom.right
      exact e.hom.w
    have hl : cofibrations C₀ l.inv :=
      IsCofibrationCategory.isomorphisms_le (C := C₀) l.inv
        (MorphismProperty.isomorphisms.infer_property l.inv)
    have hr : cofibrations C₀ r.hom :=
      IsCofibrationCategory.isomorphisms_le (C := C₀) r.hom
        (MorphismProperty.isomorphisms.infer_property r.hom)
    have hcomp₀ : cofibrations C₀ ((l.inv ≫ i.hom) ≫ r.hom) :=
      (IsCofibrationCategory.isMultiplicative (C := C₀)).comp_mem (l.inv ≫ i.hom) r.hom
        ((IsCofibrationCategory.isMultiplicative (C := C₀)).comp_mem l.inv i.hom hl hi) hr
    have hcomp : cofibrations C₀ (l.inv ≫ i.hom ≫ r.hom) := by
      rw [← Category.assoc]
      exact hcomp₀
    have heq : j.hom = l.inv ≫ i.hom ≫ r.hom := by
      calc
        j.hom = 𝟙 _ ≫ j.hom := by simp
        _ = l.inv ≫ l.hom ≫ j.hom := by simp [Category.assoc]
        _ = l.inv ≫ (i.hom ≫ r.hom) := by rw [hnat]
        _ = l.inv ≫ i.hom ≫ r.hom := by simp [Category.assoc]
    change cofibrations C₀ j.hom
    rw [heq]
    exact hcomp

private theorem arrowEssentiallySmall (C₀ : Type u₁) [Category.{v₁} C₀]
    [EssentiallySmall.{w} C₀] : EssentiallySmall.{w} (Arrow C₀) := by
  let e : Arrow C₀ ≌ Arrow (SmallModel C₀) := Functor.mapArrowEquivalence (equivSmallModel C₀)
  have hs : EssentiallySmall.{w} (Arrow (SmallModel C₀)) :=
    essentiallySmall_of_small_of_locallySmall _
  exact (essentiallySmall_congr e).2 hs

private theorem completionCofibrationArrows_essentiallySmall (C₀ : Type u₁)
    [Category.{v₁} C₀] [CategoryWithCofibrations C₀] [EssentiallySmall.{w} C₀] :
    ObjectProperty.EssentiallySmall.{w} (completionCofibrationArrows C₀) := by
  letI : EssentiallySmall.{w} (Arrow C₀) := arrowEssentiallySmall C₀
  exact ObjectProperty.EssentiallySmall.of_le (P := completionCofibrationArrows C₀) (Q := ⊤)
    (by intro i hi; trivial)

private instance completionCofibrationArrows_fullSubcategory_essentiallySmall (C₀ : Type u₁)
    [Category.{v₁} C₀] [CategoryWithCofibrations C₀] [IsCofibrationCategory C₀]
    [EssentiallySmall.{w} C₀] :
    EssentiallySmall.{w} ((completionCofibrationArrows C₀).FullSubcategory) := by
  letI : EssentiallySmall.{w} (Arrow C₀) := arrowEssentiallySmall C₀
  letI : ObjectProperty.EssentiallySmall.{w} (completionCofibrationArrows C₀) :=
    completionCofibrationArrows_essentiallySmall C₀
  infer_instance

private theorem smallYoneda_map_app {A B : C} (f : A ⟶ B) (X : C) :
    ((smallYoneda C).obj X).map f.op =
      (yoneda.obj ((ShrinkHoms.equivalence C).functor.obj X)).map
        ((ShrinkHoms.equivalence C).functor.map f).op := by
  rfl

private theorem smallYoneda_isCompletion (X : C) :
    HomotopyHypothesis.Henry.IsCompletionPresheaf.{w} C ((smallYoneda C).obj X) := by
  constructor
  · intro I hI
    let e := ShrinkHoms.equivalence C
    have hI' : IsInitial (e.functor.obj I) := hI.isInitialObj e.functor
    change Nonempty (Unique (e.functor.obj I ⟶ e.functor.obj X))
    exact ⟨⟨⟨hI'.to _⟩, fun f => hI'.hom_ext _ _⟩⟩
  · intro A B X' Q i f k j h hi
    let e := ShrinkHoms.equivalence C
    let sq : Square C := ⟨i, f, k, j, h.w⟩
    have hsq : sq.IsPushout := h
    have hsq' : (sq.map e.functor).IsPushout := hsq.map e.functor
    have hPull := (Square.isPushout_iff_op_map_yoneda_isPullback (sq.map e.functor)).1 hsq'
    rw [smallYoneda_map_app k X, smallYoneda_map_app j X,
      smallYoneda_map_app i X, smallYoneda_map_app f X]
    exact hPull (e.functor.obj X)

private noncomputable def completionYonedaSmall : C ⥤
    HomotopyHypothesis.Henry.Completion.{w} C :=
  ObjectProperty.lift _ (smallYoneda C) (smallYoneda_isCompletion (C := C))

private noncomputable def completionGeneratingArrows (C₀ : Type u₁) [Category.{v₁} C₀]
    [CategoryWithCofibrations C₀] [CategoryWithWeakEquivalences C₀]
    [IsCofibrationCategory C₀] [IsCylinderCategory C₀] [EssentiallySmall.{w} C₀] :
    SmallModel ((completionCofibrationArrows C₀).FullSubcategory) →
      Arrow (HomotopyHypothesis.Henry.Completion.{w} C₀) := fun s =>
  let i := (equivSmallModel.{w} ((completionCofibrationArrows C₀).FullSubcategory)).inverse.obj s
  Arrow.mk ((completionYonedaSmall (C := C₀)).map i.obj.hom)

private noncomputable def completionGeneratingCofibrations (C₀ : Type u₁)
    [Category.{v₁} C₀] [CategoryWithCofibrations C₀] [CategoryWithWeakEquivalences C₀]
    [IsCofibrationCategory C₀] [IsCylinderCategory C₀]
    [EssentiallySmall.{w} C₀] :
    MorphismProperty (HomotopyHypothesis.Henry.Completion.{w} C₀) :=
  MorphismProperty.ofHoms (fun s => (completionGeneratingArrows C₀ s).hom)

private instance completionGeneratingCofibrations_small (C₀ : Type u₁)
    [Category.{v₁} C₀] [CategoryWithCofibrations C₀] [CategoryWithWeakEquivalences C₀]
    [IsCofibrationCategory C₀] [IsCylinderCategory C₀]
    [EssentiallySmall.{w} C₀] :
    MorphismProperty.IsSmall.{w} (completionGeneratingCofibrations C₀) := by
  unfold completionGeneratingCofibrations
  infer_instance

private noncomputable def completionYonedaSmallEquiv (A : C)
    (X : HomotopyHypothesis.Henry.Completion.{w} C) :
    ((completionYonedaSmall (C := C)).obj A ⟶ X) ≃ (X.obj).obj (op A) where
  toFun g := smallYonedaEquiv C A X.obj
    ((ObjectProperty.ι (IsCompletionPresheaf.{w} C)).map g)
  invFun a := ObjectProperty.homMk ((smallYonedaEquiv C A X.obj).symm a)
  left_inv g := by
    apply ObjectProperty.hom_ext
    change (smallYonedaEquiv C A X.obj).symm
        (smallYonedaEquiv C A X.obj ((ObjectProperty.ι
          (IsCompletionPresheaf.{w} C)).map g)) = g.hom
    simpa only [ObjectProperty.ι_map] using
      Equiv.symm_apply_apply (smallYonedaEquiv C A X.obj) g.hom
  right_inv a := by
    change smallYonedaEquiv C A X.obj
        ((smallYonedaEquiv C A X.obj).symm a) = a
    exact (smallYonedaEquiv C A X.obj).apply_symm_apply a

private theorem completionYonedaSmallEquiv_map {A B : C} (i : A ⟶ B)
    (X : HomotopyHypothesis.Henry.Completion.{w} C)
    (g : (completionYonedaSmall (C := C)).obj B ⟶ X) :
    completionYonedaSmallEquiv (C := C) A X
      ((completionYonedaSmall (C := C)).map i ≫ g) =
        (X.obj).map i.op (completionYonedaSmallEquiv (C := C) B X g) := by
  change smallYonedaEquiv C A X.obj
      ((smallYoneda C).map i ≫
        (ObjectProperty.ι (IsCompletionPresheaf.{w} C)).map g) = _
  exact smallYonedaEquiv_map C i X.obj _

private theorem completionYonedaSmallEquiv_comp_right (A : C)
    {X Y : HomotopyHypothesis.Henry.Completion.{w} C}
    (φ : X ⟶ Y) (g : (completionYonedaSmall (C := C)).obj A ⟶ X) :
    completionYonedaSmallEquiv (C := C) A Y (g ≫ φ) =
      φ.hom.app (op A) (completionYonedaSmallEquiv (C := C) A X g) := by
  change smallYonedaEquiv C A Y.obj
      ((ObjectProperty.ι (IsCompletionPresheaf.{w} C)).map g ≫ φ.hom) = _
  exact smallYonedaEquiv_comp_right C A φ.hom _

private noncomputable def smallYonedaFullyFaithful (C : Type u) [Category.{v} C]
    [LocallySmall.{w} C] : (smallYoneda C).FullyFaithful := by
  let e := ShrinkHoms.equivalence C
  let eP := smallYonedaEquivalence C
  exact (e.fullyFaithfulFunctor.comp
    (Yoneda.fullyFaithful (C := ShrinkHoms C))).comp eP.fullyFaithfulFunctor

private noncomputable def completionYonedaElementHomEquiv (A B : C) :
    (((completionYonedaSmall (C := C)).obj B).obj).obj (op A) ≃ (A ⟶ B) :=
  (smallYonedaEquiv C A ((smallYoneda C).obj B)).symm.trans
    ((smallYonedaFullyFaithful C).homEquiv).symm

private theorem completionYonedaElementHomEquiv_map {A B X : C} (i : A ⟶ B)
    (x : (((completionYonedaSmall (C := C)).obj X).obj).obj (op B)) :
    (completionYonedaElementHomEquiv (C := C) A X)
      ((((completionYonedaSmall (C := C)).obj X).obj).map i.op x) =
        i ≫ completionYonedaElementHomEquiv (C := C) B X x := by
  change ((smallYonedaFullyFaithful C).homEquiv).symm
      ((smallYonedaEquiv C A ((smallYoneda C).obj X)).symm
        (((smallYoneda C).obj X).map i.op x)) =
    i ≫ ((smallYonedaFullyFaithful C).homEquiv).symm
      ((smallYonedaEquiv C B ((smallYoneda C).obj X)).symm x)
  have hpre : (smallYoneda C).map
      ((smallYonedaFullyFaithful C).homEquiv.symm
        ((smallYonedaEquiv C B ((smallYoneda C).obj X)).symm x)) =
      (smallYonedaEquiv C B ((smallYoneda C).obj X)).symm x := by
    simpa only [Functor.FullyFaithful.homEquiv_apply] using
      (smallYonedaFullyFaithful C).homEquiv.apply_symm_apply
        ((smallYonedaEquiv C B ((smallYoneda C).obj X)).symm x)
  apply (smallYonedaFullyFaithful C).homEquiv.injective
  apply (smallYonedaEquiv C A ((smallYoneda C).obj X)).injective
  simp only [Equiv.apply_symm_apply, Functor.FullyFaithful.homEquiv_apply,
    Functor.map_comp, Equiv.symm_apply_apply, smallYonedaEquiv_map, hpre]
  rw [(smallYonedaEquiv C B ((smallYoneda C).obj X)).apply_symm_apply x]

private theorem completionYonedaElementHomEquiv_yonedaMap {A B : C} (f : A ⟶ B) :
    completionYonedaElementHomEquiv (C := C) A B
      (completionYonedaSmallEquiv (C := C) A
        ((completionYonedaSmall (C := C)).obj B)
        ((completionYonedaSmall (C := C)).map f)) = f := by
  change ((smallYonedaEquiv C A ((smallYoneda C).obj B)).symm.trans
      ((smallYonedaFullyFaithful C).homEquiv).symm)
    (smallYonedaEquiv C A ((smallYoneda C).obj B)
      ((smallYoneda C).map f)) = f
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  exact (smallYonedaFullyFaithful C).preimage_map f

private theorem completionYonedaElementHomEquiv_id (A : C) :
    completionYonedaElementHomEquiv (C := C) A A
      (completionYonedaSmallEquiv (C := C) A
        ((completionYonedaSmall (C := C)).obj A) (𝟙 _)) = 𝟙 A := by
  simpa using completionYonedaElementHomEquiv_yonedaMap (C := C) (f := 𝟙 A)

private noncomputable def isoOfHomEquiv
    {E : Type*} [Category E] {A B : E}
    (e : ∀ Y : E, (A ⟶ Y) ≃ (B ⟶ Y))
    (hnat : ∀ ⦃Y Z : E⦄ (f : Y ⟶ Z) (g : A ⟶ Y),
      e Z (g ≫ f) = e Y g ≫ f) : A ≅ B where
  hom := (e B).symm (𝟙 B)
  inv := e A (𝟙 A)
  hom_inv_id := by
    apply (e A).injective
    calc
      e A ((e B).symm (𝟙 B) ≫ e A (𝟙 A)) =
          e B ((e B).symm (𝟙 B)) ≫ e A (𝟙 A) := hnat (e A (𝟙 A)) _
      _ = e A (𝟙 A) := by simp
      _ = e A (𝟙 A) := rfl
  inv_hom_id := by
    have h := hnat ((e B).symm (𝟙 B)) (𝟙 A)
    simpa using h.symm

private abbrev completionRestriction_yonedaEvaluationEq
    {F : C ⥤ D} (hF : HomotopyHypothesis.Henry.IsCofibrationMorphism F)
    (A : C) (Y : HomotopyHypothesis.Henry.Completion.{w} D) :
    ((HomotopyHypothesis.Henry.Completion.restriction.{w} F hF).obj Y).obj.obj (op A) =
      (Y.obj).obj (op (F.obj A)) := rfl

private noncomputable def completionRestriction_yonedaHomEquiv
    {F : C ⥤ D} (hF : HomotopyHypothesis.Henry.IsCylinderMorphism F)
    {L : HomotopyHypothesis.Henry.Completion.{w} C ⥤
      HomotopyHypothesis.Henry.Completion.{w} D}
    (adj : L ⊣ HomotopyHypothesis.Henry.Completion.restriction.{w} F
      hF.toIsCofibrationMorphism) (A : C) :
    ∀ Y : HomotopyHypothesis.Henry.Completion.{w} D,
      (L.obj ((completionYonedaSmall (C := C)).obj A) ⟶ Y) ≃
        ((completionYonedaSmall (C := D)).obj (F.obj A) ⟶ Y) := by
  let R := HomotopyHypothesis.Henry.Completion.restriction.{w} F
    hF.toIsCofibrationMorphism
  let yC := completionYonedaSmall (C := C)
  let yD := completionYonedaSmall (C := D)
  let hEval : ∀ (Y : HomotopyHypothesis.Henry.Completion.{w} D),
      ((R.obj Y).obj).obj (op A) = (Y.obj).obj (op (F.obj A)) :=
    completionRestriction_yonedaEvaluationEq hF.toIsCofibrationMorphism A
  exact fun Y =>
    (adj.homEquiv (yC.obj A) Y).trans <|
      (completionYonedaSmallEquiv (C := C) A (R.obj Y)).trans <|
        (Equiv.cast (hEval Y)).trans (completionYonedaSmallEquiv (C := D)
          (F.obj A) Y).symm

private theorem completionRestriction_yonedaHomEquiv_naturality
    {F : C ⥤ D} (hF : HomotopyHypothesis.Henry.IsCylinderMorphism F)
    {L : HomotopyHypothesis.Henry.Completion.{w} C ⥤
      HomotopyHypothesis.Henry.Completion.{w} D}
    (adj : L ⊣ HomotopyHypothesis.Henry.Completion.restriction.{w} F
      hF.toIsCofibrationMorphism) (A : C)
    ⦃Y Z : HomotopyHypothesis.Henry.Completion.{w} D⦄
    (g : Y ⟶ Z) (f : L.obj ((completionYonedaSmall (C := C)).obj A) ⟶ Y) :
    completionRestriction_yonedaHomEquiv hF adj A Z (f ≫ g) =
      completionRestriction_yonedaHomEquiv hF adj A Y f ≫ g := by
  let R := HomotopyHypothesis.Henry.Completion.restriction.{w} F
    hF.toIsCofibrationMorphism
  let hEval : ∀ (Y : HomotopyHypothesis.Henry.Completion.{w} D),
      ((R.obj Y).obj).obj (op A) = (Y.obj).obj (op (F.obj A)) :=
    completionRestriction_yonedaEvaluationEq hF.toIsCofibrationMorphism A
  change (completionYonedaSmallEquiv (C := D) (F.obj A) Z).symm
      (Equiv.cast (hEval Z)
        (completionYonedaSmallEquiv (C := C) A (R.obj Z)
          (adj.homEquiv ((completionYonedaSmall (C := C)).obj A) Z (f ≫ g)))) =
    (completionYonedaSmallEquiv (C := D) (F.obj A) Y).symm
      (Equiv.cast (hEval Y)
        (completionYonedaSmallEquiv (C := C) A (R.obj Y)
          (adj.homEquiv ((completionYonedaSmall (C := C)).obj A) Y f))) ≫ g
  rw [adj.homEquiv_naturality_right]
  rw [completionYonedaSmallEquiv_comp_right (C := C) A (R.map g)]
  have hRestr : ((R.map g).hom.app (op A)) = g.hom.app (op (F.obj A)) := rfl
  rw [hRestr]
  apply (completionYonedaSmallEquiv (C := D) (F.obj A) Z).injective
  rw [completionYonedaSmallEquiv_comp_right]
  simp only [Equiv.apply_symm_apply]
  have hEY : hEval Y = (rfl :
      ((R.obj Y).obj).obj (op A) = (Y.obj).obj (op (F.obj A))) :=
    Subsingleton.elim _ _
  have hEZ : hEval Z = (rfl :
      ((R.obj Z).obj).obj (op A) = (Z.obj).obj (op (F.obj A))) :=
    Subsingleton.elim _ _
  rw [hEY, hEZ]
  rfl

private noncomputable def completionRestriction_yonedaIso
    {F : C ⥤ D} (hF : HomotopyHypothesis.Henry.IsCylinderMorphism F)
    {L : HomotopyHypothesis.Henry.Completion.{w} C ⥤
      HomotopyHypothesis.Henry.Completion.{w} D}
    (adj : L ⊣ HomotopyHypothesis.Henry.Completion.restriction.{w} F
      hF.toIsCofibrationMorphism) (A : C) :
    L.obj ((completionYonedaSmall (C := C)).obj A) ≅
      (completionYonedaSmall (C := D)).obj (F.obj A) :=
  isoOfHomEquiv (completionRestriction_yonedaHomEquiv hF adj A) (by
    intro Y Z g f
    exact completionRestriction_yonedaHomEquiv_naturality hF adj A g f)

private theorem completionRestriction_yonedaIso_hom_equiv
    {F : C ⥤ D} (hF : HomotopyHypothesis.Henry.IsCylinderMorphism F)
    {L : HomotopyHypothesis.Henry.Completion.{w} C ⥤
      HomotopyHypothesis.Henry.Completion.{w} D}
    (adj : L ⊣ HomotopyHypothesis.Henry.Completion.restriction.{w} F
      hF.toIsCofibrationMorphism) (A : C) :
    completionRestriction_yonedaHomEquiv hF adj A
        ((completionYonedaSmall (C := D)).obj (F.obj A))
        (completionRestriction_yonedaIso hF adj A).hom = 𝟙 _ := by
  change completionRestriction_yonedaHomEquiv hF adj A
      ((completionYonedaSmall (C := D)).obj (F.obj A))
      ((completionRestriction_yonedaHomEquiv hF adj A
        ((completionYonedaSmall (C := D)).obj (F.obj A))).symm (𝟙 _)) = 𝟙 _
  exact Equiv.apply_symm_apply _ _

private theorem completionRestriction_yonedaUnit_element
    {F : C ⥤ D} (hF : HomotopyHypothesis.Henry.IsCylinderMorphism F)
    {L : HomotopyHypothesis.Henry.Completion.{w} C ⥤
      HomotopyHypothesis.Henry.Completion.{w} D}
    (adj : L ⊣ HomotopyHypothesis.Henry.Completion.restriction.{w} F
      hF.toIsCofibrationMorphism) (A U : C)
    (a : (((completionYonedaSmall (C := C)).obj A).obj).obj (op U)) :
    completionYonedaElementHomEquiv (C := D) (F.obj U) (F.obj A)
      ((completionRestriction_yonedaIso hF adj A).hom.hom.app (op (F.obj U))
        ((adj.unit.app ((completionYonedaSmall (C := C)).obj A)).hom.app (op U) a)) =
      F.map (completionYonedaElementHomEquiv (C := C) U A a) := by
  let R := HomotopyHypothesis.Henry.Completion.restriction.{w} F
    hF.toIsCofibrationMorphism
  let yC := completionYonedaSmall (C := C)
  let yD := completionYonedaSmall (C := D)
  let iso := completionRestriction_yonedaIso hF adj A
  let g : yC.obj A ⟶ R.obj (yD.obj (F.obj A)) :=
    adj.homEquiv (yC.obj A) (yD.obj (F.obj A)) iso.hom
  let idC : (((yC.obj A).obj).obj (op A)) :=
    completionYonedaSmallEquiv (C := C) A (yC.obj A) (𝟙 _)
  let idD : (((yD.obj (F.obj A)).obj).obj (op (F.obj A))) :=
    completionYonedaSmallEquiv (C := D) (F.obj A) (yD.obj (F.obj A)) (𝟙 _)
  let aHom := completionYonedaElementHomEquiv (C := C) U A a
  have hAdj : g = adj.unit.app (yC.obj A) ≫ R.map iso.hom := by
    dsimp [g]
    exact Adjunction.homEquiv_unit adj (yC.obj A) (yD.obj (F.obj A)) iso.hom
  let eVal := completionRestriction_yonedaEvaluationEq
    hF.toIsCofibrationMorphism A (yD.obj (F.obj A))
  have hIsoEval : (completionYonedaSmallEquiv (C := D) (F.obj A)
      (yD.obj (F.obj A))).symm (Equiv.cast eVal
        (completionYonedaSmallEquiv (C := C) A (R.obj (yD.obj (F.obj A))) g)) = 𝟙 _ := by
    simpa [g, iso, R, yC, yD, completionRestriction_yonedaHomEquiv] using
      completionRestriction_yonedaIso_hom_equiv hF adj A
  have hcast : Equiv.cast eVal
      (completionYonedaSmallEquiv (C := C) A (R.obj (yD.obj (F.obj A))) g) = idD := by
    apply (completionYonedaSmallEquiv (C := D) (F.obj A)
      (yD.obj (F.obj A))).symm.injective
    simpa [idD] using hIsoEval
  have hBase : completionYonedaSmallEquiv (C := C) A
      (R.obj (yD.obj (F.obj A))) g = idD := by
    exact eq_of_heq ((Equiv.cast_eq_iff_heq eVal).1 hcast)
  have hRepresent : a = (yC.obj A).obj.map aHom.op idC := by
    apply (completionYonedaElementHomEquiv (C := C) U A).injective
    symm
    calc
      completionYonedaElementHomEquiv (C := C) U A
          ((yC.obj A).obj.map aHom.op idC) =
          aHom ≫ completionYonedaElementHomEquiv (C := C) A A idC := by
            rw [completionYonedaElementHomEquiv_map]
      _ = aHom := by rw [completionYonedaElementHomEquiv_id]; simp
      _ = completionYonedaElementHomEquiv (C := C) U A a := rfl
  have hEvalRepresent : completionYonedaSmallEquiv (C := C) U (yC.obj A)
      ((yC.map aHom)) = a := by
    have h := completionYonedaSmallEquiv_map (C := C) aHom (yC.obj A)
      (𝟙 (yC.obj A))
    change completionYonedaSmallEquiv (C := C) U (yC.obj A)
        ((yC.map aHom) ≫ 𝟙 (yC.obj A)) =
      (yC.obj A).obj.map aHom.op idC at h
    rw [Category.comp_id] at h
    rw [← hRepresent] at h
    exact h
  have hEvalG : g.hom.app (op U) a =
      (R.obj (yD.obj (F.obj A))).obj.map aHom.op
        (completionYonedaSmallEquiv (C := C) A (R.obj (yD.obj (F.obj A))) g) := by
    calc
      g.hom.app (op U) a =
          completionYonedaSmallEquiv (C := C) U (R.obj (yD.obj (F.obj A)))
            ((yC.map aHom) ≫ g) := by
              rw [completionYonedaSmallEquiv_comp_right, hEvalRepresent]
      _ = (R.obj (yD.obj (F.obj A))).obj.map aHom.op
          (completionYonedaSmallEquiv (C := C) A (R.obj (yD.obj (F.obj A))) g) :=
            completionYonedaSmallEquiv_map aHom (R.obj (yD.obj (F.obj A))) g
  have hEvalUnit : completionYonedaElementHomEquiv (C := D) (F.obj U) (F.obj A)
      (g.hom.app (op U) a) = F.map aHom := by
    rw [hBase] at hEvalG
    rw [hEvalG]
    change completionYonedaElementHomEquiv (C := D) (F.obj U) (F.obj A)
        ((yD.obj (F.obj A)).obj.map (F.map aHom).op idD) = F.map aHom
    calc
      completionYonedaElementHomEquiv (C := D) (F.obj U) (F.obj A)
          ((yD.obj (F.obj A)).obj.map (F.map aHom).op idD) =
          F.map aHom ≫ completionYonedaElementHomEquiv (C := D)
            (F.obj A) (F.obj A) idD := by
              rw [completionYonedaElementHomEquiv_map]
      _ = F.map aHom := by rw [completionYonedaElementHomEquiv_id]; simp
  have hAdjEval : g.hom.app (op U) a =
      iso.hom.hom.app (op (F.obj U))
        ((adj.unit.app (yC.obj A)).hom.app (op U) a) := by
    have hHom : g.hom =
        (adj.unit.app (yC.obj A)).hom ≫ (R.map iso.hom).hom := by
      simpa using congrArg
        (fun f : yC.obj A ⟶ R.obj (yD.obj (F.obj A)) => f.hom) hAdj
    have hRestr : (R.map iso.hom).hom.app (op U) = iso.hom.hom.app (op (F.obj U)) := rfl
    rw [hHom, NatTrans.comp_app, CategoryTheory.comp_apply, hRestr]
    rfl
  change completionYonedaElementHomEquiv (C := D) (F.obj U) (F.obj A)
      (iso.hom.hom.app (op (F.obj U))
        ((adj.unit.app (yC.obj A)).hom.app (op U) a)) = F.map aHom
  rw [← hAdjEval]
  exact hEvalUnit

private theorem completionRestriction_yonedaUnit_element_cast
    {F : C ⥤ D} (hF : HomotopyHypothesis.Henry.IsCylinderMorphism F)
    {L : HomotopyHypothesis.Henry.Completion.{w} C ⥤
      HomotopyHypothesis.Henry.Completion.{w} D}
    (adj : L ⊣ HomotopyHypothesis.Henry.Completion.restriction.{w} F
      hF.toIsCofibrationMorphism) (A U : C)
    (a : (((completionYonedaSmall (C := C)).obj A).obj).obj (op U)) :
    completionYonedaElementHomEquiv (C := D) (F.obj U) (F.obj A)
      ((completionRestriction_yonedaIso hF adj A).hom.hom.app (op (F.obj U))
        (Equiv.cast (completionRestriction_yonedaEvaluationEq
          hF.toIsCofibrationMorphism U (L.obj ((completionYonedaSmall (C := C)).obj A)))
          ((adj.unit.app ((completionYonedaSmall (C := C)).obj A)).hom.app (op U) a))) =
      F.map (completionYonedaElementHomEquiv (C := C) U A a) := by
  let hEval := completionRestriction_yonedaEvaluationEq hF.toIsCofibrationMorphism U
    (L.obj ((completionYonedaSmall (C := C)).obj A))
  cases hEval
  exact completionRestriction_yonedaUnit_element hF adj A U a

private theorem completionYonedaMap_hasLiftingProperty_iff
    {A B : C} (i : A ⟶ B) {X Y : HomotopyHypothesis.Henry.Completion.{w} C}
    (f : X ⟶ Y) :
    HasLiftingProperty ((completionYonedaSmall (C := C)).map i) f ↔
      ∀ (a : (X.obj).obj (op A)) (b : (Y.obj).obj (op B)),
        f.hom.app (op A) a = (Y.obj).map i.op b →
          ∃ l : (X.obj).obj (op B), (X.obj).map i.op l = a ∧ f.hom.app (op B) l = b := by
  constructor
  · intro h a b hab
    let top := (completionYonedaSmallEquiv (C := C) A X).symm a
    let bottom := (completionYonedaSmallEquiv (C := C) B Y).symm b
    have hsq : top ≫ f = (completionYonedaSmall (C := C)).map i ≫ bottom := by
      apply (completionYonedaSmallEquiv (C := C) A Y).injective
      rw [completionYonedaSmallEquiv_comp_right, completionYonedaSmallEquiv_map]
      simpa [top, bottom] using hab
    let sq : CommSq top ((completionYonedaSmall (C := C)).map i) f bottom := ⟨hsq⟩
    obtain ⟨lift⟩ := (h.sq_hasLift sq).exists_lift
    refine ⟨completionYonedaSmallEquiv (C := C) B X lift.l, ?_, ?_⟩
    · have hleft := congrArg (completionYonedaSmallEquiv (C := C) A X) lift.fac_left
      rw [completionYonedaSmallEquiv_map] at hleft
      simpa [top] using hleft
    · have hright := congrArg (completionYonedaSmallEquiv (C := C) B Y) lift.fac_right
      rw [completionYonedaSmallEquiv_comp_right] at hright
      simpa [bottom] using hright
  · intro h
    refine ⟨fun {top bottom} sq => ?_⟩
    let a := completionYonedaSmallEquiv (C := C) A X top
    let b := completionYonedaSmallEquiv (C := C) B Y bottom
    have hab : f.hom.app (op A) a = (Y.obj).map i.op b := by
      have hsq := congrArg (completionYonedaSmallEquiv (C := C) A Y) sq.w
      rw [completionYonedaSmallEquiv_comp_right, completionYonedaSmallEquiv_map] at hsq
      exact hsq
    obtain ⟨l, hl, hr⟩ := h a b hab
    let lift := (completionYonedaSmallEquiv (C := C) B X).symm l
    refine ⟨⟨lift, ?_, ?_⟩⟩
    · apply (completionYonedaSmallEquiv (C := C) A X).injective
      rw [completionYonedaSmallEquiv_map]
      simpa [lift, a] using hl
    · apply (completionYonedaSmallEquiv (C := C) B Y).injective
      rw [completionYonedaSmallEquiv_comp_right]
      simpa [lift, b] using hr

private theorem completionGeneratingRlp_iff_trivialFibration
    {X Y : HomotopyHypothesis.Henry.Completion.{w} C} (f : X ⟶ Y) :
    (completionGeneratingCofibrations C).rlp f ↔
      HomotopyHypothesis.Henry.Completion.trivialFibrations C f := by
  constructor
  · intro h A B i hi a b hab
    let T := completionCofibrationArrows C
    let E := equivSmallModel.{w} (T.FullSubcategory)
    let x : T.FullSubcategory := ⟨Arrow.mk i, hi⟩
    let s := E.functor.obj x
    let eBase : Arrow.mk i ≅ Arrow.mk ((E.inverse.obj s).obj.hom) :=
      (ObjectProperty.ι T).mapIso (E.unitIso.app x)
    have eGen : Arrow.mk ((completionYonedaSmall (C := C)).map i) ≅
        completionGeneratingArrows C s := by
      change Arrow.mk ((completionYonedaSmall (C := C)).map i) ≅
        Arrow.mk ((completionYonedaSmall (C := C)).map ((E.inverse.obj s).obj.hom))
      exact (Functor.mapArrow (completionYonedaSmall (C := C))).mapIso eBase
    have hGen : HasLiftingProperty (completionGeneratingArrows C s).hom f := by
      exact h _ (MorphismProperty.ofHoms.mk s)
    have hLift : HasLiftingProperty ((completionYonedaSmall (C := C)).map i) f :=
      (HasLiftingProperty.iff_of_arrow_iso_left eGen f).2 hGen
    exact (completionYonedaMap_hasLiftingProperty_iff i f).1 hLift a b hab
  · intro h P Q g hg
    change MorphismProperty.ofHoms
      (fun s => (completionGeneratingArrows C s).hom) g at hg
    cases hg with
    | mk s =>
      let T := completionCofibrationArrows C
      let iObj := (equivSmallModel.{w} (T.FullSubcategory)).inverse.obj s
      let i := iObj.obj.hom
      have hi : cofibrations C i := iObj.property
      change HasLiftingProperty ((completionYonedaSmall (C := C)).map i) f
      apply (completionYonedaMap_hasLiftingProperty_iff i f).2
      intro a b hab
      exact h i hi a b hab

private theorem completionGeneratingCofibrations_hasSmallObjectArgument :
    MorphismProperty.HasSmallObjectArgument.{w} (completionGeneratingCofibrations C) := by
  classical
  letI : IsLocallyPresentable.{w} (HomotopyHypothesis.Henry.Completion.{w} C) :=
    completionLocallyPresentable
  obtain ⟨κLP, hκLP, hLocallyPresentable⟩ :=
    IsLocallyPresentable.exists_cardinal
      (HomotopyHypothesis.Henry.Completion.{w} C)
  letI : Fact κLP.IsRegular := hκLP
  letI : IsCardinalLocallyPresentable
      (HomotopyHypothesis.Henry.Completion.{w} C) κLP := hLocallyPresentable
  let sources : ObjectProperty (HomotopyHypothesis.Henry.Completion.{w} C) :=
    ObjectProperty.ofObj (fun s : SmallModel
      ((completionCofibrationArrows C).FullSubcategory) =>
        (completionGeneratingArrows C s).left)
  letI : ObjectProperty.Small.{w} sources := by
    dsimp [sources]
    infer_instance
  obtain ⟨κ, hκ, hSources⟩ :=
    ObjectProperty.le_isCardinalPresentable.{w} sources
  letI : Fact κ.IsRegular := hκ
  letI : OrderBot κ.ord.ToType :=
    Ordinal.toTypeOrderBot (ne_of_gt hκ.out.ord_pos)
  have hDomain {A B : HomotopyHypothesis.Henry.Completion.{w} C}
      (i : A ⟶ B) (hi : completionGeneratingCofibrations C i) :
      IsCardinalPresentable A κ := by
    change MorphismProperty.ofHoms
      (fun s => (completionGeneratingArrows C s).hom) i at hi
    cases hi with
    | mk s =>
      exact hSources _ (ObjectProperty.ofObj_apply
        (fun s : SmallModel ((completionCofibrationArrows C).FullSubcategory) =>
          (completionGeneratingArrows C s).left) s)
  have hPreserves {A B X Y : HomotopyHypothesis.Henry.Completion.{w} C}
      (i : A ⟶ B) (hi : completionGeneratingCofibrations C i) (f : X ⟶ Y)
      (hf : RelativeCellComplex.{w}
        (fun (_ : κ.ord.ToType) => (completionGeneratingCofibrations C).homFamily) f) :
      PreservesColimit hf.F (coyoneda.obj (op A)) := by
    letI : IsCardinalPresentable A κ := hDomain i hi
    have hPres := preservesColimitsOfShape_of_isCardinalPresentable
      A κ (κ.ord.ToType)
    letI : PreservesColimitsOfShape (κ.ord.ToType) (coyoneda.obj (op A)) := hPres
    change PreservesColimit hf.F (coyoneda.obj (op A))
    infer_instance
  let hSO : MorphismProperty.IsCardinalForSmallObjectArgument.{w}
      (completionGeneratingCofibrations C) κ :=
    { preservesColimit := hPreserves }
  exact ⟨⟨κ, hκ, inferInstance, hSO⟩⟩

private theorem completionCofibrations_eq_generators_llp :
    HomotopyHypothesis.Henry.Completion.cofibrations C =
      (completionGeneratingCofibrations C).rlp.llp := by
  have hRlp : (completionGeneratingCofibrations C).rlp =
      HomotopyHypothesis.Henry.Completion.trivialFibrations C := by
    ext X Y f
    exact completionGeneratingRlp_iff_trivialFibration (C := C) f
  change (HomotopyHypothesis.Henry.Completion.trivialFibrations C).llp = _
  rw [← hRlp]

private theorem completionCofibrant_retract_relativeCellComplex
    {X : HomotopyHypothesis.Henry.Completion.{w} C}
    (hX : IsCofibrantFor
      (HomotopyHypothesis.Henry.Completion.cofibrations C) X) :
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular) (_ : OrderBot κ.ord.ToType)
      (O Z : HomotopyHypothesis.Henry.Completion.{w} C) (hO : IsInitial O)
      (cell : O ⟶ Z) (s : X ⟶ Z) (r : Z ⟶ X)
      (hCell : RelativeCellComplex.{w}
        (fun (_ : κ.ord.ToType) => (completionGeneratingCofibrations C).homFamily) cell),
      hO.to X ≫ s = cell ∧ s ≫ r = 𝟙 X := by
  classical
  let hSemi := _root_.HomotopyHypothesis.Henry.Packages.completion_isSemiModelCategory
    (C := C)
  letI : HasFiniteColimits (HomotopyHypothesis.Henry.Completion.{w} C) :=
    hSemi.1.hasFiniteColimits
  let I := completionGeneratingCofibrations C
  letI : MorphismProperty.HasSmallObjectArgument.{w} I :=
    completionGeneratingCofibrations_hasSmallObjectArgument (C := C)
  let κ := I.smallObjectκ
  letI : Fact κ.IsRegular :=
    MorphismProperty.HasSmallObjectArgument.exists_cardinal.choose_spec.choose
  let O := ⊥_ (HomotopyHypothesis.Henry.Completion.{w} C)
  let hO : IsInitial O := initialIsInitial
  let u := hO.to X
  have hU : I.rlp.llp u := by
    rw [← completionCofibrations_eq_generators_llp]
    exact hX hO
  let cell := SmallObject.ιObj I κ u
  let r := SmallObject.πObj I κ u
  have hCell : RelativeCellComplex.{w}
      (fun (_ : κ.ord.ToType) => I.homFamily) cell :=
    SmallObject.relativeCellComplexιObj I κ u
  have hp : I.rlp r := SmallObject.rlp_πObj I κ u
  have hfactor : cell ≫ r = u := SmallObject.ιObj_πObj I κ u
  have hLift : HasLiftingProperty u r := hU r hp
  let sq : CommSq cell u r (𝟙 X) := ⟨by rw [hfactor]; simp⟩
  obtain ⟨lift⟩ := (hLift.sq_hasLift sq).exists_lift
  refine ⟨κ, inferInstance, inferInstance, O, _, hO, cell, lift.l, r, hCell, ?_, ?_⟩
  · simpa [u, cell] using lift.fac_left
  · exact lift.fac_right

private theorem completionAdjunctionUnit_isWeakEquivalence_of_retract
    {L : HomotopyHypothesis.Henry.Completion.{w} C ⥤
      HomotopyHypothesis.Henry.Completion.{w} D}
    {R : HomotopyHypothesis.Henry.Completion.{w} D ⥤
      HomotopyHypothesis.Henry.Completion.{w} C}
    (adj : L ⊣ R) {X Z : HomotopyHypothesis.Henry.Completion.{w} C}
    (s : X ⟶ Z) (r : Z ⟶ X) (hsr : s ≫ r = 𝟙 X)
    (hηZ : HomotopyHypothesis.Henry.Completion.weakEquivalences C
      (adj.unit.app Z)) :
    HomotopyHypothesis.Henry.Completion.weakEquivalences C (adj.unit.app X) := by
  let hSemi := _root_.HomotopyHypothesis.Henry.Packages.completion_isSemiModelCategory
    (C := C)
  letI : (HomotopyHypothesis.Henry.Completion.weakEquivalences C).IsStableUnderRetracts :=
    hSemi.1.W_retracts
  let iArrow : Arrow.mk (adj.unit.app X) ⟶ Arrow.mk (adj.unit.app Z) :=
    Arrow.homMk' s ((L ⋙ R).map s) (by
      simpa using NatTrans.naturality adj.unit s)
  let rArrow : Arrow.mk (adj.unit.app Z) ⟶ Arrow.mk (adj.unit.app X) :=
    Arrow.homMk' r ((L ⋙ R).map r) (by
      simpa using NatTrans.naturality adj.unit r)
  have e : RetractArrow (adj.unit.app X) (adj.unit.app Z) := by
    refine ⟨iArrow, rArrow, ?_⟩
    apply Arrow.hom_ext
    · exact hsr
    · calc
        ((L ⋙ R).map s) ≫ ((L ⋙ R).map r) = (L ⋙ R).map (s ≫ r) := by
          rw [Functor.map_comp]
        _ = (L ⋙ R).map (𝟙 X) := by rw [hsr]
        _ = 𝟙 ((L ⋙ R).obj X) := by simp
  exact (HomotopyHypothesis.Henry.Completion.weakEquivalences C).of_retract e hηZ

private theorem relativeCylinderEndpointProperties {A B : C} {i : A ⟶ B}
    (hi : cofibrations C i) (cyl : RelativeCylinder i) :
    (cofibrations C (cyl.j₀ ≫ cyl.c) ∧ weakEquivalences C (cyl.j₀ ≫ cyl.c)) ∧
      (cofibrations C (cyl.j₁ ≫ cyl.c) ∧ weakEquivalences C (cyl.j₁ ≫ cyl.c)) := by
  have hcof₀ := (IsCofibrationCategory.isMultiplicative (C := C)).comp_mem
    cyl.j₀ cyl.c ((IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout
      cyl.isPushout hi) cyl.c_mem
  have hcof₁ := (IsCofibrationCategory.isMultiplicative (C := C)).comp_mem
    cyl.j₁ cyl.c ((IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout
      cyl.isPushout.flip hi) cyl.c_mem
  have hid : weakEquivalences C (𝟙 B) :=
    IsCylinderCategory.isomorphisms_le_weakEquivalences (C := C) (𝟙 B)
      (MorphismProperty.isomorphisms.infer_property (𝟙 B))
  have hw₀ := IsCylinderCategory.twoOutOfSix (C := C) (cyl.j₀ ≫ cyl.c) cyl.p (𝟙 B)
    (by simpa [Category.assoc, cyl.j₀_c_p] using hid) (by simpa using cyl.p_mem)
  have hw₁ := IsCylinderCategory.twoOutOfSix (C := C) (cyl.j₁ ≫ cyl.c) cyl.p (𝟙 B)
    (by simpa [Category.assoc, cyl.j₁_c_p] using hid) (by simpa using cyl.p_mem)
  exact ⟨⟨hcof₀, hw₀.1⟩, ⟨hcof₁, hw₁.1⟩⟩

private theorem brownFactorization {A B : C} (f : A ⟶ B) :
    ∃ (M : C) (i : A ⟶ M) (p : M ⟶ B),
      cofibrations C i ∧ weakEquivalences C p ∧ i ≫ p = f := by
  classical
  obtain ⟨O, hO_nonempty⟩ := IsCofibrationCategory.exists_initial (C := C)
  let hO : IsInitial O := Classical.choice hO_nonempty
  have hA0 : cofibrations C (hO.to A) :=
    IsCofibrationCategory.initial_cofibration hO A
  have hB0 : cofibrations C (hO.to B) :=
    IsCofibrationCategory.initial_cofibration hO B
  let cyl := Classical.choice (IsCylinderCategory.exists_cylinder (C := C) hO A)
  have hPAB : HasPushout (hO.to A) (hO.to B) :=
    IsCofibrationCategory.hasPushout (C := C) (hO.to A) (hO.to B) hA0
  letI := hPAB
  let PAB := pushout (hO.to A) (hO.to B)
  let a : A ⟶ PAB := pushout.inl (hO.to A) (hO.to B)
  let b : B ⟶ PAB := pushout.inr (hO.to A) (hO.to B)
  let hAB : IsPushout (hO.to A) (hO.to B) a b :=
    IsPushout.of_hasPushout (hO.to A) (hO.to B)
  have hP0 : HasPushout (hO.to A) (hO.to A) := cyl.isPushout.hasPushout
  letI := hP0
  have hdcond : (hO.to A) ≫ a = (hO.to A) ≫ (f ≫ b) := hO.hom_ext _ _
  let d : cyl.P ⟶ PAB := cyl.isPushout.desc a (f ≫ b) hdcond
  have hM : HasPushout cyl.c d :=
    IsCofibrationCategory.hasPushout (C := C) cyl.c d cyl.c_mem
  letI := hM
  let M := pushout cyl.c d
  let mI : cyl.I ⟶ M := pushout.inl cyl.c d
  let mAB : PAB ⟶ M := pushout.inr cyl.c d
  have hMpo : IsPushout cyl.c d mI mAB := IsPushout.of_hasPushout cyl.c d
  let qAB : PAB ⟶ B := hAB.desc f (𝟙 B) (by apply hO.hom_ext)
  have hqABa : a ≫ qAB = f := by simp [qAB, hAB]
  have hqABb : b ≫ qAB = 𝟙 B := by simp [qAB, hAB]
  have hcomm : cyl.c ≫ (cyl.p ≫ f) = d ≫ qAB := by
    apply cyl.isPushout.hom_ext
    · calc
        cyl.j₀ ≫ cyl.c ≫ cyl.p ≫ f = (cyl.j₀ ≫ cyl.c ≫ cyl.p) ≫ f := by simp [Category.assoc]
        _ = f := by rw [cyl.j₀_c_p]; simp
        _ = cyl.j₀ ≫ d ≫ qAB := by simp [d, qAB]
    · calc
        cyl.j₁ ≫ cyl.c ≫ cyl.p ≫ f = (cyl.j₁ ≫ cyl.c ≫ cyl.p) ≫ f := by simp [Category.assoc]
        _ = f := by rw [cyl.j₁_c_p]; simp
        _ = cyl.j₁ ≫ d ≫ qAB := by simp [d, qAB]
  let qM : M ⟶ B := hMpo.desc (cyl.p ≫ f) qAB hcomm
  have hqMI : mI ≫ qM = cyl.p ≫ f := by simp [qM, hMpo]
  have hqMAB : mAB ≫ qM = qAB := by simp [qM, hMpo]
  have hinc : IsPushout (cyl.j₁ ≫ cyl.c) f mI (b ≫ mAB) := by
    let e₀ : A ⟶ cyl.I := cyl.j₀ ≫ cyl.c
    let e₁ : A ⟶ cyl.I := cyl.j₁ ≫ cyl.c
    have hsq : e₁ ≫ mI = f ≫ (b ≫ mAB) := by
      calc
        e₁ ≫ mI = cyl.j₁ ≫ (cyl.c ≫ mI) := by simp [e₁, Category.assoc]
        _ = cyl.j₁ ≫ (d ≫ mAB) := by rw [hMpo.w]
        _ = (cyl.j₁ ≫ d) ≫ mAB := by simp [Category.assoc]
        _ = f ≫ (b ≫ mAB) := by simp [d, Category.assoc]
    let t : PushoutCocone e₁ f := PushoutCocone.mk mI (b ≫ mAB) hsq
    have ht : IsColimit t := by
      apply PushoutCocone.isColimitAux' t
      intro s
      have hinit : (hO.to A) ≫ (e₀ ≫ s.inl) = (hO.to B) ≫ s.inr := hO.hom_ext _ _
      let q : PAB ⟶ s.pt := hAB.desc (e₀ ≫ s.inl) s.inr hinit
      have hcompat : d ≫ q = cyl.c ≫ s.inl := by
        apply cyl.isPushout.hom_ext
        · simp [q, d, hAB, e₀]
        · calc
            cyl.j₁ ≫ d ≫ q = f ≫ b ≫ q := by simp [d, Category.assoc]
            _ = f ≫ s.inr := by simp [q]
            _ = e₁ ≫ s.inl := s.condition.symm
            _ = cyl.j₁ ≫ cyl.c ≫ s.inl := by simpa [e₁]
      let m := hMpo.desc s.inl q hcompat.symm
      have hmI : mI ≫ m = s.inl := by
        dsimp [m]
        exact hMpo.inl_desc s.inl q hcompat.symm
      have hmAB : mAB ≫ m = q := by
        dsimp [m]
        exact hMpo.inr_desc s.inl q hcompat.symm
      refine ⟨m, hmI, ?_, ?_⟩
      · calc
          (b ≫ mAB) ≫ m = b ≫ (mAB ≫ m) := by simp [Category.assoc]
          _ = b ≫ q := by rw [hmAB]
          _ = s.inr := by simp [q]
      · intro m' hm'I hm'B
        change M ⟶ s.pt at m'
        change mI ≫ m' = s.inl at hm'I
        have hmAB' : mAB ≫ m' = q := by
          apply hAB.hom_ext
          · calc
              a ≫ mAB ≫ m' = cyl.j₀ ≫ d ≫ mAB ≫ m' := by simp [d, Category.assoc]
              _ = cyl.j₀ ≫ (d ≫ mAB) ≫ m' := by simp [Category.assoc]
              _ = cyl.j₀ ≫ (cyl.c ≫ mI) ≫ m' := by rw [← hMpo.w]
              _ = cyl.j₀ ≫ cyl.c ≫ s.inl := by simp [Category.assoc, hm'I]
              _ = a ≫ q := by simp [q, e₀]
          · calc
              b ≫ mAB ≫ m' = (b ≫ mAB) ≫ m' := by simp [Category.assoc]
              _ = s.inr := hm'B
              _ = b ≫ q := by simp [q]
        apply hMpo.hom_ext
        · calc
            mI ≫ m' = s.inl := hm'I
            _ = mI ≫ m := hmI.symm
        · exact hmAB'.trans hmAB.symm
    exact IsPushout.of_isColimit ht
  have hend := relativeCylinderEndpointProperties hA0 cyl
  have hincW : weakEquivalences C (b ≫ mAB) :=
    IsCylinderCategory.trivialCofibration_cobaseChange (C := C)
      (cyl.j₁ ≫ cyl.c) f mI (b ≫ mAB) hinc hend.2.1 hend.2.2
  have hid : weakEquivalences C (𝟙 B) :=
    IsCylinderCategory.isomorphisms_le_weakEquivalences (C := C) (𝟙 B)
      (MorphismProperty.isomorphisms.infer_property (𝟙 B))
  have hsqW : weakEquivalences C ((b ≫ mAB) ≫ qM) := by
    rw [Category.assoc, hqMAB, hqABb]
    exact hid
  have hqW := IsCylinderCategory.twoOutOfSix (C := C) (𝟙 B) (b ≫ mAB) qM
    (by simpa using hincW) hsqW
  have hiW : weakEquivalences C qM := hqW.2.2.1
  have hia : cofibrations C (a ≫ mAB) :=
    (IsCofibrationCategory.isMultiplicative (C := C)).comp_mem a mAB
      ((IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout hAB hB0)
      ((IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout hMpo.flip cyl.c_mem)
  refine ⟨M, a ≫ mAB, qM, hia, hiW, ?_⟩
  calc
    (a ≫ mAB) ≫ qM = a ≫ (mAB ≫ qM) := by simp [Category.assoc]
    _ = a ≫ qAB := by rw [hqMAB]
    _ = f := hqABa

private theorem cofibrationLiftsAgainstWeakEquivalence {A B X Y : C}
    (i : A ⟶ B) (hi : cofibrations C i) (f : A ⟶ X) (w : X ⟶ Y) (g : B ⟶ Y)
    (hsq : i ≫ g = f ≫ w) (hw : weakEquivalences C w) :
    ∃ l : B ⟶ X, i ≫ l = f := by
  classical
  letI : HasPushout i f := IsCofibrationCategory.hasPushout (C := C) i f hi
  let P := pushout i f
  let k : B ⟶ P := pushout.inl i f
  let j : X ⟶ P := pushout.inr i f
  let hP : IsPushout i f k j := IsPushout.of_hasPushout i f
  let q : P ⟶ Y := hP.desc g w hsq
  obtain ⟨Z, c, e, hc, he, hce⟩ := brownFactorization q
  have hjcof : cofibrations C j :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout hP.flip hi
  have hJcof : cofibrations C (j ≫ c) :=
    (IsCofibrationCategory.isMultiplicative (C := C)).comp_mem j c hjcof hc
  have hcomp : (j ≫ c) ≫ e = w := by
    calc
      (j ≫ c) ≫ e = j ≫ (c ≫ e) := by simp [Category.assoc]
      _ = j ≫ q := by rw [hce]
      _ = w := by simp [q]
  have hJwcomp : weakEquivalences C ((j ≫ c) ≫ e) := by rw [hcomp]; exact hw
  have heId : weakEquivalences C (𝟙 Y) :=
    IsCylinderCategory.isomorphisms_le_weakEquivalences (C := C) (𝟙 Y)
      (MorphismProperty.isomorphisms.infer_property (𝟙 Y))
  have hjw := IsCylinderCategory.twoOutOfSix (C := C) (j ≫ c) e (𝟙 Y)
    (by simpa using hJwcomp) (by simpa using he)
  have hJw : weakEquivalences C (j ≫ c) := hjw.1
  obtain ⟨r, hr⟩ := IsCylinderCategory.exists_retraction (C := C) (j ≫ c) hJcof hJw
  refine ⟨k ≫ c ≫ r, ?_⟩
  calc
    i ≫ (k ≫ c ≫ r) = (i ≫ k) ≫ c ≫ r := by simp [Category.assoc]
    _ = (f ≫ j) ≫ c ≫ r := by rw [hP.w]
    _ = f := by
      calc
        (f ≫ j) ≫ c ≫ r = f ≫ ((j ≫ c) ≫ r) := by simp [Category.assoc]
        _ = f ≫ 𝟙 X := by rw [hr]
        _ = f := by simp

private theorem existsRelativeCylinder {A B : C} {i : A ⟶ B}
    (hi : cofibrations C i) : Nonempty (RelativeCylinder i) := by
  classical
  letI : HasPushout i i := IsCofibrationCategory.hasPushout (C := C) i i hi
  let P := pushout i i
  let j₀ : B ⟶ P := pushout.inl i i
  let j₁ : B ⟶ P := pushout.inr i i
  let hP : IsPushout i i j₀ j₁ := IsPushout.of_hasPushout i i
  let d : P ⟶ B := hP.desc (𝟙 B) (𝟙 B) (by simp)
  obtain ⟨I, c, p, hc, hp, hcp⟩ := brownFactorization d
  refine ⟨⟨P, j₀, j₁, hP, I, c, p, hc, hp, ?_, ?_⟩⟩
  · calc
      j₀ ≫ c ≫ p = j₀ ≫ (c ≫ p) := by simp [Category.assoc]
      _ = j₀ ≫ d := by rw [hcp]
      _ = 𝟙 B := by simp [j₀, d, hP]
  · calc
      j₁ ≫ c ≫ p = j₁ ≫ (c ≫ p) := by simp [Category.assoc]
      _ = j₁ ≫ d := by rw [hcp]
      _ = 𝟙 B := by simp [j₁, d, hP]

private theorem compareMappedRelativeCylinder {F : C ⥤ D}
    (hF : IsCylinderMorphism F) {A B : C} {i : A ⟶ B} (hi : cofibrations C i)
    (cylC : RelativeCylinder i) (cylD : RelativeCylinder (F.map i)) :
    ∃ g : F.obj cylC.I ⟶ cylD.I,
      F.map (cylC.j₀ ≫ cylC.c) ≫ g = cylD.j₀ ≫ cylD.c ∧
      F.map (cylC.j₁ ≫ cylC.c) ≫ g = cylD.j₁ ≫ cylD.c := by
  let hMap := hF.map_isPushout i i cylC.j₀ cylC.j₁ cylC.isPushout hi
  have hbase : F.map i ≫ cylD.j₀ = F.map i ≫ cylD.j₁ := cylD.isPushout.w
  let top : F.obj cylC.P ⟶ cylD.P := hMap.desc cylD.j₀ cylD.j₁ hbase
  have htop₀ : F.map cylC.j₀ ≫ top = cylD.j₀ :=
    hMap.inl_desc cylD.j₀ cylD.j₁ hbase
  have htop₁ : F.map cylC.j₁ ≫ top = cylD.j₁ :=
    hMap.inr_desc cylD.j₀ cylD.j₁ hbase
  have h0 : cylD.j₀ ≫ cylD.c ≫ cylD.p =
      F.map cylC.j₀ ≫ (top ≫ cylD.c) ≫ cylD.p := by
    calc
      cylD.j₀ ≫ cylD.c ≫ cylD.p =
          (F.map cylC.j₀ ≫ top) ≫ (cylD.c ≫ cylD.p) :=
        congrArg (fun k => k ≫ (cylD.c ≫ cylD.p)) htop₀.symm
      _ = F.map cylC.j₀ ≫ (top ≫ (cylD.c ≫ cylD.p)) :=
        Category.assoc (F.map cylC.j₀) top (cylD.c ≫ cylD.p)
      _ = F.map cylC.j₀ ≫ ((top ≫ cylD.c) ≫ cylD.p) :=
        congrArg (fun k => F.map cylC.j₀ ≫ k) (Category.assoc top cylD.c cylD.p).symm
  have h1 : cylD.j₁ ≫ cylD.c ≫ cylD.p =
      F.map cylC.j₁ ≫ (top ≫ cylD.c) ≫ cylD.p := by
    calc
      cylD.j₁ ≫ cylD.c ≫ cylD.p =
          (F.map cylC.j₁ ≫ top) ≫ (cylD.c ≫ cylD.p) :=
        congrArg (fun k => k ≫ (cylD.c ≫ cylD.p)) htop₁.symm
      _ = F.map cylC.j₁ ≫ (top ≫ (cylD.c ≫ cylD.p)) :=
        Category.assoc (F.map cylC.j₁) top (cylD.c ≫ cylD.p)
      _ = F.map cylC.j₁ ≫ ((top ≫ cylD.c) ≫ cylD.p) :=
        congrArg (fun k => F.map cylC.j₁ ≫ k) (Category.assoc top cylD.c cylD.p).symm
  have hsq : F.map cylC.c ≫ F.map cylC.p = (top ≫ cylD.c) ≫ cylD.p := by
    apply hMap.hom_ext
    · calc
        F.map cylC.j₀ ≫ F.map cylC.c ≫ F.map cylC.p =
            F.map (cylC.j₀ ≫ cylC.c ≫ cylC.p) := by simp
        _ = 𝟙 (F.obj B) := by rw [cylC.j₀_c_p]; simp
        _ = cylD.j₀ ≫ cylD.c ≫ cylD.p := by rw [cylD.j₀_c_p]
        _ = F.map cylC.j₀ ≫ (top ≫ cylD.c) ≫ cylD.p := h0
    · calc
        F.map cylC.j₁ ≫ F.map cylC.c ≫ F.map cylC.p =
            F.map (cylC.j₁ ≫ cylC.c ≫ cylC.p) := by simp
        _ = 𝟙 (F.obj B) := by rw [cylC.j₁_c_p]; simp
        _ = cylD.j₁ ≫ cylD.c ≫ cylD.p := by rw [cylD.j₁_c_p]
        _ = F.map cylC.j₁ ≫ (top ≫ cylD.c) ≫ cylD.p := h1
  obtain ⟨g, hg⟩ := cofibrationLiftsAgainstWeakEquivalence (F.map cylC.c)
    (hF.map_cofibration cylC.c cylC.c_mem) (top ≫ cylD.c) cylD.p (F.map cylC.p)
    hsq cylD.p_mem
  refine ⟨g, ?_, ?_⟩
  · calc
      F.map (cylC.j₀ ≫ cylC.c) ≫ g = F.map cylC.j₀ ≫ (F.map cylC.c ≫ g) := by
        simp only [Functor.map_comp, Category.assoc]
      _ = F.map cylC.j₀ ≫ top ≫ cylD.c := by rw [hg]
      _ = (F.map cylC.j₀ ≫ top) ≫ cylD.c := (Category.assoc _ _ _).symm
      _ = cylD.j₀ ≫ cylD.c := by rw [htop₀]
  · calc
      F.map (cylC.j₁ ≫ cylC.c) ≫ g = F.map cylC.j₁ ≫ (F.map cylC.c ≫ g) := by
        simp only [Functor.map_comp, Category.assoc]
      _ = F.map cylC.j₁ ≫ top ≫ cylD.c := by rw [hg]
      _ = (F.map cylC.j₁ ≫ top) ≫ cylD.c := (Category.assoc _ _ _).symm
      _ = cylD.j₁ ≫ cylD.c := by rw [htop₁]

private def mapRelativeCylinder {F : C ⥤ D}
    (hF : HomotopyHypothesis.Henry.IsCylinderMorphism F)
    {A B : C} {i : A ⟶ B} (hi : cofibrations C i)
    (cyl : HomotopyHypothesis.Henry.RelativeCylinder i) :
    HomotopyHypothesis.Henry.RelativeCylinder (F.map i) where
  P := F.obj cyl.P
  j₀ := F.map cyl.j₀
  j₁ := F.map cyl.j₁
  isPushout := hF.map_isPushout i i cyl.j₀ cyl.j₁ cyl.isPushout hi
  I := F.obj cyl.I
  c := F.map cyl.c
  p := F.map cyl.p
  c_mem := hF.map_cofibration cyl.c cyl.c_mem
  p_mem := hF.map_weakEquivalence cyl.p cyl.p_mem
  j₀_c_p := by simpa using congrArg F.map cyl.j₀_c_p
  j₁_c_p := by simpa using congrArg F.map cyl.j₁_c_p

private theorem completionRestriction_yoneda_weakEquivalence_ofHomotopyFullyFaithful
    {F : C ⥤ D} (hF : HomotopyHypothesis.Henry.IsCylinderMorphism F)
    (hFF : HomotopyHypothesis.Henry.IsHomotopyFullyFaithful F)
    {L : HomotopyHypothesis.Henry.Completion.{w} C ⥤
      HomotopyHypothesis.Henry.Completion.{w} D}
    (adj : L ⊣ HomotopyHypothesis.Henry.Completion.restriction.{w} F
      hF.toIsCofibrationMorphism) (A : C) :
    HomotopyHypothesis.Henry.Completion.weakEquivalences C
      (adj.unit.app ((completionYonedaSmall (C := C)).obj A)) := by
  let yC := completionYonedaSmall (C := C)
  let yD := completionYonedaSmall (C := D)
  let R := HomotopyHypothesis.Henry.Completion.restriction.{w} F
    hF.toIsCofibrationMorphism
  let target := R.obj (L.obj (yC.obj A))
  let iso := completionRestriction_yonedaIso hF adj A
  change HomotopyHypothesis.Henry.presheafWeakEquivalences
    (adj.unit.app (yC.obj A)).hom
  intro U V i hi a b hab
  have hEvalU : (target.obj).obj (op U) =
      ((L.obj (yC.obj A)).obj).obj (op (F.obj U)) :=
    completionRestriction_yonedaEvaluationEq hF.toIsCofibrationMorphism U
      (L.obj (yC.obj A))
  have hEvalV : (target.obj).obj (op V) =
      ((L.obj (yC.obj A)).obj).obj (op (F.obj V)) :=
    completionRestriction_yonedaEvaluationEq hF.toIsCofibrationMorphism V
      (L.obj (yC.obj A))
  let unitD := Equiv.cast
    (completionRestriction_yonedaEvaluationEq hF.toIsCofibrationMorphism U
      (L.obj (yC.obj A))) ((adj.unit.app (yC.obj A)).hom.app (op U) a)
  let bD := Equiv.cast hEvalV b
  let aArrow := completionYonedaElementHomEquiv (C := C) U A a
  let bImage := iso.hom.hom.app (op (F.obj V)) bD
  let bArrow := completionYonedaElementHomEquiv (C := D) (F.obj V) (F.obj A) bImage
  have hMapCast : Equiv.cast hEvalU (target.obj.map i.op b) =
      (L.obj (yC.obj A)).obj.map (F.map i).op bD := by
    rfl
  have hAlpha : iso.hom.hom.app (op (F.obj U)) unitD =
      (yD.obj (F.obj A)).obj.map (F.map i).op bImage := by
    calc
      _ = iso.hom.hom.app (op (F.obj U))
          (Equiv.cast hEvalU (target.obj.map i.op b)) := by
            exact congrArg (iso.hom.hom.app (op (F.obj U))) (congrArg (Equiv.cast hEvalU) hab)
      _ = iso.hom.hom.app (op (F.obj U))
          ((L.obj (yC.obj A)).obj.map (F.map i).op bD) := by rw [hMapCast]
      _ = (yD.obj (F.obj A)).obj.map (F.map i).op bImage := by
            rw [← NatTrans.naturality_apply]
  have hUnit : completionYonedaElementHomEquiv (C := D) (F.obj U) (F.obj A)
      (iso.hom.hom.app (op (F.obj U)) unitD) = F.map aArrow := by
    exact completionRestriction_yonedaUnit_element_cast hF adj A U a
  have hArrow : F.map i ≫ bArrow = F.map aArrow := by
    have h := congrArg (completionYonedaElementHomEquiv (C := D)
      (F.obj U) (F.obj A)) hAlpha
    rw [hUnit, completionYonedaElementHomEquiv_map] at h
    exact h.symm
  obtain ⟨v, hv, hRel⟩ := hFF i hi aArrow bArrow hArrow
  let l := (completionYonedaElementHomEquiv (C := C) V A).symm v
  have hl : (yC.obj A).obj.map i.op l = a := by
    apply (completionYonedaElementHomEquiv (C := C) U A).injective
    calc
      completionYonedaElementHomEquiv (C := C) U A ((yC.obj A).obj.map i.op l) =
          i ≫ completionYonedaElementHomEquiv (C := C) V A l :=
            completionYonedaElementHomEquiv_map (C := C) i l
      _ = aArrow := by simp [l, hv]
      _ = completionYonedaElementHomEquiv (C := C) U A a := rfl
  obtain ⟨cylC⟩ := existsRelativeCylinder hi
  rcases hRel with ⟨cylD, H, h₀, h₁⟩
  obtain ⟨k, hk₀, hk₁⟩ := compareMappedRelativeCylinder hF hi cylC cylD
  let hEvalI := completionRestriction_yonedaEvaluationEq
    hF.toIsCofibrationMorphism cylC.I (L.obj (yC.obj A))
  let hEvalV := completionRestriction_yonedaEvaluationEq
    hF.toIsCofibrationMorphism V (L.obj (yC.obj A))
  let dHom := (completionYonedaElementHomEquiv (C := D) cylD.I (F.obj A)).symm H
  let dElem := (yD.obj (F.obj A)).obj.map k.op dHom
  let hD := iso.inv.hom.app (op (F.obj cylC.I)) dElem
  let h : target.obj.obj (op cylC.I) :=
    (Equiv.cast hEvalI).symm hD
  have hIsoElem : iso.hom.hom.app (op (F.obj cylC.I))
      (Equiv.cast hEvalI h) = dElem := by
    change iso.hom.hom.app (op (F.obj cylC.I))
      (Equiv.cast hEvalI ((Equiv.cast hEvalI).symm hD)) = dElem
    rw [Equiv.apply_symm_apply]
    have h' := congrArg (fun f : yD.obj (F.obj A) ⟶ yD.obj (F.obj A) =>
      f.hom.app (op (F.obj cylC.I)) dElem) iso.inv_hom_id
    change iso.hom.hom.app (op (F.obj cylC.I))
        (iso.inv.hom.app (op (F.obj cylC.I)) dElem) = dElem at h'
    exact h'
  let e₀ := cylC.j₀ ≫ cylC.c
  let e₁ := cylC.j₁ ≫ cylC.c
  have hAlpha₀ : iso.hom.hom.app (op (F.obj V))
      (Equiv.cast hEvalV (target.obj.map e₀.op h)) =
      (yD.obj (F.obj A)).obj.map (F.map e₀).op dElem := by
    have hMapCast : Equiv.cast hEvalV (target.obj.map e₀.op h) =
        (L.obj (yC.obj A)).obj.map (F.map e₀).op (Equiv.cast hEvalI h) := by
      cases hEvalV
      cases hEvalI
      rfl
    calc
      _ = (yD.obj (F.obj A)).obj.map (F.map e₀).op
          (iso.hom.hom.app (op (F.obj cylC.I)) (Equiv.cast hEvalI h)) := by
            rw [hMapCast]
            rw [← NatTrans.naturality_apply]
      _ = (yD.obj (F.obj A)).obj.map (F.map e₀).op dElem := by rw [hIsoElem]
  have hEndpoint₀Arrow : completionYonedaElementHomEquiv (C := D)
      (F.obj V) (F.obj A) ((yD.obj (F.obj A)).obj.map (F.map e₀).op dElem) = F.map v := by
    calc
      completionYonedaElementHomEquiv (C := D) (F.obj V) (F.obj A)
          ((yD.obj (F.obj A)).obj.map (F.map e₀).op dElem) =
          F.map e₀ ≫ completionYonedaElementHomEquiv (C := D)
            (F.obj cylC.I) (F.obj A) dElem :=
              completionYonedaElementHomEquiv_map (C := D) (F.map e₀) dElem
      _ = F.map e₀ ≫ (k ≫ H) := by
            rw [completionYonedaElementHomEquiv_map (C := D) k dHom]
            simp [dHom]
      _ = (F.map e₀ ≫ k) ≫ H := by simp [Category.assoc]
      _ = (cylD.j₀ ≫ cylD.c) ≫ H := by rw [hk₀]
      _ = F.map v := by simpa [Category.assoc] using h₀
  let unitV := (adj.unit.app (yC.obj A)).hom.app (op V) l
  let unitVD := Equiv.cast
    (completionRestriction_yonedaEvaluationEq hF.toIsCofibrationMorphism V
      (L.obj (yC.obj A))) unitV
  have hUnitV : completionYonedaElementHomEquiv (C := D) (F.obj V) (F.obj A)
      (iso.hom.hom.app (op (F.obj V)) unitVD) = F.map v := by
    have h := completionRestriction_yonedaUnit_element_cast hF adj A V l
    rw [(completionYonedaElementHomEquiv (C := C) V A).apply_symm_apply] at h
    exact h
  have hEndpoint₀Elem : (yD.obj (F.obj A)).obj.map (F.map e₀).op dElem =
      iso.hom.hom.app (op (F.obj V)) unitVD := by
    apply (completionYonedaElementHomEquiv (C := D) (F.obj V) (F.obj A)).injective
    calc
      completionYonedaElementHomEquiv (C := D) (F.obj V) (F.obj A)
          ((yD.obj (F.obj A)).obj.map (F.map e₀).op dElem) = F.map v :=
            hEndpoint₀Arrow
      _ = completionYonedaElementHomEquiv (C := D) (F.obj V) (F.obj A)
          (iso.hom.hom.app (op (F.obj V)) unitVD) := hUnitV.symm
  have hAlphaInjective : Function.Injective (iso.hom.hom.app (op (F.obj V))) := by
    have hbij : Function.Bijective (iso.hom.hom.app (op (F.obj V))) :=
      (CategoryTheory.isIso_iff_bijective _).1 (by infer_instance)
    exact hbij.1
  have h₀raw : target.obj.map e₀.op h =
      (adj.unit.app (yC.obj A)).hom.app (op V) l := by
    have hCast := hAlphaInjective (hAlpha₀.trans hEndpoint₀Elem)
    exact (Equiv.cast hEvalV).injective hCast
  have hAlpha₁ : iso.hom.hom.app (op (F.obj V))
      (Equiv.cast hEvalV (target.obj.map e₁.op h)) =
      (yD.obj (F.obj A)).obj.map (F.map e₁).op dElem := by
    have hMapCast : Equiv.cast hEvalV (target.obj.map e₁.op h) =
        (L.obj (yC.obj A)).obj.map (F.map e₁).op (Equiv.cast hEvalI h) := by
      cases hEvalV
      cases hEvalI
      rfl
    calc
      _ = (yD.obj (F.obj A)).obj.map (F.map e₁).op
          (iso.hom.hom.app (op (F.obj cylC.I)) (Equiv.cast hEvalI h)) := by
            rw [hMapCast]
            rw [← NatTrans.naturality_apply]
      _ = (yD.obj (F.obj A)).obj.map (F.map e₁).op dElem := by rw [hIsoElem]
  have hEndpoint₁Arrow : completionYonedaElementHomEquiv (C := D)
      (F.obj V) (F.obj A) ((yD.obj (F.obj A)).obj.map (F.map e₁).op dElem) = bArrow := by
    calc
      completionYonedaElementHomEquiv (C := D) (F.obj V) (F.obj A)
          ((yD.obj (F.obj A)).obj.map (F.map e₁).op dElem) =
          F.map e₁ ≫ completionYonedaElementHomEquiv (C := D)
            (F.obj cylC.I) (F.obj A) dElem :=
              completionYonedaElementHomEquiv_map (C := D) (F.map e₁) dElem
      _ = F.map e₁ ≫ (k ≫ H) := by
            rw [completionYonedaElementHomEquiv_map (C := D) k dHom]
            simp [dHom]
      _ = (F.map e₁ ≫ k) ≫ H := by simp [Category.assoc]
      _ = (cylD.j₁ ≫ cylD.c) ≫ H := by rw [hk₁]
      _ = bArrow := by simpa [Category.assoc] using h₁
  have hEndpoint₁Elem : (yD.obj (F.obj A)).obj.map (F.map e₁).op dElem =
      bImage := by
    apply (completionYonedaElementHomEquiv (C := D) (F.obj V) (F.obj A)).injective
    calc
      completionYonedaElementHomEquiv (C := D) (F.obj V) (F.obj A)
          ((yD.obj (F.obj A)).obj.map (F.map e₁).op dElem) = bArrow := hEndpoint₁Arrow
      _ = completionYonedaElementHomEquiv (C := D) (F.obj V) (F.obj A)
          bImage := rfl
  have h₁raw : target.obj.map e₁.op h = b := by
    have hEq : iso.hom.hom.app (op (F.obj V))
        (Equiv.cast hEvalV (target.obj.map e₁.op h)) =
        iso.hom.hom.app (op (F.obj V)) bD := by
      change iso.hom.hom.app (op (F.obj V))
          (Equiv.cast hEvalV (target.obj.map e₁.op h)) = bImage
      exact hAlpha₁.trans hEndpoint₁Elem
    have hCast := hAlphaInjective hEq
    exact (Equiv.cast hEvalV).injective hCast
  exact ⟨l, cylC, h, hl, h₀raw, h₁raw⟩

private noncomputable def completionRestriction_preservesFilteredColimit
    {F : C ⥤ D} (hF : HomotopyHypothesis.Henry.IsCofibrationMorphism F)
    {J : Type w} [SmallCategory J] [IsFiltered J]
    {G : J ⥤ HomotopyHypothesis.Henry.Completion.{w} D}
    {c : Cocone G} (hc : IsColimit c) :
    IsColimit ((HomotopyHypothesis.Henry.Completion.restriction.{w} F hF).mapCocone c) := by
  classical
  let R := HomotopyHypothesis.Henry.Completion.restriction.{w} F hF
  let P_C := HomotopyHypothesis.Henry.IsCompletionPresheaf.{w} C
  let ι_C := ObjectProperty.ι P_C
  let cR := R.mapCocone c
  have hRaw : IsColimit (ι_C.mapCocone cR) := by
    apply evaluationJointlyReflectsColimits
    intro A
    cases A with
    | op A =>
      let evalC := (evaluation Cᵒᵖ (Type w)).obj (op A)
      let evalD := ObjectProperty.ι (HomotopyHypothesis.Henry.IsCompletionPresheaf.{w} D) ⋙
        (evaluation Dᵒᵖ (Type w)).obj (op (F.obj A))
      have hA := Classical.choice
        (HomotopyHypothesis.Category.SemiModelStructure.completion_isColimit_evaluation hc (F.obj A))
      have hCoc : evalC.mapCocone (ι_C.mapCocone cR) ≅ evalD.mapCocone c := by
        refine Cocone.ext (Iso.refl _) ?_
        intro j
        rfl
      exact IsColimit.ofIsoColimit hA hCoc.symm
  letI : ι_C.FullyFaithful := ObjectProperty.fullyFaithfulι _
  exact isColimitOfReflects ι_C hRaw

private theorem solCompletionSmallYonedaHomEquiv_comp_right (A : C)
    {X Y : HomotopyHypothesis.Henry.Completion.{w} C}
    (g : X ⟶ Y)
    (f : (HomotopyHypothesis.Category.SemiModelConstruction.completionSmallYoneda.{w} (C := C)).obj A ⟶ X) :
    HomotopyHypothesis.Category.SemiModelConstruction.completionSmallYonedaHomEquiv A Y (f ≫ g) =
      g.hom.app (op A)
        (HomotopyHypothesis.Category.SemiModelConstruction.completionSmallYonedaHomEquiv A X f) := by
  change shrinkYonedaEquiv (f.hom ≫ g.hom) =
    g.hom.app (op A) (shrinkYonedaEquiv f.hom)
  rw [shrinkYonedaEquiv_comp]

private noncomputable def solCompletionSmallYonedaIso (A : C) :
    (HomotopyHypothesis.Category.SemiModelConstruction.completionSmallYoneda.{w} (C := C)).obj A ≅
      (completionYonedaSmall (C := C)).obj A := by
  let ySol := HomotopyHypothesis.Category.SemiModelConstruction.completionSmallYoneda.{w} (C := C)
  let y := completionYonedaSmall (C := C)
  let e : ∀ Y : HomotopyHypothesis.Henry.Completion.{w} C,
      (ySol.obj A ⟶ Y) ≃ (y.obj A ⟶ Y) := fun Y =>
    (HomotopyHypothesis.Category.SemiModelConstruction.completionSmallYonedaHomEquiv A Y).trans
      (completionYonedaSmallEquiv (C := C) A Y).symm
  exact isoOfHomEquiv e (by
    intro Y Z g f
    change (completionYonedaSmallEquiv (C := C) A Z).symm
        (HomotopyHypothesis.Category.SemiModelConstruction.completionSmallYonedaHomEquiv A Z (f ≫ g)) =
      (completionYonedaSmallEquiv (C := C) A Y).symm
        (HomotopyHypothesis.Category.SemiModelConstruction.completionSmallYonedaHomEquiv A Y f) ≫ g
    apply (completionYonedaSmallEquiv (C := C) A Z).injective
    rw [completionYonedaSmallEquiv_comp_right]
    simp only [Equiv.apply_symm_apply]
    exact solCompletionSmallYonedaHomEquiv_comp_right A g f)

private theorem completionAdjunctionUnit_isWeakEquivalence_ofFlat
    {F : C ⥤ D} (hF : HomotopyHypothesis.Henry.IsCylinderMorphism F)
    (hFF : HomotopyHypothesis.Henry.IsHomotopyFullyFaithful F)
    {L : HomotopyHypothesis.Henry.Completion.{w} C ⥤
      HomotopyHypothesis.Henry.Completion.{w} D}
    (adj : L ⊣ HomotopyHypothesis.Henry.Completion.restriction.{w} F
      hF.toIsCofibrationMorphism)
    {X : HomotopyHypothesis.Henry.Completion.{w} C}
    (hX : HomotopyHypothesis.Category.SemiModelStructure.IsFlat X) :
    HomotopyHypothesis.Henry.Completion.weakEquivalences C (adj.unit.app X) := by
  classical
  obtain ⟨J, hJsmall, hJfiltered, pres, hRep⟩ := hX
  letI : SmallCategory J := hJsmall
  letI : IsFiltered J := hJfiltered
  let W := HomotopyHypothesis.Henry.Completion.weakEquivalences C
  let hSemi := HomotopyHypothesis.Henry.Packages.completion_isSemiModelCategory (C := C)
  letI : W.HasTwoOutOfThreeProperty := hSemi.1.twoOutOfThree
  letI : W.ContainsIdentities :=
    ⟨fun X => HomotopyHypothesis.Category.SemiModelStructure.completion_weakEquivalence_id X⟩
  letI : W.RespectsIso := HomotopyHypothesis.Henry.Completion.weakEquivalences_respectsIso C
  let G : J ⥤ HomotopyHypothesis.Henry.Completion.{w} C := pres.diag
  have hStage : ∀ j : J, W (adj.unit.app (G.obj j)) := by
    intro j
    obtain ⟨A, ⟨e⟩⟩ := hRep j
    let e' := e ≪≫ solCompletionSmallYonedaIso (C := C) A
    have hRepUnit : W
        (adj.unit.app ((completionYonedaSmall (C := C)).obj A)) :=
      completionRestriction_yoneda_weakEquivalence_ofHomotopyFullyFaithful hF hFF adj A
    have hIso : W e'.hom := W.of_isIso e'.hom
    have hIsoMap : W ((L ⋙ HomotopyHypothesis.Henry.Completion.restriction.{w} F
      hF.toIsCofibrationMorphism).map e'.hom) :=
        W.of_isIso _
    have hRight : W (e'.hom ≫ adj.unit.app ((completionYonedaSmall (C := C)).obj A)) :=
      W.comp_mem e'.hom (adj.unit.app ((completionYonedaSmall (C := C)).obj A)) hIso hRepUnit
    have hNat : e'.hom ≫ adj.unit.app ((completionYonedaSmall (C := C)).obj A) =
        adj.unit.app (G.obj j) ≫
          (L ⋙ HomotopyHypothesis.Henry.Completion.restriction.{w} F
            hF.toIsCofibrationMorphism).map e'.hom := by
      simpa using adj.unit.naturality e'.hom
    have hLeft : W (adj.unit.app (G.obj j) ≫
        (L ⋙ HomotopyHypothesis.Henry.Completion.restriction.{w} F
          hF.toIsCofibrationMorphism).map e'.hom) := by
      rw [← hNat]
      exact hRight
    exact W.of_postcomp (adj.unit.app (G.obj j))
      ((L ⋙ HomotopyHypothesis.Henry.Completion.restriction.{w} F
        hF.toIsCofibrationMorphism).map e'.hom) hIsoMap hLeft
  let cL := L.mapCocone pres.cocone
  letI : PreservesColimitsOfShape J L :=
    adj.leftAdjoint_preservesColimits.preservesColimitsOfShape
  have hcL : IsColimit cL := isColimitOfPreserves L pres.isColimit
  let R := HomotopyHypothesis.Henry.Completion.restriction.{w} F
    hF.toIsCofibrationMorphism
  let cR := R.mapCocone cL
  have hcR : IsColimit cR := completionRestriction_preservesFilteredColimit
    hF.toIsCofibrationMorphism hcL
  let t : G ⟶ (G ⋙ L) ⋙ R :=
    { app := fun j => adj.unit.app (G.obj j)
      naturality := by
        intro j j' f
        exact adj.unit.naturality (G.map f) }
  have hu (j : J) : pres.ι.app j ≫ adj.unit.app X = t.app j ≫ cR.ι.app j := by
    dsimp [t, cR, cL]
    exact adj.unit.naturality (pres.ι.app j)
  exact HomotopyHypothesis.Category.SemiModelStructure.completion_weakEquivalence_of_isColimit
    t hStage pres.isColimit hcR (adj.unit.app X) hu

private theorem completionAdjunctionUnit_isWeakEquivalence_ofCofibrant
    {F : C ⥤ D} (hF : HomotopyHypothesis.Henry.IsCylinderMorphism F)
    (hFF : HomotopyHypothesis.Henry.IsHomotopyFullyFaithful F)
    {L : HomotopyHypothesis.Henry.Completion.{w} C ⥤
      HomotopyHypothesis.Henry.Completion.{w} D}
    (adj : L ⊣ HomotopyHypothesis.Henry.Completion.restriction.{w} F
      hF.toIsCofibrationMorphism)
    {X : HomotopyHypothesis.Henry.Completion.{w} C}
    (hX : IsCofibrantFor (HomotopyHypothesis.Henry.Completion.cofibrations C) X) :
    HomotopyHypothesis.Henry.Completion.weakEquivalences C (adj.unit.app X) :=
  completionAdjunctionUnit_isWeakEquivalence_ofFlat hF hFF adj
    (HomotopyHypothesis.Category.SemiModelStructure.isFlat_of_isCofibrant hX)

private theorem homotopic_compRight {E : Type u} [Category.{v} E]
    [CategoryWithCofibrations E] [CategoryWithWeakEquivalences E]
    [HomotopyHypothesis.Henry.IsCylinderCategory E]
    {A X Y : E} {f g : A ⟶ X}
    (h : HomotopyHypothesis.Henry.Homotopic f g) (k : X ⟶ Y) :
    HomotopyHypothesis.Henry.Homotopic (f ≫ k) (g ≫ k) := by
  obtain ⟨I, hI, ⟨cyl, H, h₀, h₁⟩⟩ := h
  refine ⟨I, hI, ⟨cyl, H ≫ k, ?_, ?_⟩⟩
  · calc
      cyl.j₀ ≫ cyl.c ≫ (H ≫ k) = (cyl.j₀ ≫ cyl.c ≫ H) ≫ k := by simp [Category.assoc]
      _ = f ≫ k := by rw [h₀]
  · calc
      cyl.j₁ ≫ cyl.c ≫ (H ≫ k) = (cyl.j₁ ≫ cyl.c ≫ H) ≫ k := by simp [Category.assoc]
      _ = g ≫ k := by rw [h₁]

private theorem homotopic_compLeft {E : Type u} [Category.{v} E]
    [CategoryWithCofibrations E] [CategoryWithWeakEquivalences E]
    [HomotopyHypothesis.Henry.IsCylinderCategory E]
    {A B X : E} (k : A ⟶ B) {f g : B ⟶ X}
    (h : HomotopyHypothesis.Henry.Homotopic f g) :
    HomotopyHypothesis.Henry.Homotopic (k ≫ f) (k ≫ g) := by
  obtain ⟨I, hI, h⟩ := h
  let i := hI.to B
  let i' := hI.to A
  have hs : i' ≫ k = (𝟙 I) ≫ i := by
    apply hI.hom_ext
  have hi' : cofibrations E i' := IsCofibrationCategory.initial_cofibration hI A
  exact ⟨I, hI, HomotopyHypothesis.Category.SemiModelStructure.relHomotopic_precomp
    i i' (𝟙 I) k hs hi' h⟩

private theorem homotopic_symm {E : Type u} [Category.{v} E]
    [CategoryWithCofibrations E] [CategoryWithWeakEquivalences E]
    [HomotopyHypothesis.Henry.IsCylinderCategory E]
    {A X : E} {f g : A ⟶ X}
    (h : HomotopyHypothesis.Henry.Homotopic f g) :
    HomotopyHypothesis.Henry.Homotopic g f := by
  obtain ⟨I, hI, h⟩ := h
  let i := hI.to A
  let hi : cofibrations E i := IsCofibrationCategory.initial_cofibration hI A
  exact ⟨I, hI, (HomotopyHypothesis.Henry.Packages.relHomotopic_equivalence i hi).1.symm h⟩

private theorem homotopic_trans {E : Type u} [Category.{v} E]
    [CategoryWithCofibrations E] [CategoryWithWeakEquivalences E]
    [HomotopyHypothesis.Henry.IsCylinderCategory E]
    {A X : E} {f g h : A ⟶ X}
    (hfg : HomotopyHypothesis.Henry.Homotopic f g)
    (hgh : HomotopyHypothesis.Henry.Homotopic g h) :
    HomotopyHypothesis.Henry.Homotopic f h := by
  obtain ⟨I, hI, hfg⟩ := hfg
  obtain ⟨I', hI', hgh⟩ := hgh
  let i := hI.to A
  let i' := hI'.to A
  let e : I ⟶ I' := hI.to I'
  have hs : i ≫ 𝟙 A = e ≫ i' := by
    apply hI.hom_ext
  have hi : cofibrations E i := IsCofibrationCategory.initial_cofibration hI A
  have hgh' := HomotopyHypothesis.Category.SemiModelStructure.relHomotopic_precomp
    i' i e (𝟙 A) hs hi hgh
  have hgh'' : RelHomotopic i g h := by simpa using hgh'
  exact ⟨I, hI, (HomotopyHypothesis.Henry.Packages.relHomotopic_equivalence i hi).1.trans
    hfg hgh''⟩

private theorem completionWeakEquivalence_ofHomotopic {E : Type u} [Category.{v} E]
    [CategoryWithCofibrations E] [CategoryWithWeakEquivalences E]
    [HomotopyHypothesis.Henry.IsCylinderCategory E]
    {A B : E} {f g : A ⟶ B}
    (hf : weakEquivalences E f)
    (hfg : HomotopyHypothesis.Henry.Homotopic f g) :
    weakEquivalences E g := by
  obtain ⟨k, hfk, hkf⟩ :=
    (HomotopyHypothesis.Henry.Packages.weakEquivalence_iff f).mp hf
  have hgk : HomotopyHypothesis.Henry.Homotopic (g ≫ k) (𝟙 A) := by
    exact homotopic_trans (homotopic_symm (homotopic_compRight hfg k)) hfk
  have hkg : HomotopyHypothesis.Henry.Homotopic (k ≫ g) (𝟙 B) := by
    exact homotopic_trans
      (homotopic_symm
        (homotopic_compLeft (A := B) (B := A) (X := B) k hfg)) hkf
  exact (HomotopyHypothesis.Henry.Packages.weakEquivalence_iff g).mpr ⟨k, hgk, hkg⟩

private theorem completionWeakEquivalence_inverse {E : Type u} [Category.{v} E]
    [CategoryWithCofibrations E] [CategoryWithWeakEquivalences E]
    [HomotopyHypothesis.Henry.IsCylinderCategory E]
    {A B : E} (f : A ⟶ B) (hf : weakEquivalences E f) :
    ∃ g : B ⟶ A, weakEquivalences E g ∧
      HomotopyHypothesis.Henry.Homotopic (f ≫ g) (𝟙 A) ∧
      HomotopyHypothesis.Henry.Homotopic (g ≫ f) (𝟙 B) := by
  obtain ⟨g, hfg, hgf⟩ :=
    (HomotopyHypothesis.Henry.Packages.weakEquivalence_iff f).mp hf
  have hid : weakEquivalences E (𝟙 A) :=
    HomotopyHypothesis.Henry.IsCylinderCategory.isomorphisms_le_weakEquivalences
      (C := E) (𝟙 A) (MorphismProperty.isomorphisms.infer_property (𝟙 A))
  have hfgW := completionWeakEquivalence_ofHomotopic hid (homotopic_symm hfg)
  have hgfW := completionWeakEquivalence_ofHomotopic
    (HomotopyHypothesis.Henry.IsCylinderCategory.isomorphisms_le_weakEquivalences
      (C := E) (𝟙 B) (MorphismProperty.isomorphisms.infer_property (𝟙 B)))
    (homotopic_symm hgf)
  have hg := (HomotopyHypothesis.Henry.IsCylinderCategory.twoOutOfSix
    (C := E) (𝟙 A) f g (by simpa using hf) (by simpa using hfgW)).2.2.1
  exact ⟨g, hg, hfg, hgf⟩

private theorem homotopic_of_relHomotopic {E : Type u} [Category.{v} E]
    [CategoryWithCofibrations E] [CategoryWithWeakEquivalences E]
    [HomotopyHypothesis.Henry.IsCylinderCategory E]
    {A B X : E} (i : A ⟶ B) (hi : cofibrations E i) {f g : B ⟶ X}
    (h : HomotopyHypothesis.Henry.RelHomotopic i f g) :
    HomotopyHypothesis.Henry.Homotopic f g := by
  obtain ⟨O, hOne⟩ := IsCofibrationCategory.exists_initial (C := E)
  let hO : IsInitial O := Classical.choice hOne
  let i₀ := hO.to B
  have hi₀ : cofibrations E i₀ := IsCofibrationCategory.initial_cofibration hO B
  have hsq : i₀ ≫ 𝟙 B = hO.to A ≫ i := by
    apply hO.hom_ext
  have h' := HomotopyHypothesis.Category.SemiModelStructure.relHomotopic_precomp
    i i₀ (hO.to A) (𝟙 B) hsq hi₀ h
  exact ⟨O, hO, by simpa using h'⟩

private theorem relHomotopic_postcomp {E : Type u} [Category.{v} E]
    [CategoryWithCofibrations E] [CategoryWithWeakEquivalences E]
    {A B X Y : E} {i : A ⟶ B} {f g : B ⟶ X}
    (h : HomotopyHypothesis.Henry.RelHomotopic i f g) (k : X ⟶ Y) :
    HomotopyHypothesis.Henry.RelHomotopic i (f ≫ k) (g ≫ k) := by
  obtain ⟨cyl, H, h₀, h₁⟩ := h
  refine ⟨cyl, H ≫ k, ?_, ?_⟩
  · calc
      cyl.j₀ ≫ cyl.c ≫ (H ≫ k) = (cyl.j₀ ≫ cyl.c ≫ H) ≫ k := by simp [Category.assoc]
      _ = f ≫ k := by rw [h₀]
  · calc
      cyl.j₁ ≫ cyl.c ≫ (H ≫ k) = (cyl.j₁ ≫ cyl.c ≫ H) ≫ k := by simp [Category.assoc]
      _ = g ≫ k := by rw [h₁]

private theorem exists_imageCofibration_homotopySquare {F : C ⥤ D}
    (hF : HomotopyHypothesis.Henry.IsCylinderMorphism F)
    (hac : HomotopyHypothesis.Henry.IsAcyclic F)
    {A B : D} (i : A ⟶ B) (hi : cofibrations D i) :
    ∃ (A' B' : C) (j : A' ⟶ B'),
      cofibrations C j ∧
      ∃ (u : F.obj A' ⟶ A) (hu : weakEquivalences D u)
        (v : F.obj B' ⟶ B) (hv : weakEquivalences D v),
        HomotopyHypothesis.Henry.Homotopic (F.map j ≫ v) (u ≫ i) := by
  obtain ⟨A', wA, hwA⟩ := hac.1 A
  obtain ⟨B', wB, hwB⟩ := hac.1 B
  obtain ⟨uA, huA, hAwA, hAwu⟩ := completionWeakEquivalence_inverse wA hwA
  obtain ⟨uB, huB, hBwB, hBwu⟩ := completionWeakEquivalence_inverse wB hwB
  let gD : F.obj A' ⟶ F.obj B' := uA ≫ i ≫ wB
  obtain ⟨I, hIne⟩ :=
    HomotopyHypothesis.Henry.IsCofibrationCategory.exists_initial (C := C)
  let hI : IsInitial I := Classical.choice hIne
  let i₀ := hI.to A'
  have hi₀ : cofibrations C i₀ :=
    HomotopyHypothesis.Henry.IsCofibrationCategory.initial_cofibration hI A'
  let hFI : IsInitial (F.obj I) := Classical.choice (hF.map_initial hI)
  have hbase : F.map i₀ ≫ gD = F.map (hI.to B') := by
    apply hFI.hom_ext
  obtain ⟨g, hg, hHomRel⟩ := hac.2 i₀ hi₀ (hI.to B') gD hbase
  have hInitialMap : F.map i₀ = hFI.to (F.obj A') := hFI.hom_ext _ _
  have hHom : HomotopyHypothesis.Henry.Homotopic (F.map g) gD := by
    refine ⟨F.obj I, hFI, ?_⟩
    rw [← hInitialMap]
    exact hHomRel
  obtain ⟨Q, j, p, hj, hp, hjp⟩ :=
    HomotopyHypothesis.Category.SemiModelStructure.brown_factorization g
  have hFp := hF.map_weakEquivalence p hp
  have hK : weakEquivalences D (F.map p ≫ uB) :=
    (HomotopyHypothesis.Henry.IsCylinderCategory.weakEquivalences_isMultiplicative
      (C := D)).comp_mem _ _ hFp huB
  obtain ⟨t, ht, hKt, htK⟩ := completionWeakEquivalence_inverse (F.map p ≫ uB) hK
  have hPost := homotopic_compRight hHom uB
  have hPre := homotopic_compLeft wA hPost
  have h1 : HomotopyHypothesis.Henry.Homotopic
      (wA ≫ F.map g ≫ uB) ((wA ≫ uA) ≫ i ≫ wB ≫ uB) := by
    simpa [gD, Category.assoc] using hPre
  have h2 : HomotopyHypothesis.Henry.Homotopic
      ((wA ≫ uA) ≫ i ≫ wB ≫ uB) (i ≫ wB ≫ uB) := by
    have h := homotopic_compRight hAwA (i ≫ wB ≫ uB)
    simpa [Category.assoc] using h
  have h3 : HomotopyHypothesis.Henry.Homotopic (i ≫ wB ≫ uB) i := by
    simpa [Category.assoc] using homotopic_compLeft i hBwB
  have hFactor : wA ≫ F.map g ≫ uB = wA ≫ F.map j ≫ (F.map p ≫ uB) := by
    simp only [← Functor.map_comp, ← hjp, Functor.map_comp, Category.assoc]
  have hbaseHom : HomotopyHypothesis.Henry.Homotopic
      (wA ≫ F.map j ≫ (F.map p ≫ uB)) i := by
    rw [← hFactor]
    exact homotopic_trans h1 (homotopic_trans h2 h3)
  have hCancel : HomotopyHypothesis.Henry.Homotopic
      ((wA ≫ F.map j) ≫ ((F.map p ≫ uB) ≫ t)) (wA ≫ F.map j) := by
    have h := homotopic_compLeft (wA ≫ F.map j) hKt
    simpa [Category.assoc] using h
  have hSquare : HomotopyHypothesis.Henry.Homotopic (wA ≫ F.map j) (i ≫ t) := by
    have h := homotopic_compRight hbaseHom t
    have h' : HomotopyHypothesis.Henry.Homotopic
        ((wA ≫ F.map j) ≫ (F.map p ≫ uB) ≫ t) (i ≫ t) := by
      simpa [Category.assoc] using h
    exact homotopic_trans (homotopic_symm hCancel) h'
  have hPre := homotopic_compLeft uA hSquare
  have hPost := homotopic_compRight hPre (F.map p ≫ uB)
  have hCancelLeft : HomotopyHypothesis.Henry.Homotopic
      (uA ≫ wA ≫ F.map j ≫ (F.map p ≫ uB)) (F.map j ≫ (F.map p ≫ uB)) := by
    have h := homotopic_compRight hAwu (F.map j ≫ (F.map p ≫ uB))
    simpa [Category.assoc] using h
  have hCancelRight : HomotopyHypothesis.Henry.Homotopic
      (uA ≫ i ≫ t ≫ (F.map p ≫ uB)) (uA ≫ i) := by
    have h := homotopic_compLeft (uA ≫ i) htK
    simpa [Category.assoc] using h
  have hSquareInv : HomotopyHypothesis.Henry.Homotopic
      (F.map j ≫ (F.map p ≫ uB)) (uA ≫ i) := by
    have hPost' : HomotopyHypothesis.Henry.Homotopic
        (uA ≫ wA ≫ F.map j ≫ (F.map p ≫ uB))
        (uA ≫ i ≫ t ≫ (F.map p ≫ uB)) := by
      simpa [Category.assoc] using hPost
    exact homotopic_trans (homotopic_symm hCancelLeft)
      (homotopic_trans hPost' hCancelRight)
  exact ⟨A', Q, j, hj, uA, huA, F.map p ≫ uB, hK, hSquareInv⟩

private abbrev completionRelativeBoundary {E : Type u₁} [Category.{v₁} E]
    [CategoryWithCofibrations E] {X : HomotopyHypothesis.Henry.Completion.{w} E}
    {A B : E} (i : A ⟶ B) (a : X.obj.obj (op A)) :=
  { b : X.obj.obj (op B) // X.obj.map i.op b = a }

private def completionRelativeBoundarySetoid {E : Type u₁} [Category.{v₁} E]
    [CategoryWithCofibrations E] [CategoryWithWeakEquivalences E]
    [HomotopyHypothesis.Henry.IsCylinderCategory E]
    {X : HomotopyHypothesis.Henry.Completion.{w} E} {A B : E}
    (i : A ⟶ B) (hi : cofibrations E i) (a : X.obj.obj (op A)) :
    Setoid (completionRelativeBoundary i a) where
  r x y := HomotopyHypothesis.Category.SemiModelConstruction.PresheafRelHomotopic i X x.1 y.1
  iseqv := by
    let e := HomotopyHypothesis.Category.SemiModelConstruction.presheafRelHomotopic_equivalence i hi X
    exact ⟨fun x => e.refl x.1, fun h => e.symm h, fun h₁ h₂ => e.trans h₁ h₂⟩

private def completionRelativeClassMap {E : Type u₁} [Category.{v₁} E]
    [CategoryWithCofibrations E] [CategoryWithWeakEquivalences E]
    [HomotopyHypothesis.Henry.IsCylinderCategory E]
    {X Y : HomotopyHypothesis.Henry.Completion.{w} E} (f : X ⟶ Y)
    {A B : E} (i : A ⟶ B) (hi : cofibrations E i) (a : X.obj.obj (op A)) :
    Quotient (completionRelativeBoundarySetoid i hi a) →
      Quotient (completionRelativeBoundarySetoid i hi (f.hom.app (op A) a)) :=
  Quotient.map
    (fun x => ⟨f.hom.app (op B) x.1, by
      calc
        Y.obj.map i.op (f.hom.app (op B) x.1) =
            f.hom.app (op A) (X.obj.map i.op x.1) := by
              rw [← NatTrans.naturality_apply]
        _ = f.hom.app (op A) a := congrArg (f.hom.app (op A)) x.2⟩)
    (by
      intro x y hxy
      exact HomotopyHypothesis.Category.SemiModelConstruction.presheafRelHomotopic_map f hxy)

private def completionRelativeClassPrecomp {E : Type u₁} [Category.{v₁} E]
    [CategoryWithCofibrations E] [CategoryWithWeakEquivalences E]
    [HomotopyHypothesis.Henry.IsCylinderCategory E]
    {X : HomotopyHypothesis.Henry.Completion.{w} E}
    {A B A' B' : E} {i : A ⟶ B} {i' : A' ⟶ B'}
    (a : A' ⟶ A) (v : B' ⟶ B) (hsq : i' ≫ v = a ≫ i)
    (hi : cofibrations E i) (hi' : cofibrations E i')
    (x : X.obj.obj (op A)) (x' : X.obj.obj (op A'))
    (hx : X.obj.map a.op x = x') :
    Quotient (completionRelativeBoundarySetoid i hi x) →
      Quotient (completionRelativeBoundarySetoid i' hi' x') :=
  Quotient.map
    (fun y => ⟨X.obj.map v.op y.1, by
      calc
        X.obj.map i'.op (X.obj.map v.op y.1) = X.obj.map (i' ≫ v).op y.1 :=
          (HomotopyHypothesis.Category.SemiModelStructure.presheafMap_comp_apply X i' v y.1).symm
        _ = X.obj.map (a ≫ i).op y.1 := congrArg (fun q => X.obj.map q.op y.1) hsq
        _ = X.obj.map a.op (X.obj.map i.op y.1) :=
          HomotopyHypothesis.Category.SemiModelStructure.presheafMap_comp_apply X a i y.1
        _ = x' := (congrArg (X.obj.map a.op) y.2).trans hx⟩)
    (by
      intro y z hyz
      exact HomotopyHypothesis.Category.SemiModelStructure.presheafRelHomotopic_precomp
        a v hsq hi' hyz)

private theorem completionRelativeClassPrecomp_natural
    {E : Type u₁} [Category.{v₁} E] [CategoryWithCofibrations E]
    [CategoryWithWeakEquivalences E] [HomotopyHypothesis.Henry.IsCylinderCategory E]
    {X Y : HomotopyHypothesis.Henry.Completion.{w} E} (F : X ⟶ Y)
    {A B A' B' : E} {i : A ⟶ B} {i' : A' ⟶ B'}
    (a : A' ⟶ A) (v : B' ⟶ B) (hsq : i' ≫ v = a ≫ i)
    (hi : cofibrations E i) (hi' : cofibrations E i')
    (x : X.obj.obj (op A)) (x' : X.obj.obj (op A'))
    (hx : X.obj.map a.op x = x') :
    (completionRelativeClassMap F i' hi' x') ∘
        (completionRelativeClassPrecomp (X := X) a v hsq hi hi' x x' hx) =
      (completionRelativeClassPrecomp (X := Y) a v hsq hi hi'
        (F.hom.app (op A) x) (F.hom.app (op A') x') (by
          calc
            Y.obj.map a.op (F.hom.app (op A) x) =
                F.hom.app (op A') (X.obj.map a.op x) := by
                  rw [← NatTrans.naturality_apply]
            _ = F.hom.app (op A') x' := congrArg (F.hom.app (op A')) hx)) ∘
        (completionRelativeClassMap F i hi x) := by
  funext q
  induction q using Quotient.inductionOn with
  | _ y =>
    apply Quotient.sound
    change HomotopyHypothesis.Category.SemiModelConstruction.PresheafRelHomotopic i' Y
      (F.hom.app (op B') (X.obj.map v.op y.1))
      (Y.obj.map v.op (F.hom.app (op B) y.1))
    have hVal : F.hom.app (op B') (X.obj.map v.op y.1) =
        Y.obj.map v.op (F.hom.app (op B) y.1) := by
      rw [← NatTrans.naturality_apply]
    rw [hVal]
    exact HomotopyHypothesis.Category.SemiModelConstruction.presheafRelHomotopic_refl i' hi' Y _

private theorem completionRestriction_presheafRelHomotopic_iff
    {F : C ⥤ D} (hF : HomotopyHypothesis.Henry.IsCylinderMorphism F)
    {X : HomotopyHypothesis.Henry.Completion.{w} D} {A B : C}
    (i : A ⟶ B) (hi : cofibrations C i) {x y : X.obj.obj (op (F.obj B))} :
    HomotopyHypothesis.Category.SemiModelConstruction.PresheafRelHomotopic i
        ((HomotopyHypothesis.Henry.Completion.restriction F
          hF.toIsCofibrationMorphism).obj X) x y ↔
      HomotopyHypothesis.Category.SemiModelConstruction.PresheafRelHomotopic (F.map i) X x y := by
  let R := HomotopyHypothesis.Henry.Completion.restriction.{w} F hF.toIsCofibrationMorphism
  constructor
  · rintro ⟨cyl, H, h0, h1⟩
    let cylD := mapRelativeCylinder hF hi cyl
    have h0' : X.obj.map (F.map cyl.j₀ ≫ F.map cyl.c).op H = x := by
      change X.obj.map (F.map (cyl.j₀ ≫ cyl.c)).op H = x at h0
      rw [← Functor.map_comp]
      exact h0
    have h1' : X.obj.map (F.map cyl.j₁ ≫ F.map cyl.c).op H = y := by
      change X.obj.map (F.map (cyl.j₁ ≫ cyl.c)).op H = y at h1
      rw [← Functor.map_comp]
      exact h1
    refine ⟨cylD, H, ?_, ?_⟩
    · change X.obj.map (F.map cyl.j₀ ≫ F.map cyl.c).op H = x
      exact h0'
    · change X.obj.map (F.map cyl.j₁ ≫ F.map cyl.c).op H = y
      exact h1'
  · intro h
    obtain ⟨cylD, H, h0, h1⟩ := h
    obtain ⟨cylC⟩ := existsRelativeCylinder hi
    obtain ⟨g, hg0, hg1⟩ := compareMappedRelativeCylinder hF hi cylC cylD
    refine ⟨cylC, X.obj.map g.op H, ?_, ?_⟩
    · change X.obj.map (F.map (cylC.j₀ ≫ cylC.c)).op (X.obj.map g.op H) = x
      rw [← HomotopyHypothesis.Category.SemiModelStructure.presheafMap_comp_apply]
      rw [hg0]
      exact h0
    · change X.obj.map (F.map (cylC.j₁ ≫ cylC.c)).op (X.obj.map g.op H) = y
      rw [← HomotopyHypothesis.Category.SemiModelStructure.presheafMap_comp_apply]
      rw [hg1]
      exact h1

private noncomputable def completionRelativeClassRestrictionEquiv
    {F : C ⥤ D} (hF : HomotopyHypothesis.Henry.IsCylinderMorphism F)
    {X : HomotopyHypothesis.Henry.Completion.{w} D} {A B : C}
    (i : A ⟶ B) (hi : cofibrations C i) (a : X.obj.obj (op (F.obj A))) :
    _root_.Quotient (completionRelativeBoundarySetoid
      (X := (HomotopyHypothesis.Henry.Completion.restriction.{w} F
        hF.toIsCofibrationMorphism).obj X) i hi a) ≃
      _root_.Quotient (completionRelativeBoundarySetoid
        (X := X) (F.map i) (hF.map_cofibration i hi) a) := by
  let R := HomotopyHypothesis.Henry.Completion.restriction.{w} F hF.toIsCofibrationMorphism
  let hEvalA := completionRestriction_yonedaEvaluationEq hF.toIsCofibrationMorphism A X
  let hEvalB := completionRestriction_yonedaEvaluationEq hF.toIsCofibrationMorphism B X
  let sourceSetoid := completionRelativeBoundarySetoid (X := R.obj X) i hi a
  let targetSetoid := completionRelativeBoundarySetoid (X := X)
    (F.map i) (hF.map_cofibration i hi) a
  let fwd : _root_.Quotient sourceSetoid → _root_.Quotient targetSetoid :=
    _root_.Quotient.map (fun b => ⟨Equiv.cast hEvalB b.1, by
      have hCast : Equiv.cast hEvalB b.1 = b.1 := by cases hEvalB; rfl
      rw [hCast]
      change X.obj.map (F.map i).op b.1 = a
      have hprop := b.2
      change X.obj.map (F.map i).op b.1 = a at hprop
      exact hprop⟩)
      (fun x y h => by
        have hD := (completionRestriction_presheafRelHomotopic_iff hF i hi).mp h
        have hCastX : Equiv.cast hEvalB x.1 = x.1 := by cases hEvalB; rfl
        have hCastY : Equiv.cast hEvalB y.1 = y.1 := by cases hEvalB; rfl
        change HomotopyHypothesis.Category.SemiModelConstruction.PresheafRelHomotopic (F.map i) X
          (Equiv.cast hEvalB x.1) (Equiv.cast hEvalB y.1)
        rw [hCastX, hCastY]
        exact hD)
  let bwd : _root_.Quotient targetSetoid → _root_.Quotient sourceSetoid :=
    _root_.Quotient.map (fun b => ⟨(Equiv.cast hEvalB).symm b.1, by
      have hCast : (Equiv.cast hEvalB).symm b.1 = b.1 := by cases hEvalB; rfl
      rw [hCast]
      change (R.obj X).obj.map i.op b.1 = a
      have hprop := b.2
      change (R.obj X).obj.map i.op b.1 = a at hprop
      exact hprop⟩)
      (fun x y h => by
        have hC := (completionRestriction_presheafRelHomotopic_iff hF i hi).mpr h
        have hCastX : (Equiv.cast hEvalB).symm x.1 = x.1 := by cases hEvalB; rfl
        have hCastY : (Equiv.cast hEvalB).symm y.1 = y.1 := by cases hEvalB; rfl
        change HomotopyHypothesis.Category.SemiModelConstruction.PresheafRelHomotopic i (R.obj X)
          ((Equiv.cast hEvalB).symm x.1) ((Equiv.cast hEvalB).symm y.1)
        rw [hCastX, hCastY]
        exact hC)
  exact ⟨fwd, bwd, by
    intro q
    induction q using Quotient.inductionOn with
    | _ x => rfl, by
    intro q
    induction q using Quotient.inductionOn with
    | _ x => rfl⟩

private theorem equivOfBijective_natural {A B C D : Type*}
    {f : A → B} {g : C → D} {α : A → C} {β : B → D}
    (hf : Function.Bijective f) (hg : Function.Bijective g)
    (hcomm : Function.comp β f = Function.comp g α) :
    Function.comp β (Equiv.ofBijective f hf) =
      Function.comp (Equiv.ofBijective g hg) α := by
  funext x
  exact congrFun hcomm x

private theorem equivOfBijective_symm_natural {A B C D : Type*}
    {f : A → B} {g : C → D} {α : A → C} {β : B → D}
    (hf : Function.Bijective f) (hg : Function.Bijective g)
    (hcomm : Function.comp β f = Function.comp g α) :
    Function.comp α (Equiv.ofBijective f hf).symm =
      Function.comp (Equiv.ofBijective g hg).symm β := by
  funext y
  apply (Equiv.ofBijective g hg).injective
  calc
    g (α ((Equiv.ofBijective f hf).symm y)) =
        β (f ((Equiv.ofBijective f hf).symm y)) := by
          exact (congrFun hcomm ((Equiv.ofBijective f hf).symm y)).symm
    _ = β y := by
      congr 1
      exact (Equiv.ofBijective f hf).apply_symm_apply y
    _ = g ((Equiv.ofBijective g hg).symm (β y)) := by
      symm
      exact (Equiv.ofBijective g hg).apply_symm_apply (β y)

private theorem equiv_symm_natural {A B C D : Type*}
    (e₁ : A ≃ B) (e₂ : C ≃ D) (α : A → C) (β : B → D)
    (h : Function.comp β e₁ = Function.comp e₂ α) :
    Function.comp α e₁.symm = Function.comp e₂.symm β := by
  funext y
  apply e₂.injective
  calc
    e₂ (α (e₁.symm y)) = β (e₁ (e₁.symm y)) := (congrFun h (e₁.symm y)).symm
    _ = β y := by simp
    _ = e₂ (e₂.symm (β y)) := by simp

private theorem completionRelativeClassPrecomp_pushout_bijective
    {E : Type u₁} [Category.{v₁} E] [CategoryWithCofibrations E]
    [CategoryWithWeakEquivalences E] [HomotopyHypothesis.Henry.IsCylinderCategory E]
    {X : HomotopyHypothesis.Henry.Completion.{w} E}
    {A B A' P : E} (i : A ⟶ B) (u : A ⟶ A') (k : B ⟶ P) (j : A' ⟶ P)
    (hP : IsPushout i u k j) (hi : cofibrations E i) (a' : X.obj.obj (op A')) :
    Function.Bijective (completionRelativeClassPrecomp
      (X := X) u k hP.w
      ((IsCofibrationCategory.isStableUnderCobaseChange (C := E)).of_isPushout hP.flip hi)
      hi a' (X.obj.map u.op a') rfl) := by
  have hj : cofibrations E j :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := E)).of_isPushout hP.flip hi
  let pb := X.property.2 i u k j hP hi
  constructor
  · intro q₁ q₂ hq
    induction q₁ using Quotient.inductionOn with
    | _ x =>
      induction q₂ using Quotient.inductionOn with
      | _ y =>
        have hRel : HomotopyHypothesis.Category.SemiModelConstruction.PresheafRelHomotopic i X
            (X.obj.map k.op x.1) (X.obj.map k.op y.1) := Quotient.exact hq
        have hBase : X.obj.map j.op x.1 = X.obj.map j.op y.1 :=
          x.2.trans y.2.symm
        have hPush := HomotopyHypothesis.Category.SemiModelStructure.presheafRelHomotopic_pushout
          i u k j hP hi hBase hRel
        exact Quotient.sound hPush
  · intro q
    induction q using Quotient.inductionOn with
    | _ b =>
      obtain ⟨p, hk, hj'⟩ := Types.exists_of_isPullback pb b.1 a' b.2
      let p' : completionRelativeBoundary j a' := ⟨p, hj'⟩
      refine ⟨Quotient.mk _ p', ?_⟩
      apply Quotient.sound
      change HomotopyHypothesis.Category.SemiModelConstruction.PresheafRelHomotopic i X
        (X.obj.map k.op p) b.1
      rw [hk]
      exact HomotopyHypothesis.Category.SemiModelConstruction.presheafRelHomotopic_refl i hi X b.1

private theorem completionRelativeClassPrecomp_weakEquivalence_bijective
    {E : Type u} [Category.{v} E] [CategoryWithCofibrations E]
    [CategoryWithWeakEquivalences E] [HomotopyHypothesis.Henry.IsCylinderCategory E]
    {X : HomotopyHypothesis.Henry.Completion.{w} E}
    {A B B' : E} (i : A ⟶ B) (i' : A ⟶ B') (v : B' ⟶ B)
    (hsq : i' ≫ v = i) (hi : cofibrations E i) (hi' : cofibrations E i')
    (hv : weakEquivalences E v) (a : X.obj.obj (op A)) :
    Function.Bijective (completionRelativeClassPrecomp
      (X := X) (i := i) (i' := i') (𝟙 A) v (by simpa using hsq)
      hi hi' a a (by simp)) := by
  obtain ⟨l, hl, hRel⟩ := HomotopyHypothesis.Category.SemiModelStructure.cofibration_semilifts_against_weak_equivalence
    i hi i' v (𝟙 B) (by simpa using hsq.symm) hv
  have hAbs := homotopic_of_relHomotopic i hi hRel
  have hId : weakEquivalences E (𝟙 B) :=
    HomotopyHypothesis.Henry.IsCylinderCategory.isomorphisms_le_weakEquivalences
      (C := E) (𝟙 B) (MorphismProperty.isomorphisms.infer_property (𝟙 B))
  have hLv := completionWeakEquivalence_ofHomotopic hId (homotopic_symm hAbs)
  have hL : weakEquivalences E l :=
    (HomotopyHypothesis.Henry.IsCylinderCategory.twoOutOfSix
      (C := E) l v (𝟙 B) hLv (by simpa using hv)).1
  obtain ⟨m, hm, hRel'⟩ := HomotopyHypothesis.Category.SemiModelStructure.cofibration_semilifts_against_weak_equivalence
    i' hi' i l (𝟙 B') (by simpa using hl.symm) hL
  have h1 := relHomotopic_postcomp hRel' v
  have h2 := HomotopyHypothesis.Category.SemiModelStructure.relHomotopic_precomp
    i i' (𝟙 A) m (by simpa using hm) hi' hRel
  have h1' : HomotopyHypothesis.Henry.RelHomotopic i'
      ((m ≫ l) ≫ v) v := by simpa [Category.assoc] using h1
  have h2' : HomotopyHypothesis.Henry.RelHomotopic i'
      ((m ≫ l) ≫ v) m := by simpa [Category.assoc] using h2
  have hMv : HomotopyHypothesis.Henry.RelHomotopic i' m v :=
    (HomotopyHypothesis.Henry.Packages.relHomotopic_equivalence i' hi').1.trans
      ((HomotopyHypothesis.Henry.Packages.relHomotopic_equivalence i' hi').1.symm h2') h1'
  have hVl : HomotopyHypothesis.Henry.RelHomotopic i' (v ≫ l) (𝟙 B') := by
    exact (HomotopyHypothesis.Henry.Packages.relHomotopic_equivalence i' hi').1.trans
      ((HomotopyHypothesis.Henry.Packages.relHomotopic_equivalence i' hi').1.symm
        (relHomotopic_postcomp hMv l)) hRel'
  let fwd := completionRelativeClassPrecomp
    (X := X) (i := i) (i' := i') (𝟙 A) v (by simpa using hsq) hi hi' a a (by simp)
  let bwd := completionRelativeClassPrecomp
    (X := X) (i := i') (i' := i) (𝟙 A) l (by simpa using hl) hi' hi a a (by simp)
  have hLeft : ∀ q, bwd (fwd q) = q := by
    intro q
    induction q using Quotient.inductionOn with
    | _ x =>
      simp only [fwd, bwd, completionRelativeClassPrecomp, Quotient.map_mk]
      apply Quotient.sound
      change HomotopyHypothesis.Category.SemiModelConstruction.PresheafRelHomotopic i X
        (X.obj.map l.op (X.obj.map v.op x.1)) x.1
      simpa using HomotopyHypothesis.Category.SemiModelStructure.presheafRelHomotopic_of_relHomotopic
        x.1 hRel
  have hRight : ∀ q, fwd (bwd q) = q := by
    intro q
    induction q using Quotient.inductionOn with
    | _ y =>
      simp only [fwd, bwd, completionRelativeClassPrecomp, Quotient.map_mk]
      apply Quotient.sound
      change HomotopyHypothesis.Category.SemiModelConstruction.PresheafRelHomotopic i' X
        (X.obj.map v.op (X.obj.map l.op y.1)) y.1
      simpa using HomotopyHypothesis.Category.SemiModelStructure.presheafRelHomotopic_of_relHomotopic
        y.1 hVl
  constructor
  · intro q₁ q₂ hq
    have h := congrArg bwd hq
    rw [hLeft q₁, hLeft q₂] at h
    exact h
  · intro q
    exact ⟨bwd q, hRight q⟩

private theorem completionRelativeClassPrecomp_strictWeakSquare_bijective
    {E : Type u} [Category.{v} E] [CategoryWithCofibrations E]
    [CategoryWithWeakEquivalences E] [HomotopyHypothesis.Henry.IsCylinderCategory E]
    {X : HomotopyHypothesis.Henry.Completion.{w} E}
    {A A' B B' : E} (i : A ⟶ B) (i' : A' ⟶ B')
    (f : A ⟶ A') (g : B ⟶ B') (hsq : i ≫ g = f ≫ i')
    (hi : cofibrations E i) (hi' : cofibrations E i')
    (hf : weakEquivalences E f) (hg : weakEquivalences E g)
    (x' : X.obj.obj (op A')) :
    Function.Bijective (completionRelativeClassPrecomp
      (X := X) (i := i') (i' := i) f g hsq hi' hi x' (X.obj.map f.op x')
        rfl) := by
  letI : HasPushout i f := IsCofibrationCategory.hasPushout (C := E) i f hi
  let P := pushout i f
  let k : B ⟶ P := pushout.inl i f
  let j : A' ⟶ P := pushout.inr i f
  let hP : IsPushout i f k j := IsPushout.of_hasPushout i f
  have hj : cofibrations E j :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := E)).of_isPushout hP.flip hi
  let r : P ⟶ B' := hP.desc g i' hsq
  have hkr : k ≫ r = g := by simp [r, hP]
  have hjr : j ≫ r = i' := by simp [r, hP]
  have hkW : weakEquivalences E k :=
    HomotopyHypothesis.Henry.Packages.weakEquivalence_cobaseChange i f k j hP hi hf
  have hkrW : weakEquivalences E (k ≫ r) := by rw [hkr]; exact hg
  have hr : weakEquivalences E r :=
    (HomotopyHypothesis.Henry.IsCylinderCategory.twoOutOfSix
      (C := E) (𝟙 B) k r (by simpa using hkW) (by simpa using hkrW)).2.2.1
  let rMap := completionRelativeClassPrecomp
    (X := X) (i := i') (i' := j) (𝟙 A') r (by simpa using hjr) hi' hj x' x' (by simp)
  let pMap := completionRelativeClassPrecomp
    (X := X) (i := j) (i' := i) f k hP.w hj hi x' (X.obj.map f.op x') rfl
  let dMap := completionRelativeClassPrecomp
    (X := X) (i := i') (i' := i) f g hsq hi' hi x' (X.obj.map f.op x') rfl
  have hRMap := completionRelativeClassPrecomp_weakEquivalence_bijective
    i' j r (by simpa using hjr) hi' hj hr x'
  have hPMap := completionRelativeClassPrecomp_pushout_bijective i f k j hP hi x'
  have hComposite (q : Quotient (completionRelativeBoundarySetoid i' hi' x')) :
      pMap (rMap q) = dMap q := by
    induction q using Quotient.inductionOn with
    | _ y =>
      simp only [rMap, pMap, dMap, completionRelativeClassPrecomp, Quotient.map_mk]
      apply Quotient.sound
      change HomotopyHypothesis.Category.SemiModelConstruction.PresheafRelHomotopic i X
        (X.obj.map k.op (X.obj.map r.op y.1)) (X.obj.map g.op y.1)
      have hVal : X.obj.map k.op (X.obj.map r.op y.1) = X.obj.map g.op y.1 := by
        calc
          X.obj.map k.op (X.obj.map r.op y.1) = X.obj.map (k ≫ r).op y.1 :=
            (HomotopyHypothesis.Category.SemiModelStructure.presheafMap_comp_apply X k r y.1).symm
          _ = X.obj.map g.op y.1 := congrArg (fun q => X.obj.map q.op y.1) hkr
      rw [hVal]
      exact HomotopyHypothesis.Category.SemiModelConstruction.presheafRelHomotopic_refl i hi X
        (X.obj.map g.op y.1)
  constructor
  · intro q₁ q₂ hq
    apply hRMap.1
    apply hPMap.1
    calc
      pMap (rMap q₁) = dMap q₁ := hComposite q₁
      _ = dMap q₂ := hq
      _ = pMap (rMap q₂) := (hComposite q₂).symm
  · intro q
    obtain ⟨qP, hPq⟩ := hPMap.2 q
    obtain ⟨qR, hRq⟩ := hRMap.2 qP
    refine ⟨qR, ?_⟩
    calc
      dMap qR = pMap (rMap qR) := (hComposite qR).symm
      _ = pMap qP := congrArg pMap hRq
      _ = q := hPq

private theorem completionRelativeClassPrecomp_strictWeakSquare_bijective_ofBaseEq
    {E : Type u} [Category.{v} E] [CategoryWithCofibrations E]
    [CategoryWithWeakEquivalences E] [HomotopyHypothesis.Henry.IsCylinderCategory E]
    {X : HomotopyHypothesis.Henry.Completion.{w} E}
    {A A' B B' : E} (i : A ⟶ B) (i' : A' ⟶ B')
    (f : A ⟶ A') (g : B ⟶ B') (hsq : i ≫ g = f ≫ i')
    (hi : cofibrations E i) (hi' : cofibrations E i')
    (hf : weakEquivalences E f) (hg : weakEquivalences E g)
    (x' : X.obj.obj (op A')) (x : X.obj.obj (op A))
    (hx : X.obj.map f.op x' = x) :
    Function.Bijective (completionRelativeClassPrecomp
      (X := X) (i := i') (i' := i) f g hsq hi' hi x' x hx) := by
  cases hx
  exact completionRelativeClassPrecomp_strictWeakSquare_bijective
    i i' f g hsq hi hi' hf hg x'

private noncomputable def completionRelativeClassStrictWeakSquareEquiv
    {E : Type u} [Category.{v} E] [CategoryWithCofibrations E]
    [CategoryWithWeakEquivalences E] [HomotopyHypothesis.Henry.IsCylinderCategory E]
    {X : HomotopyHypothesis.Henry.Completion.{w} E}
    {A A' B B' : E} (i : A ⟶ B) (i' : A' ⟶ B')
    (f : A ⟶ A') (g : B ⟶ B') (hsq : i ≫ g = f ≫ i')
    (hi : cofibrations E i) (hi' : cofibrations E i')
    (hf : weakEquivalences E f) (hg : weakEquivalences E g)
    (x' : X.obj.obj (op A')) (x : X.obj.obj (op A))
    (hx : X.obj.map f.op x' = x) :
    Quotient (completionRelativeBoundarySetoid i' hi' x') ≃
      Quotient (completionRelativeBoundarySetoid i hi x) :=
  Equiv.ofBijective _ (completionRelativeClassPrecomp_strictWeakSquare_bijective_ofBaseEq
    i i' f g hsq hi hi' hf hg x' x hx)

private theorem completionRelativeClassStrictWeakSquareEquiv_natural
    {E : Type u₁} [Category.{v₁} E] [CategoryWithCofibrations E]
    [CategoryWithWeakEquivalences E] [HomotopyHypothesis.Henry.IsCylinderCategory E]
    {X Y : HomotopyHypothesis.Henry.Completion.{w} E} (F : X ⟶ Y)
    {A A' B B' : E} (i : A ⟶ B) (i' : A' ⟶ B')
    (f : A ⟶ A') (g : B ⟶ B') (hsq : i ≫ g = f ≫ i')
    (hi : cofibrations E i) (hi' : cofibrations E i')
    (hf : weakEquivalences E f) (hg : weakEquivalences E g)
    (x' : X.obj.obj (op A')) (x : X.obj.obj (op A))
    (hx : X.obj.map f.op x' = x)
    (hy : Y.obj.map f.op (F.hom.app (op A') x') = F.hom.app (op A) x) :
    Function.comp (completionRelativeClassMap F i hi x)
        (completionRelativeClassStrictWeakSquareEquiv
          i i' f g hsq hi hi' hf hg x' x hx) =
      Function.comp
        (completionRelativeClassStrictWeakSquareEquiv (X := Y)
          i i' f g hsq hi hi' hf hg (F.hom.app (op A') x')
          (F.hom.app (op A) x) hy)
        (completionRelativeClassMap F i' hi' x') := by
  have hPre := completionRelativeClassPrecomp_natural F f g hsq hi' hi x' x hx
  exact equivOfBijective_natural
    (completionRelativeClassPrecomp_strictWeakSquare_bijective_ofBaseEq
      i i' f g hsq hi hi' hf hg x' x hx)
    (completionRelativeClassPrecomp_strictWeakSquare_bijective_ofBaseEq
      i i' f g hsq hi hi' hf hg (F.hom.app (op A') x') (F.hom.app (op A) x) hy)
    hPre

private structure CompletionRelativeClassCylinderData
    {E : Type u} [Category.{v} E] [CategoryWithCofibrations E]
    [CategoryWithWeakEquivalences E] [HomotopyHypothesis.Henry.IsCylinderCategory E]
    {O A B : E} (hO : IsInitial O) (i : A ⟶ B) (hi : cofibrations E i)
    (cylA : RelativeCylinder (hO.to A)) where
  P : E
  m : cylA.I ⟶ P
  b0 : B ⟶ P
  b1 : B ⟶ P
  m_cof : cofibrations E m
  b0_weak : weakEquivalences E b0
  b1_weak : weakEquivalences E b1
  square0 : i ≫ b0 = (cylA.j₀ ≫ cylA.c) ≫ m
  square1 : i ≫ b1 = (cylA.j₁ ≫ cylA.c) ≫ m

private noncomputable def completionRelativeClassCylinderData.mk
    {E : Type u} [Category.{v} E] [CategoryWithCofibrations E]
    [CategoryWithWeakEquivalences E] [HomotopyHypothesis.Henry.IsCylinderCategory E]
    {O A B : E} (hO : IsInitial O) (i : A ⟶ B) (hi : cofibrations E i)
    (cylA : RelativeCylinder (hO.to A)) :
    CompletionRelativeClassCylinderData hO i hi cylA := by
  let e0 := cylA.j₀ ≫ cylA.c
  let e1 := cylA.j₁ ≫ cylA.c
  have hi0 : cofibrations E (hO.to A) := IsCofibrationCategory.initial_cofibration hO A
  have hEnd := HomotopyHypothesis.Category.SemiModelStructure.relativeCylinder_endpoint_properties hi0 cylA
  have he0p : e0 ≫ cylA.p = 𝟙 A := by simpa [e0, Category.assoc] using cylA.j₀_c_p
  have he1p : e1 ≫ cylA.p = 𝟙 A := by simpa [e1, Category.assoc] using cylA.j₁_c_p
  letI : HasPushout i e0 := IsCofibrationCategory.hasPushout (C := E) i e0 hi
  let P := pushout i e0
  let b0 : B ⟶ P := pushout.inl i e0
  let m0 : cylA.I ⟶ P := pushout.inr i e0
  let hP : IsPushout i e0 b0 m0 := IsPushout.of_hasPushout i e0
  have hm0 : cofibrations E m0 :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := E)).of_isPushout hP.flip hi
  have hb0 : weakEquivalences E b0 :=
    HomotopyHypothesis.Henry.Packages.weakEquivalence_cobaseChange
      i e0 b0 m0 hP hi hEnd.1.2
  have hCompat0 : i ≫ 𝟙 B = e0 ≫ (cylA.p ≫ i) := by
    calc
      i ≫ 𝟙 B = i := by simp
      _ = (e0 ≫ cylA.p) ≫ i := by rw [he0p]; simp
      _ = e0 ≫ (cylA.p ≫ i) := by simp [Category.assoc]
  let p0 : P ⟶ B := hP.desc (𝟙 B) (cylA.p ≫ i) hCompat0
  have hb0p : b0 ≫ p0 = 𝟙 B := by simp [p0, hP]
  have hm0p : m0 ≫ p0 = cylA.p ≫ i := by simp [p0, hP]
  have hIdB : weakEquivalences E (𝟙 B) :=
    HomotopyHypothesis.Henry.IsCylinderCategory.isomorphisms_le_weakEquivalences
      (C := E) (𝟙 B) (MorphismProperty.isomorphisms.infer_property (𝟙 B))
  have hp0 : weakEquivalences E p0 :=
    (HomotopyHypothesis.Henry.IsCylinderCategory.twoOutOfSix
      (C := E) (𝟙 B) b0 p0 (by simpa using hb0) (by simpa [hb0p] using hIdB)).2.2.1
  have hCompat1 : i ≫ 𝟙 B = (e1 ≫ m0) ≫ p0 := by
    calc
      i ≫ 𝟙 B = i := by simp
      _ = (e1 ≫ cylA.p) ≫ i := by rw [he1p]; simp
      _ = e1 ≫ (cylA.p ≫ i) := by simp [Category.assoc]
      _ = e1 ≫ (m0 ≫ p0) := by rw [hm0p]
      _ = (e1 ≫ m0) ≫ p0 := by simp [Category.assoc]
  let hLift1 := HomotopyHypothesis.Category.SemiModelStructure.cofibration_semilifts_against_weak_equivalence
    i hi (e1 ≫ m0) p0 (𝟙 B) hCompat1 hp0
  let b1 := Classical.choose hLift1
  have hLift1' := Classical.choose_spec hLift1
  have hExtend1 := hLift1'.1
  have hrelB := hLift1'.2
  have hAbsB := homotopic_of_relHomotopic i hi hrelB
  have hb1p : weakEquivalences E (b1 ≫ p0) :=
    completionWeakEquivalence_ofHomotopic hIdB (homotopic_symm hAbsB)
  have hb1W : weakEquivalences E b1 :=
    (HomotopyHypothesis.Henry.IsCylinderCategory.twoOutOfSix
      (C := E) b1 p0 (𝟙 B) hb1p (by simpa using hp0)).1
  exact ⟨P, m0, b0, b1, hm0, hb0, hb1W, hP.w, hExtend1⟩

private noncomputable def completionRelativeClassBasepointEquiv
    {E : Type u} [Category.{v} E] [CategoryWithCofibrations E]
    [CategoryWithWeakEquivalences E] [HomotopyHypothesis.Henry.IsCylinderCategory E]
    {X : HomotopyHypothesis.Henry.Completion.{w} E}
    {O A B : E} (hO : IsInitial O) (i : A ⟶ B) (hi : cofibrations E i)
    (a a' : X.obj.obj (op A)) (cylA : RelativeCylinder (hO.to A))
    (H : X.obj.obj (op cylA.I))
    (h0 : X.obj.map (cylA.j₀ ≫ cylA.c).op H = a)
    (h1 : X.obj.map (cylA.j₁ ≫ cylA.c).op H = a') :
    Quotient (completionRelativeBoundarySetoid i hi a) ≃
      Quotient (completionRelativeBoundarySetoid i hi a') := by
  let e0 := cylA.j₀ ≫ cylA.c
  let e1 := cylA.j₁ ≫ cylA.c
  let hEnd := HomotopyHypothesis.Category.SemiModelStructure.relativeCylinder_endpoint_properties
    (IsCofibrationCategory.initial_cofibration hO A) cylA
  let d := completionRelativeClassCylinderData.mk hO i hi cylA
  have ht0 := completionRelativeClassPrecomp_strictWeakSquare_bijective_ofBaseEq
    i d.m e0 d.b0 d.square0 hi d.m_cof hEnd.1.2 d.b0_weak H a h0
  have ht1 := completionRelativeClassPrecomp_strictWeakSquare_bijective_ofBaseEq
    i d.m e1 d.b1 d.square1 hi d.m_cof hEnd.2.2 d.b1_weak H a' h1
  let e0' := Equiv.ofBijective _ ht0
  let e1' := Equiv.ofBijective _ ht1
  exact e0'.symm.trans e1'

private theorem completionRelativeClassBasepointEquiv_natural
    {E : Type u} [Category.{v} E] [CategoryWithCofibrations E]
    [CategoryWithWeakEquivalences E] [HomotopyHypothesis.Henry.IsCylinderCategory E]
    {X Y : HomotopyHypothesis.Henry.Completion.{w} E} (F : X ⟶ Y)
    {O A B : E} (hO : IsInitial O) (i : A ⟶ B) (hi : cofibrations E i)
    (a a' : X.obj.obj (op A)) (cylA : RelativeCylinder (hO.to A))
    (H : X.obj.obj (op cylA.I))
    (h0 : X.obj.map (cylA.j₀ ≫ cylA.c).op H = a)
    (h1 : X.obj.map (cylA.j₁ ≫ cylA.c).op H = a') :
    Function.comp (completionRelativeClassMap F i hi a')
        (completionRelativeClassBasepointEquiv hO i hi a a' cylA H h0 h1) =
      Function.comp
        (completionRelativeClassBasepointEquiv hO i hi
          (F.hom.app (op A) a) (F.hom.app (op A) a') cylA
          (F.hom.app (op cylA.I) H)
          (by
            calc
              Y.obj.map (cylA.j₀ ≫ cylA.c).op (F.hom.app (op cylA.I) H) =
                  F.hom.app (op A) (X.obj.map (cylA.j₀ ≫ cylA.c).op H) := by
                    rw [← NatTrans.naturality_apply]
              _ = F.hom.app (op A) a := congrArg (F.hom.app (op A)) h0)
          (by
            calc
              Y.obj.map (cylA.j₁ ≫ cylA.c).op (F.hom.app (op cylA.I) H) =
                  F.hom.app (op A) (X.obj.map (cylA.j₁ ≫ cylA.c).op H) := by
                    rw [← NatTrans.naturality_apply]
              _ = F.hom.app (op A) a' := congrArg (F.hom.app (op A)) h1))
        (completionRelativeClassMap F i hi a) := by
  classical
  let e0 := cylA.j₀ ≫ cylA.c
  let e1 := cylA.j₁ ≫ cylA.c
  let d := completionRelativeClassCylinderData.mk hO i hi cylA
  let HX := completionRelativeClassPrecomp (X := X) e0 d.b0 d.square0 d.m_cof hi H a h0
  let HY := completionRelativeClassPrecomp (X := Y) e0 d.b0 d.square0 d.m_cof hi
    (F.hom.app (op cylA.I) H) (F.hom.app (op A) a)
    (by
      calc
        Y.obj.map e0.op (F.hom.app (op cylA.I) H) =
            F.hom.app (op A) (X.obj.map e0.op H) := by rw [← NatTrans.naturality_apply]
        _ = F.hom.app (op A) a := congrArg (F.hom.app (op A)) h0)
  let htX := completionRelativeClassPrecomp_strictWeakSquare_bijective_ofBaseEq
    i d.m e0 d.b0 d.square0 hi d.m_cof
    (HomotopyHypothesis.Category.SemiModelStructure.relativeCylinder_endpoint_properties
      (IsCofibrationCategory.initial_cofibration hO A) cylA).1.2 d.b0_weak H a h0
  let htY := completionRelativeClassPrecomp_strictWeakSquare_bijective_ofBaseEq
    i d.m e0 d.b0 d.square0 hi d.m_cof
    (HomotopyHypothesis.Category.SemiModelStructure.relativeCylinder_endpoint_properties
      (IsCofibrationCategory.initial_cofibration hO A) cylA).1.2 d.b0_weak
    (F.hom.app (op cylA.I) H) (F.hom.app (op A) a)
    (by
      calc
        Y.obj.map e0.op (F.hom.app (op cylA.I) H) =
            F.hom.app (op A) (X.obj.map e0.op H) := by rw [← NatTrans.naturality_apply]
        _ = F.hom.app (op A) a := congrArg (F.hom.app (op A)) h0)
  let HX1 := completionRelativeClassPrecomp (X := X) e1 d.b1 d.square1 d.m_cof hi H a' h1
  let HY1 := completionRelativeClassPrecomp (X := Y) e1 d.b1 d.square1 d.m_cof hi
    (F.hom.app (op cylA.I) H) (F.hom.app (op A) a')
    (by
      calc
        Y.obj.map e1.op (F.hom.app (op cylA.I) H) =
            F.hom.app (op A) (X.obj.map e1.op H) := by rw [← NatTrans.naturality_apply]
        _ = F.hom.app (op A) a' := congrArg (F.hom.app (op A)) h1)
  let htX1 := completionRelativeClassPrecomp_strictWeakSquare_bijective_ofBaseEq
    i d.m e1 d.b1 d.square1 hi d.m_cof
    (HomotopyHypothesis.Category.SemiModelStructure.relativeCylinder_endpoint_properties
      (IsCofibrationCategory.initial_cofibration hO A) cylA).2.2 d.b1_weak H a' h1
  let htY1 := completionRelativeClassPrecomp_strictWeakSquare_bijective_ofBaseEq
    i d.m e1 d.b1 d.square1 hi d.m_cof
    (HomotopyHypothesis.Category.SemiModelStructure.relativeCylinder_endpoint_properties
      (IsCofibrationCategory.initial_cofibration hO A) cylA).2.2 d.b1_weak
    (F.hom.app (op cylA.I) H) (F.hom.app (op A) a')
    (by
      calc
        Y.obj.map e1.op (F.hom.app (op cylA.I) H) =
            F.hom.app (op A) (X.obj.map e1.op H) := by rw [← NatTrans.naturality_apply]
        _ = F.hom.app (op A) a' := congrArg (F.hom.app (op A)) h1)
  have hComm0 := completionRelativeClassPrecomp_natural F e0 d.b0 d.square0
    d.m_cof hi H a h0
  have hComm1 := completionRelativeClassPrecomp_natural F e1 d.b1 d.square1
    d.m_cof hi H a' h1
  let E0X := Equiv.ofBijective HX htX
  let E0Y := Equiv.ofBijective HY htY
  let E1X := Equiv.ofBijective HX1 htX1
  let E1Y := Equiv.ofBijective HY1 htY1
  have hInv0 := equivOfBijective_symm_natural htX htY hComm0
  have hForw1 := equivOfBijective_natural htX1 htY1 hComm1
  funext q
  change (completionRelativeClassMap F i hi a')
      (E1X (E0X.symm q)) =
    E1Y (E0Y.symm (completionRelativeClassMap F i hi a q))
  calc
    _ = E1Y (completionRelativeClassMap F d.m d.m_cof H (E0X.symm q)) :=
      congrFun hForw1 (E0X.symm q)
    _ = E1Y (E0Y.symm (completionRelativeClassMap F i hi a q)) :=
      congrArg E1Y (congrFun hInv0 q)

private structure CompletionRelativeClassHomotopySquareData
    {E : Type u} [Category.{v} E] [CategoryWithCofibrations E]
    [CategoryWithWeakEquivalences E] [HomotopyHypothesis.Henry.IsCylinderCategory E]
    {A A' B B' : E} (i : A ⟶ B) (i' : A' ⟶ B')
    (s : A ⟶ A') (t : B ⟶ B') (hi : cofibrations E i)
    (ht : weakEquivalences E t) (h : HomotopyHypothesis.Henry.Homotopic (s ≫ i') (i ≫ t)) where
  O : E
  hO : IsInitial O
  cylA : RelativeCylinder (hO.to A)
  H : cylA.I ⟶ B'
  h0 : (cylA.j₀ ≫ cylA.c) ≫ H = s ≫ i'
  h1 : (cylA.j₁ ≫ cylA.c) ≫ H = i ≫ t
  Z : E
  c : A ⟶ Z
  w : Z ⟶ B'
  hc : cofibrations E c
  hw : weakEquivalences E w
  hcw : c ≫ w = s ≫ i'
  P : E
  z : Z ⟶ P
  m : cylA.I ⟶ P
  hP : IsPushout c (cylA.j₀ ≫ cylA.c) z m
  hm : cofibrations E m
  hz : weakEquivalences E z
  q : P ⟶ B'
  hzq : z ≫ q = w
  hmQ : m ≫ q = H
  hq : weakEquivalences E q
  b : B ⟶ P
  hb : weakEquivalences E b
  hib : i ≫ b = (cylA.j₁ ≫ cylA.c) ≫ m

private noncomputable def completionRelativeClassHomotopySquareData.mk
    {E : Type u} [Category.{v} E] [CategoryWithCofibrations E]
    [CategoryWithWeakEquivalences E] [HomotopyHypothesis.Henry.IsCylinderCategory E]
    {A A' B B' : E} (i : A ⟶ B) (i' : A' ⟶ B')
    (s : A ⟶ A') (t : B ⟶ B') (hi : cofibrations E i)
    (ht : weakEquivalences E t) (h : HomotopyHypothesis.Henry.Homotopic (s ≫ i') (i ≫ t)) :
    CompletionRelativeClassHomotopySquareData i i' s t hi ht h := by
  let O := Classical.choose h
  have hSpec := Classical.choose_spec h
  let hO : IsInitial O := Classical.choose hSpec
  have hRel := Classical.choose_spec hSpec
  let cylA := Classical.choose hRel
  have hCylSpec := Classical.choose_spec hRel
  let H := Classical.choose hCylSpec
  have hEnds := Classical.choose_spec hCylSpec
  let e0 := cylA.j₀ ≫ cylA.c
  let e1 := cylA.j₁ ≫ cylA.c
  have hi₀ : cofibrations E (hO.to A) := IsCofibrationCategory.initial_cofibration hO A
  have hEnd := HomotopyHypothesis.Category.SemiModelStructure.relativeCylinder_endpoint_properties hi₀ cylA
  let hFactor := HomotopyHypothesis.Category.SemiModelStructure.brown_factorization (s ≫ i')
  let Z := Classical.choose hFactor
  have hFactor1 := Classical.choose_spec hFactor
  let c := Classical.choose hFactor1
  have hFactor2 := Classical.choose_spec hFactor1
  let w := Classical.choose hFactor2
  have hFactor3 := Classical.choose_spec hFactor2
  have hc := hFactor3.1
  have hw := hFactor3.2.1
  have hcw := hFactor3.2.2
  letI : HasPushout c e0 := IsCofibrationCategory.hasPushout (C := E) c e0 hc
  let P := pushout c e0
  let z : Z ⟶ P := pushout.inl c e0
  let m : cylA.I ⟶ P := pushout.inr c e0
  let hP : IsPushout c e0 z m := IsPushout.of_hasPushout c e0
  have hm : cofibrations E m :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := E)).of_isPushout hP.flip hc
  have hz : weakEquivalences E z :=
    HomotopyHypothesis.Henry.Packages.weakEquivalence_cobaseChange
      c e0 z m hP hc hEnd.1.2
  have hCompat : c ≫ w = e0 ≫ H := by
    calc
      c ≫ w = s ≫ i' := hcw
      _ = e0 ≫ H := by simpa [e0, H] using hEnds.1.symm
  let q : P ⟶ B' := hP.desc w H hCompat
  have hzq : z ≫ q = w := by simp [q, hP]
  have hmQ : m ≫ q = H := by simp [q, hP]
  have hzqW : weakEquivalences E (z ≫ q) := by rw [hzq]; exact hw
  have hq : weakEquivalences E q :=
    (HomotopyHypothesis.Henry.IsCylinderCategory.twoOutOfSix
      (C := E) (𝟙 Z) z q (by simpa using hz) (by simpa using hzqW)).2.2.1
  have hLiftSq : i ≫ t = (e1 ≫ m) ≫ q := by
    calc
      i ≫ t = e1 ≫ H := by simpa [e1, H] using hEnds.2.symm
      _ = e1 ≫ (m ≫ q) := by rw [hmQ]
      _ = (e1 ≫ m) ≫ q := by simp [Category.assoc]
  let hLift := HomotopyHypothesis.Category.SemiModelStructure.cofibration_semilifts_against_weak_equivalence
    i hi (e1 ≫ m) q t hLiftSq hq
  let b := Classical.choose hLift
  have hLiftSpec := Classical.choose_spec hLift
  have hib : i ≫ b = e1 ≫ m := hLiftSpec.1
  have hRelB := hLiftSpec.2
  have hAbsB := homotopic_of_relHomotopic i hi hRelB
  have hbq : weakEquivalences E (b ≫ q) :=
    completionWeakEquivalence_ofHomotopic ht (homotopic_symm hAbsB)
  have hb : weakEquivalences E b :=
    (HomotopyHypothesis.Henry.IsCylinderCategory.twoOutOfSix
      (C := E) b q (𝟙 B') hbq (by simpa using hq)).1
  have h0 : (cylA.j₀ ≫ cylA.c) ≫ H = s ≫ i' := by simpa [cylA, H] using hEnds.1
  have h1 : (cylA.j₁ ≫ cylA.c) ≫ H = i ≫ t := by simpa [cylA, H] using hEnds.2
  exact ⟨O, hO, cylA, H, h0, h1, Z, c, w, hc, hw, hcw,
    P, z, m, hP, hm, hz, q, hzq, hmQ, hq, b, hb, hib⟩

private noncomputable def completionRelativeClassHomotopySquareEquiv
    {E : Type u} [Category.{v} E] [CategoryWithCofibrations E]
    [CategoryWithWeakEquivalences E] [HomotopyHypothesis.Henry.IsCylinderCategory E]
    {X : HomotopyHypothesis.Henry.Completion.{w} E}
    {A A' B B' : E} (i : A ⟶ B) (i' : A' ⟶ B')
    (s : A ⟶ A') (t : B ⟶ B') (hi : cofibrations E i)
    (ht : weakEquivalences E t) (h : HomotopyHypothesis.Henry.Homotopic (s ≫ i') (i ≫ t))
    (d : CompletionRelativeClassHomotopySquareData i i' s t hi ht h)
    (hs : weakEquivalences E s) (hi' : cofibrations E i')
    (x' : X.obj.obj (op A')) (x : X.obj.obj (op A))
    (hx : X.obj.map s.op x' = x)
    (z : X.obj.obj (op d.cylA.I))
    (hz0 : X.obj.map (d.cylA.j₀ ≫ d.cylA.c).op z = x)
    (hz1 : X.obj.map (d.cylA.j₁ ≫ d.cylA.c).op z = x) :
    Quotient (completionRelativeBoundarySetoid i' hi' x') ≃
      Quotient (completionRelativeBoundarySetoid i hi x) := by
  let e0 := d.cylA.j₀ ≫ d.cylA.c
  let e1 := d.cylA.j₁ ≫ d.cylA.c
  have hEnd := HomotopyHypothesis.Category.SemiModelStructure.relativeCylinder_endpoint_properties
    (IsCofibrationCategory.initial_cofibration d.hO A) d.cylA
  let eC := completionRelativeClassStrictWeakSquareEquiv
    d.c i' s d.w d.hcw d.hc hi' hs d.hw x' x hx
  let eCM := completionRelativeClassStrictWeakSquareEquiv
    d.c d.m e0 d.z d.hP.w d.hc d.hm hEnd.1.2 d.hz z x hz0
  let eIM := completionRelativeClassStrictWeakSquareEquiv
    i d.m e1 d.b d.hib hi d.hm hEnd.2.2 d.hb z x hz1
  exact eC.trans (eCM.symm.trans eIM)
private theorem completionRelativeClassHomotopySquareEquiv_natural
    {E : Type u₁} [Category.{v₁} E] [CategoryWithCofibrations E]
    [CategoryWithWeakEquivalences E] [HomotopyHypothesis.Henry.IsCylinderCategory E]
    {X Y : HomotopyHypothesis.Henry.Completion.{w} E} (F : X ⟶ Y)
    {A A' B B' : E} (i : A ⟶ B) (i' : A' ⟶ B')
    (s : A ⟶ A') (t : B ⟶ B') (hi : cofibrations E i)
    (ht : weakEquivalences E t) (h : HomotopyHypothesis.Henry.Homotopic (s ≫ i') (i ≫ t))
    (d : CompletionRelativeClassHomotopySquareData i i' s t hi ht h)
    (hs : weakEquivalences E s) (hi' : cofibrations E i')
    (x' : X.obj.obj (op A')) (x : X.obj.obj (op A))
    (hx : X.obj.map s.op x' = x)
    (hy : Y.obj.map s.op (F.hom.app (op A') x') = F.hom.app (op A) x)
    (z : X.obj.obj (op d.cylA.I))
    (hz0 : X.obj.map (d.cylA.j₀ ≫ d.cylA.c).op z = x)
    (hz1 : X.obj.map (d.cylA.j₁ ≫ d.cylA.c).op z = x) :
    Function.comp (completionRelativeClassMap F i hi x)
        (completionRelativeClassHomotopySquareEquiv
          i i' s t hi ht h d hs hi' x' x hx z hz0 hz1) =
      Function.comp
        (completionRelativeClassHomotopySquareEquiv (X := Y)
          i i' s t hi ht h d hs hi' (F.hom.app (op A') x') (F.hom.app (op A) x) hy
          (F.hom.app (op d.cylA.I) z)
          (by
            calc
              Y.obj.map (d.cylA.j₀ ≫ d.cylA.c).op (F.hom.app (op d.cylA.I) z) =
                  F.hom.app (op A) (X.obj.map (d.cylA.j₀ ≫ d.cylA.c).op z) := by
                    rw [← NatTrans.naturality_apply]
              _ = F.hom.app (op A) x := congrArg (F.hom.app (op A)) hz0)
          (by
            calc
              Y.obj.map (d.cylA.j₁ ≫ d.cylA.c).op (F.hom.app (op d.cylA.I) z) =
                  F.hom.app (op A) (X.obj.map (d.cylA.j₁ ≫ d.cylA.c).op z) := by
                    rw [← NatTrans.naturality_apply]
              _ = F.hom.app (op A) x := congrArg (F.hom.app (op A)) hz1))
        (completionRelativeClassMap F i' hi' x') := by
  let e0 := d.cylA.j₀ ≫ d.cylA.c
  let e1 := d.cylA.j₁ ≫ d.cylA.c
  have hEnd := HomotopyHypothesis.Category.SemiModelStructure.relativeCylinder_endpoint_properties
    (IsCofibrationCategory.initial_cofibration d.hO A) d.cylA
  have hy0 : Y.obj.map e0.op (F.hom.app (op d.cylA.I) z) = F.hom.app (op A) x := by
    calc
      Y.obj.map e0.op (F.hom.app (op d.cylA.I) z) =
          F.hom.app (op A) (X.obj.map e0.op z) := by rw [← NatTrans.naturality_apply]
      _ = F.hom.app (op A) x := congrArg (F.hom.app (op A)) hz0
  have hy1 : Y.obj.map e1.op (F.hom.app (op d.cylA.I) z) = F.hom.app (op A) x := by
    calc
      Y.obj.map e1.op (F.hom.app (op d.cylA.I) z) =
          F.hom.app (op A) (X.obj.map e1.op z) := by rw [← NatTrans.naturality_apply]
      _ = F.hom.app (op A) x := congrArg (F.hom.app (op A)) hz1
  have hC := completionRelativeClassStrictWeakSquareEquiv_natural
    F d.c i' s d.w d.hcw d.hc hi' hs d.hw x' x hx hy
  have hCM := completionRelativeClassStrictWeakSquareEquiv_natural
    F d.c d.m e0 d.z d.hP.w d.hc d.hm hEnd.1.2 d.hz z x hz0 hy0
  have hIM := completionRelativeClassStrictWeakSquareEquiv_natural
    F i d.m e1 d.b d.hib hi d.hm hEnd.2.2 d.hb z x hz1 hy1
  let eCX := completionRelativeClassStrictWeakSquareEquiv
    d.c i' s d.w d.hcw d.hc hi' hs d.hw x' x hx
  let eCY := completionRelativeClassStrictWeakSquareEquiv (X := Y)
    d.c i' s d.w d.hcw d.hc hi' hs d.hw (F.hom.app (op A') x')
    (F.hom.app (op A) x) hy
  let eCMX := completionRelativeClassStrictWeakSquareEquiv
    d.c d.m e0 d.z d.hP.w d.hc d.hm hEnd.1.2 d.hz z x hz0
  let eCMY := completionRelativeClassStrictWeakSquareEquiv (X := Y)
    d.c d.m e0 d.z d.hP.w d.hc d.hm hEnd.1.2 d.hz
    (F.hom.app (op d.cylA.I) z) (F.hom.app (op A) x) hy0
  let eIMX := completionRelativeClassStrictWeakSquareEquiv
    i d.m e1 d.b d.hib hi d.hm hEnd.2.2 d.hb z x hz1
  let eIMY := completionRelativeClassStrictWeakSquareEquiv (X := Y)
    i d.m e1 d.b d.hib hi d.hm hEnd.2.2 d.hb
    (F.hom.app (op d.cylA.I) z) (F.hom.app (op A) x) hy1
  have hCMInv := equiv_symm_natural eCMX eCMY
    (completionRelativeClassMap F d.m d.hm z)
    (completionRelativeClassMap F d.c d.hc x) hCM
  funext q
  change completionRelativeClassMap F i hi x (eIMX (eCMX.symm (eCX q))) =
    eIMY (eCMY.symm (eCY (completionRelativeClassMap F i' hi' x' q)))
  calc
    _ = eIMY (completionRelativeClassMap F d.m d.hm z (eCMX.symm (eCX q))) :=
      congrFun hIM (eCMX.symm (eCX q))
    _ = eIMY (eCMY.symm (completionRelativeClassMap F d.c d.hc x (eCX q))) :=
      congrArg eIMY (congrFun hCMInv (eCX q))
    _ = eIMY (eCMY.symm (eCY (completionRelativeClassMap F i' hi' x' q))) :=
      congrArg (fun y => eIMY (eCMY.symm y)) (congrFun hC q)

private theorem completionWeakEquivalence_iff_relativeClassesBijection
    {X Y : HomotopyHypothesis.Henry.Completion.{w} C} (f : X ⟶ Y) :
    HomotopyHypothesis.Henry.Completion.weakEquivalences C f ↔
      ∀ ⦃A B : C⦄ (i : A ⟶ B) (hi : cofibrations C i) (a : X.obj.obj (op A)),
        Function.Bijective (completionRelativeClassMap f i hi a) := by
  constructor
  · intro hf A B i hi a
    have hLift :=
      (HomotopyHypothesis.Category.SemiModelConstruction.completion_weakEquivalence_iff_homotopyLift f).1 hf
    constructor
    · intro q₁ q₂ hq
      induction q₁ using Quotient.inductionOn with
      | _ x =>
        induction q₂ using Quotient.inductionOn with
        | _ y =>
          have hBoundary : X.obj.map i.op x.1 = X.obj.map i.op y.1 :=
            x.2.trans y.2.symm
          have hRel : HomotopyHypothesis.Category.SemiModelConstruction.PresheafRelHomotopic i Y
              (f.hom.app (op B) x.1) (f.hom.app (op B) y.1) := by
            exact Quotient.exact hq
          have hReflect :=
            HomotopyHypothesis.Category.SemiModelConstruction.completion_weakEquivalence_reflectsHomotopy
              f hf hi hBoundary hRel
          exact Quotient.sound hReflect
    · intro q
      induction q using Quotient.inductionOn with
      | _ b =>
        obtain ⟨l, hl, hrel⟩ := hLift i hi a b.1 b.2.symm
        refine ⟨Quotient.mk _ ⟨l, hl⟩, ?_⟩
        exact Quotient.sound hrel
  · intro hbij
    apply (HomotopyHypothesis.Category.SemiModelConstruction.completion_weakEquivalence_iff_homotopyLift f).2
    intro A B i hi a b hab
    let b' : completionRelativeBoundary i (f.hom.app (op A) a) := ⟨b, hab.symm⟩
    obtain ⟨q, hq⟩ := (hbij i hi a).2 (Quotient.mk _ b')
    induction q using Quotient.inductionOn with
    | _ l =>
      have hrel : HomotopyHypothesis.Category.SemiModelConstruction.PresheafRelHomotopic i Y
          (f.hom.app (op B) l.1) b := by
        exact Quotient.exact hq
      exact ⟨l.1, l.2, hrel⟩

private theorem completionRestriction_mapFibration {F : C ⥤ D}
    (hF : HomotopyHypothesis.Henry.IsCylinderMorphism F)
    {X Y : HomotopyHypothesis.Henry.Completion.{w} D} (f : X ⟶ Y)
    (hf : HomotopyHypothesis.Henry.Completion.fibrations D f) :
    HomotopyHypothesis.Henry.Completion.fibrations C
      ((HomotopyHypothesis.Henry.Completion.restriction.{w} F hF.toIsCofibrationMorphism).map f) := by
  let rawRestr := (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj F.op
  change HomotopyHypothesis.Henry.presheafFibrations (rawRestr.map f.hom)
  intro A B i hiC hiW a b hab
  obtain ⟨l, hlA, hlB⟩ := hf (F.map i) (hF.map_cofibration i hiC)
    (hF.map_weakEquivalence i hiW) a b (by simpa [rawRestr] using hab)
  exact ⟨l, by simpa [rawRestr] using hlA, by simpa [rawRestr] using hlB⟩

private theorem completionRestriction_mapWeakEquivalence {F : C ⥤ D}
    (hF : HomotopyHypothesis.Henry.IsCylinderMorphism F)
    {X Y : HomotopyHypothesis.Henry.Completion.{w} D} (f : X ⟶ Y)
    (hf : HomotopyHypothesis.Henry.Completion.weakEquivalences D f) :
    HomotopyHypothesis.Henry.Completion.weakEquivalences C
      ((HomotopyHypothesis.Henry.Completion.restriction.{w} F hF.toIsCofibrationMorphism).map f) := by
  let rawRestr := (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type w)).obj F.op
  change HomotopyHypothesis.Henry.presheafWeakEquivalences (rawRestr.map f.hom)
  intro A B i hi a b hab
  obtain ⟨cylC⟩ := existsRelativeCylinder hi
  obtain ⟨l, cylD, h, hlA, h₀, h₁⟩ := hf (F.map i) (hF.map_cofibration i hi)
    a b (by simpa [rawRestr] using hab)
  obtain ⟨g, hg₀, hg₁⟩ := compareMappedRelativeCylinder hF hi cylC cylD
  let h' : (Y.obj).obj (op (F.obj cylC.I)) := (Y.obj).map g.op h
  refine ⟨l, cylC, h', ?_, ?_, ?_⟩
  · simpa [rawRestr] using hlA
  · calc
      (Y.obj).map (F.map (cylC.j₀ ≫ cylC.c)).op h' =
          (Y.obj).map ((F.map (cylC.j₀ ≫ cylC.c)) ≫ g).op h := by simp [h']
      _ = (Y.obj).map (cylD.j₀ ≫ cylD.c).op h := by rw [hg₀]
      _ = f.hom.app (op (F.obj B)) l := h₀
  · calc
      (Y.obj).map (F.map (cylC.j₁ ≫ cylC.c)).op h' =
          (Y.obj).map ((F.map (cylC.j₁ ≫ cylC.c)) ≫ g).op h := by simp [h']
      _ = (Y.obj).map (cylD.j₁ ≫ cylD.c).op h := by rw [hg₁]
      _ = b := h₁

private theorem completionRestriction_weakComparison_ofReflection
    {F : C ⥤ D} (hF : HomotopyHypothesis.Henry.IsCylinderMorphism F)
    (hFF : HomotopyHypothesis.Henry.IsHomotopyFullyFaithful F)
    {L : HomotopyHypothesis.Henry.Completion.{w} C ⥤
      HomotopyHypothesis.Henry.Completion.{w} D}
    (adj : L ⊣ HomotopyHypothesis.Henry.Completion.restriction.{w} F
      hF.toIsCofibrationMorphism)
    (hReflect : ∀ ⦃X Y : HomotopyHypothesis.Henry.Completion.{w} D⦄ (f : X ⟶ Y),
      HomotopyHypothesis.Henry.Completion.weakEquivalences C
          ((HomotopyHypothesis.Henry.Completion.restriction.{w} F
            hF.toIsCofibrationMorphism).map f) →
        HomotopyHypothesis.Henry.Completion.weakEquivalences D f)
    {X : HomotopyHypothesis.Henry.Completion.{w} C}
    (hX : IsCofibrantFor (HomotopyHypothesis.Henry.Completion.cofibrations C) X)
    {Y : HomotopyHypothesis.Henry.Completion.{w} D}
    (f : L.obj X ⟶ Y) :
    (HomotopyHypothesis.Henry.Completion.weakEquivalences D f ↔
      HomotopyHypothesis.Henry.Completion.weakEquivalences C (adj.homEquiv X Y f)) := by
  let R := HomotopyHypothesis.Henry.Completion.restriction.{w} F
    hF.toIsCofibrationMorphism
  let W := HomotopyHypothesis.Henry.Completion.weakEquivalences C
  let hSemi := HomotopyHypothesis.Henry.Packages.completion_isSemiModelCategory (C := C)
  letI : W.HasTwoOutOfThreeProperty := hSemi.1.twoOutOfThree
  have hη := completionAdjunctionUnit_isWeakEquivalence_ofFlat hF hFF adj
    (HomotopyHypothesis.Category.SemiModelStructure.isFlat_of_isCofibrant hX)
  have hAdj : adj.homEquiv X Y f = adj.unit.app X ≫ R.map f :=
    Adjunction.homEquiv_unit adj X Y f
  constructor
  · intro hf
    have hRf := completionRestriction_mapWeakEquivalence hF f hf
    have hComp : W (adj.unit.app X ≫ R.map f) := W.comp_mem _ _ hη hRf
    rw [hAdj]
    exact hComp
  · intro hf
    have hRf : W (R.map f) := by
      apply W.of_precomp (adj.unit.app X) (R.map f) hη
      rw [← hAdj]
      exact hf
    exact hReflect f hRf

private theorem completionRestriction_isQuillenEquivalence_ofWeakComparison
    {F : C ⥤ D} (hF : HomotopyHypothesis.Henry.IsCylinderMorphism F)
    {L : HomotopyHypothesis.Henry.Completion.{w} C ⥤
      HomotopyHypothesis.Henry.Completion.{w} D}
    (adj : L ⊣ HomotopyHypothesis.Henry.Completion.restriction.{w} F
      hF.toIsCofibrationMorphism)
    (hWeak : ∀ ⦃X : HomotopyHypothesis.Henry.Completion.{w} C⦄
      ⦃Y : HomotopyHypothesis.Henry.Completion.{w} D⦄ (f : L.obj X ⟶ Y),
      IsCofibrantFor (HomotopyHypothesis.Henry.Completion.cofibrations C) X →
      IsFibrantFor (HomotopyHypothesis.Henry.Completion.fibrations D) Y →
      (HomotopyHypothesis.Henry.Completion.weakEquivalences D f ↔
        HomotopyHypothesis.Henry.Completion.weakEquivalences C (adj.homEquiv X Y f))) :
    HomotopyHypothesis.Henry.IsQuillenEquivalence adj
      (HomotopyHypothesis.Henry.Completion.cofibrations C)
      (HomotopyHypothesis.Henry.Completion.fibrations C)
      (HomotopyHypothesis.Henry.Completion.weakEquivalences C)
      (HomotopyHypothesis.Henry.Completion.cofibrations D)
      (HomotopyHypothesis.Henry.Completion.fibrations D)
      (HomotopyHypothesis.Henry.Completion.weakEquivalences D) := by
  refine ⟨?_, ?_, hWeak⟩
  · intro X Y f hf
    exact completionRestriction_mapFibration hF f hf
  · intro X Y f hf hw
    exact completionRestriction_mapWeakEquivalence hF f hw

private theorem completionWeakEquivalence_iff_relativeClassesBijectionAt
    {E : Type u} [Category.{v} E] [CategoryWithCofibrations E]
    [CategoryWithWeakEquivalences E] [IsCylinderCategory E]
    {X Y : Completion.{w} E} (f : X ⟶ Y) :
    Completion.weakEquivalences E f ↔
      ∀ ⦃A B : E⦄ (i : A ⟶ B) (hi : cofibrations E i) (a : X.obj.obj (op A)),
        Function.Bijective (completionRelativeClassMap f i hi a) := by
  constructor
  · intro hf A B i hi a
    have hLift :=
      (HomotopyHypothesis.Category.SemiModelConstruction.completion_weakEquivalence_iff_homotopyLift f).1 hf
    constructor
    · intro q₁ q₂ hq
      induction q₁ using Quotient.inductionOn with
      | _ x =>
        induction q₂ using Quotient.inductionOn with
        | _ y =>
          have hBoundary : X.obj.map i.op x.1 = X.obj.map i.op y.1 :=
            x.2.trans y.2.symm
          have hRel : HomotopyHypothesis.Category.SemiModelConstruction.PresheafRelHomotopic i Y
              (f.hom.app (op B) x.1) (f.hom.app (op B) y.1) := by
            exact Quotient.exact hq
          have hReflect :=
            HomotopyHypothesis.Category.SemiModelConstruction.completion_weakEquivalence_reflectsHomotopy
              f hf hi hBoundary hRel
          exact Quotient.sound hReflect
    · intro q
      induction q using Quotient.inductionOn with
      | _ b =>
        obtain ⟨l, hl, hrel⟩ := hLift i hi a b.1 b.2.symm
        refine ⟨Quotient.mk _ ⟨l, hl⟩, ?_⟩
        exact Quotient.sound hrel
  · intro hbij
    apply (HomotopyHypothesis.Category.SemiModelConstruction.completion_weakEquivalence_iff_homotopyLift f).2
    intro A B i hi a b hab
    let b' : completionRelativeBoundary i (f.hom.app (op A) a) := ⟨b, hab.symm⟩
    obtain ⟨q, hq⟩ := (hbij i hi a).2 (Quotient.mk _ b')
    induction q using Quotient.inductionOn with
    | _ l =>
      have hrel : HomotopyHypothesis.Category.SemiModelConstruction.PresheafRelHomotopic i Y
          (f.hom.app (op B) l.1) b := by
        exact Quotient.exact hq
      exact ⟨l.1, l.2, hrel⟩

private theorem completionRelativeClassRestrictionEquiv_natural
    {F : C ⥤ D} (hF : IsCylinderMorphism F)
    {X Y : Completion.{w} D} (f : X ⟶ Y) {A B : C}
    (i : A ⟶ B) (hi : cofibrations C i) (a : X.obj.obj (op (F.obj A))) :
    Function.comp (completionRelativeClassMap f (F.map i) (hF.map_cofibration i hi) a)
        (completionRelativeClassRestrictionEquiv hF i hi a) =
      Function.comp
        (completionRelativeClassRestrictionEquiv hF i hi (f.hom.app (op (F.obj A)) a))
        (completionRelativeClassMap
          ((Completion.restriction.{w} F hF.toIsCofibrationMorphism).map f) i hi a) := by
  funext q
  induction q using Quotient.inductionOn with
  | _ b =>
    cases completionRestriction_yonedaEvaluationEq hF.toIsCofibrationMorphism B X
    cases completionRestriction_yonedaEvaluationEq hF.toIsCofibrationMorphism B Y
    unfold completionRelativeClassRestrictionEquiv completionRelativeClassMap
    simp only [Quotient.map_mk, Equiv.cast_apply, cast_eq]
    apply Quotient.sound
    exact HomotopyHypothesis.Category.SemiModelConstruction.presheafRelHomotopic_refl
      (F.map i) (hF.map_cofibration i hi) Y (f.hom.app (op (F.obj B)) b.1)

private theorem completionRelativeClassMap_image_bijective
    {F : C ⥤ D} (hF : IsCylinderMorphism F)
    {X Y : Completion.{w} D} (f : X ⟶ Y)
    (hf : Completion.weakEquivalences C
      ((Completion.restriction.{w} F hF.toIsCofibrationMorphism).map f))
    {A B : C} (j : A ⟶ B) (hj : cofibrations C j)
    (a : X.obj.obj (op (F.obj A))) :
    Function.Bijective (completionRelativeClassMap f (F.map j)
      (hF.map_cofibration j hj) a) := by
  let R := Completion.restriction.{w} F hF.toIsCofibrationMorphism
  have hR :=
    ((completionWeakEquivalence_iff_relativeClassesBijection (R.map f)).1 hf) j hj a
  let eX := completionRelativeClassRestrictionEquiv hF j hj a
  let eY := completionRelativeClassRestrictionEquiv hF j hj
    (f.hom.app (op (F.obj A)) a)
  have hNat := completionRelativeClassRestrictionEquiv_natural hF f j hj a
  have hComp : Function.Bijective
      (Function.comp (completionRelativeClassMap f (F.map j)
        (hF.map_cofibration j hj) a) eX) := by
    rw [hNat]
    exact eY.bijective.comp hR
  exact (Function.Bijective.of_comp_iff _ eX.bijective).mp hComp

private theorem completionRelativeClassMap_bijective_of_homotopySquare
    {E : Type u} [Category.{v} E] [CategoryWithCofibrations E]
    [CategoryWithWeakEquivalences E] [IsCylinderCategory E]
    {X Y : Completion.{w} E} (F : X ⟶ Y)
    {A A' B B' : E} (i : A ⟶ B) (i' : A' ⟶ B')
    (s : A ⟶ A') (t : B ⟶ B') (hi : cofibrations E i)
    (ht : weakEquivalences E t)
    (h : Homotopic (s ≫ i') (i ≫ t))
    (d : CompletionRelativeClassHomotopySquareData i i' s t hi ht h)
    (hs : weakEquivalences E s) (hi' : cofibrations E i')
    (x' : X.obj.obj (op A')) (x : X.obj.obj (op A))
    (hx : X.obj.map s.op x' = x)
    (z : X.obj.obj (op d.cylA.I))
    (hz0 : X.obj.map (d.cylA.j₀ ≫ d.cylA.c).op z = x)
    (hz1 : X.obj.map (d.cylA.j₁ ≫ d.cylA.c).op z = x)
    (hBij : Function.Bijective (completionRelativeClassMap F i hi x)) :
    Function.Bijective (completionRelativeClassMap F i' hi' x') := by
  have hy : Y.obj.map s.op (F.hom.app (op A') x') = F.hom.app (op A) x := by
    calc
      Y.obj.map s.op (F.hom.app (op A') x') =
          F.hom.app (op A) (X.obj.map s.op x') := by
            rw [← NatTrans.naturality_apply]
      _ = F.hom.app (op A) x := congrArg (F.hom.app (op A)) hx
  let e0 := d.cylA.j₀ ≫ d.cylA.c
  let e1 := d.cylA.j₁ ≫ d.cylA.c
  have hEnd := HomotopyHypothesis.Category.SemiModelStructure.relativeCylinder_endpoint_properties
    (IsCofibrationCategory.initial_cofibration d.hO A) d.cylA
  have hy0 : Y.obj.map e0.op (F.hom.app (op d.cylA.I) z) = F.hom.app (op A) x := by
    calc
      Y.obj.map e0.op (F.hom.app (op d.cylA.I) z) =
          F.hom.app (op A) (X.obj.map e0.op z) := by rw [← NatTrans.naturality_apply]
      _ = F.hom.app (op A) x := congrArg (F.hom.app (op A)) hz0
  have hy1 : Y.obj.map e1.op (F.hom.app (op d.cylA.I) z) = F.hom.app (op A) x := by
    calc
      Y.obj.map e1.op (F.hom.app (op d.cylA.I) z) =
          F.hom.app (op A) (X.obj.map e1.op z) := by rw [← NatTrans.naturality_apply]
      _ = F.hom.app (op A) x := congrArg (F.hom.app (op A)) hz1
  have hC := completionRelativeClassStrictWeakSquareEquiv_natural
    F d.c i' s d.w d.hcw d.hc hi' hs d.hw x' x hx hy
  have hCM := completionRelativeClassStrictWeakSquareEquiv_natural
    F d.c d.m e0 d.z d.hP.w d.hc d.hm hEnd.1.2 d.hz z x hz0 hy0
  have hIM := completionRelativeClassStrictWeakSquareEquiv_natural
    F i d.m e1 d.b d.hib hi d.hm hEnd.2.2 d.hb z x hz1 hy1
  let eCX := completionRelativeClassStrictWeakSquareEquiv
    d.c i' s d.w d.hcw d.hc hi' hs d.hw x' x hx
  let eCY := completionRelativeClassStrictWeakSquareEquiv (X := Y)
    d.c i' s d.w d.hcw d.hc hi' hs d.hw (F.hom.app (op A') x')
    (F.hom.app (op A) x) hy
  let eCMX := completionRelativeClassStrictWeakSquareEquiv
    d.c d.m e0 d.z d.hP.w d.hc d.hm hEnd.1.2 d.hz z x hz0
  let eCMY := completionRelativeClassStrictWeakSquareEquiv (X := Y)
    d.c d.m e0 d.z d.hP.w d.hc d.hm hEnd.1.2 d.hz
    (F.hom.app (op d.cylA.I) z) (F.hom.app (op A) x) hy0
  let eIMX := completionRelativeClassStrictWeakSquareEquiv
    i d.m e1 d.b d.hib hi d.hm hEnd.2.2 d.hb z x hz1
  let eIMY := completionRelativeClassStrictWeakSquareEquiv (X := Y)
    i d.m e1 d.b d.hib hi d.hm hEnd.2.2 d.hb
    (F.hom.app (op d.cylA.I) z) (F.hom.app (op A) x) hy1
  have hCMInv := equiv_symm_natural eCMX eCMY
    (completionRelativeClassMap F d.m d.hm z)
    (completionRelativeClassMap F d.c d.hc x) hCM
  have hPoint (q : Quotient (completionRelativeBoundarySetoid i' hi' x')) :
      completionRelativeClassMap F i hi x (eIMX (eCMX.symm (eCX q))) =
        eIMY (eCMY.symm (eCY (completionRelativeClassMap F i' hi' x' q))) := by
    calc
      _ = eIMY (completionRelativeClassMap F d.m d.hm z (eCMX.symm (eCX q))) :=
        congrFun hIM (eCMX.symm (eCX q))
      _ = eIMY (eCMY.symm (completionRelativeClassMap F d.c d.hc x (eCX q))) :=
        congrArg eIMY (congrFun hCMInv (eCX q))
      _ = eIMY (eCMY.symm (eCY (completionRelativeClassMap F i' hi' x' q))) :=
        congrArg (fun y => eIMY (eCMY.symm y)) (congrFun hC q)
  let EX := eCX.trans (eCMX.symm.trans eIMX)
  let EY := eCY.trans (eCMY.symm.trans eIMY)
  have hNat : Function.comp (completionRelativeClassMap F i hi x) EX =
      Function.comp EY (completionRelativeClassMap F i' hi' x') := by
    funext q
    simpa [EX, EY, Function.comp, Equiv.trans_apply] using hPoint q
  have hComp : Function.Bijective
      (Function.comp (completionRelativeClassMap F i hi x) EX) :=
    hBij.comp EX.bijective
  have hComp' : Function.Bijective
      (Function.comp EY (completionRelativeClassMap F i' hi' x')) := by
    simpa [hNat] using hComp
  exact (Function.Bijective.of_comp_iff' EY.bijective
    (completionRelativeClassMap F i' hi' x')).mp hComp'

/-- Relative extension classes along an arbitrary cofibration are bijective once they are
bijective along cofibrations in the image, because homotopy surjectivity supplies a
homotopy-commutative square of weak equivalences and those classes are invariant under it. -/
private theorem completionRestriction_reflectsWeakEquivalence
    {F : C ⥤ D} (hF : IsCylinderMorphism F) (hac : IsAcyclic F)
    {X Y : Completion.{w} D} (f : X ⟶ Y)
    (hf : Completion.weakEquivalences C
      ((Completion.restriction.{w} F hF.toIsCofibrationMorphism).map f)) :
    Completion.weakEquivalences D f := by
  apply (completionWeakEquivalence_iff_relativeClassesBijectionAt f).2
  intro A B i hi a
  obtain ⟨A0, B0, j, hj, hrest⟩ := exists_imageCofibration_homotopySquare hF hac i hi
  obtain ⟨u, hu, v, hv, hHom⟩ := hrest
  have hPath : Homotopic (u ≫ i) (F.map j ≫ v) := homotopic_symm hHom
  let d := completionRelativeClassHomotopySquareData.mk (F.map j) i u v
    (hF.map_cofibration j hj) hv hPath
  let x : X.obj.obj (op (F.obj A0)) := X.obj.map u.op a
  have hx : X.obj.map u.op a = x := rfl
  let z : X.obj.obj (op d.cylA.I) := X.obj.map d.cylA.p.op x
  have hz0 : X.obj.map (d.cylA.j₀ ≫ d.cylA.c).op z = x := by
    change (X.obj.map d.cylA.p.op ≫ X.obj.map (d.cylA.j₀ ≫ d.cylA.c).op) x = x
    rw [← X.obj.map_comp, ← op_comp, Category.assoc, d.cylA.j₀_c_p, op_id, X.obj.map_id]
    rfl
  have hz1 : X.obj.map (d.cylA.j₁ ≫ d.cylA.c).op z = x := by
    change (X.obj.map d.cylA.p.op ≫ X.obj.map (d.cylA.j₁ ≫ d.cylA.c).op) x = x
    rw [← X.obj.map_comp, ← op_comp, Category.assoc, d.cylA.j₁_c_p, op_id, X.obj.map_id]
    rfl
  have hImg := completionRelativeClassMap_image_bijective hF f hf j hj x
  exact completionRelativeClassMap_bijective_of_homotopySquare f (F.map j) i u v
    (hF.map_cofibration j hj) hv hPath d hu hi a x hx z hz0 hz1 hImg

end CompletionRestrictionQuillen

/-- H Prop 2.4.16: restriction along an acyclic morphism of cylinder categories is a
Quillen equivalence on completions. -/
theorem completionRestriction_isQuillenEquivalence_proof
    {C : Type u₁} [Category.{v₁} C] [CategoryWithCofibrations C]
    [CategoryWithWeakEquivalences C]
    {D : Type u₂} [Category.{v₂} D] [CategoryWithCofibrations D]
    [CategoryWithWeakEquivalences D]
    [HomotopyHypothesis.Henry.IsCylinderCategory C]
    [HomotopyHypothesis.Henry.IsCylinderCategory D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {F : C ⥤ D} (hF : HomotopyHypothesis.Henry.IsCylinderMorphism F)
    (hac : HomotopyHypothesis.Henry.IsAcyclic F)
    {L : HomotopyHypothesis.Henry.Completion.{w} C ⥤
      HomotopyHypothesis.Henry.Completion.{w} D}
    (adj : L ⊣ HomotopyHypothesis.Henry.Completion.restriction.{w} F
      hF.toIsCofibrationMorphism) :
    HomotopyHypothesis.Henry.IsQuillenEquivalence adj
      (HomotopyHypothesis.Henry.Completion.cofibrations C)
      (HomotopyHypothesis.Henry.Completion.fibrations C)
      (HomotopyHypothesis.Henry.Completion.weakEquivalences C)
      (HomotopyHypothesis.Henry.Completion.cofibrations D)
      (HomotopyHypothesis.Henry.Completion.fibrations D)
      (HomotopyHypothesis.Henry.Completion.weakEquivalences D) := by
  refine completionRestriction_isQuillenEquivalence_ofWeakComparison hF adj ?_
  intro X Y f hX _
  refine completionRestriction_weakComparison_ofReflection hF hac.2 adj ?_ hX f
  intro _ _ g hg
  exact completionRestriction_reflectsWeakEquivalence hF hac g hg

#print axioms completionRestriction_isRightAdjoint_proof

#print axioms completionRestriction_isQuillenEquivalence_proof

end HomotopyHypothesis.Localization.CompletionEquivalence
