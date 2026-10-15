import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Interfaces.Restriction
import HomotopyHypothesis.Completion.FinitelyCellular.Afin
import HomotopyHypothesis.Completion.FinitelyCellular.Counit
import HomotopyHypothesis.Completion.FinitelyCellular.Equiv
import HomotopyHypothesis.Completion.FinitelyCellular.Phi
import HomotopyHypothesis.Completion.FinitelyCellular.Theta
import HomotopyHypothesis.FiniteCategory.Lifting.ModelShapes
import HomotopyHypothesis.FiniteCategory.Lifting.RealizationStatements
universe u v

open CategoryTheory Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck
open HomotopyHypothesis.Blueprint HomotopyHypothesis.Henry

noncomputable section

namespace HomotopyHypothesis.FiniteCategory.Comparison

/-- The completion presheaf represented by an object of the target category. -/
def exactFunctorCompletion {C : GlobularTheory.{u}} (hC : C.IsCoherator)
    {Y : Type v} [Category.{u} Y] [CategoryWithCofibrations Y]
    (F : Afin C hC ⥤ Y) (hF : IsCofibrationMorphism F) :
    Y ⥤ Completion.{u} (Afin C hC) :=
  Completion.yoneda.{u} (C := Y) ⋙ Completion.restriction.{u} F hF

/-- The model associated to an exact functor by restricting representable presheaves. -/
def exactFunctorModel {C : GlobularTheory.{u}} (hC : C.IsCoherator)
    {Y : Type v} [Category.{u} Y] [CategoryWithCofibrations Y]
    (F : Afin C hC ⥤ Y) (hF : IsCofibrationMorphism F) : Y ⥤ C.Model :=
  Completion.yoneda.{u} (C := Y) ⋙ Completion.restriction.{u} F hF ⋙
    HomotopyHypothesis.Completion.FinitelyCellular.Phi hC

/-- The representables used by the completion construction agree with the named globular diagram. -/
def afinRepresentablesIsoFree {C : GlobularTheory.{u}} (hC : C.IsCoherator) :
    HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC ≅
      HomotopyHypothesis.Completion.FinitelyCellular.FreeAfin hC := by
  rfl

/-- The prescribed comparison induces an isomorphism after restricting the free globular diagram. -/
def freeRestrictionIso {C : GlobularTheory.{u}} (hC : C.IsCoherator)
    {Y : Type v} [Category.{u} Y] [CategoryWithCofibrations Y]
    (F G : Afin C hC ⥤ Y)
    (e : HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC ⋙ F ≅
      HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC ⋙ G) :
    HomotopyHypothesis.Completion.FinitelyCellular.FreeAfin hC ⋙ F ≅
      HomotopyHypothesis.Completion.FinitelyCellular.FreeAfin hC ⋙ G :=
  Functor.isoWhiskerRight (afinRepresentablesIsoFree hC).symm F ≪≫ e ≪≫
    Functor.isoWhiskerRight (afinRepresentablesIsoFree hC) G

/-- The free-diagram transport has the prescribed component on each theory object. -/
theorem freeRestrictionIso_hom_app {C : GlobularTheory.{u}} (hC : C.IsCoherator)
    {Y : Type v} [Category.{u} Y] [CategoryWithCofibrations Y]
    (F G : Afin C hC ⥤ Y)
    (e : HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC ⋙ F ≅
      HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC ⋙ G) (X : C.Obj) :
    (freeRestrictionIso hC F G e).hom.app X = e.hom.app X := by
  change F.map (𝟙 ((HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC).obj X)) ≫
      e.hom.app X ≫ G.map (𝟙 ((HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC).obj X)) =
    e.hom.app X
  simp

/-- The completion presheaf of an exact functor evaluates at its values. -/
def completionEvaluation {C : GlobularTheory.{u}} (hC : C.IsCoherator)
    (A : Afin C hC) : Completion.{u} (Afin C hC) ⥤ Type u where
  obj P := P.obj.obj (op A)
  map f := f.hom.app (op A)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The restricted Yoneda completion of a functor evaluates as its ordinary Hom functor. -/
def exactFunctorEvaluationIso {C : GlobularTheory.{u}} (hC : C.IsCoherator)
    {Y : Type v} [Category.{u} Y] [CategoryWithCofibrations Y]
    (F : Afin C hC ⥤ Y) (hF : IsCofibrationMorphism F) (A : Afin C hC) :
    exactFunctorCompletion hC F hF ⋙ completionEvaluation hC A ≅
      coyoneda.obj (op (F.obj A)) := by
  rfl

/-- The input isomorphism gives an isomorphism of the associated models at each target object. -/
def exactFunctorPresheafIsoApp {C : GlobularTheory.{u}} (hC : C.IsCoherator)
    {Y : Type v} [Category.{u} Y] [CategoryWithCofibrations Y]
    (F G : Afin C hC ⥤ Y) (hF : IsCofibrationMorphism F) (hG : IsCofibrationMorphism G)
    (e : HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC ⋙ F ≅
      HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC ⋙ G) (Z : Y) :
    (Completion.FinitelyCellular.FreeAfin hC).op ⋙ G.op ⋙ yoneda.obj Z ≅
      (Completion.FinitelyCellular.FreeAfin hC).op ⋙ F.op ⋙ yoneda.obj Z := by
  exact Functor.isoWhiskerRight
    (NatIso.op (freeRestrictionIso hC F G e)) (yoneda.obj Z)

/-- The input isomorphism gives an isomorphism of the associated models at each target object. -/
def exactFunctorModelIsoApp {C : GlobularTheory.{u}} (hC : C.IsCoherator)
    {Y : Type v} [Category.{u} Y] [CategoryWithCofibrations Y]
    (F G : Afin C hC ⥤ Y) (hF : IsCofibrationMorphism F) (hG : IsCofibrationMorphism G)
    (e : HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC ⋙ F ≅
      HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC ⋙ G) (Z : Y) :
    (exactFunctorModel hC G hG).obj Z ≅ (exactFunctorModel hC F hF).obj Z := by
  let s := exactFunctorPresheafIsoApp hC F G hF hG e Z
  exact ⟨s.hom, s.inv, s.hom_inv_id, s.inv_hom_id⟩

/-- The model comparison acts on cells by postcomposition with the restricted comparison. -/
theorem exactFunctorModelIsoApp_apply {C : GlobularTheory.{u}} (hC : C.IsCoherator)
    {Y : Type v} [Category.{u} Y] [CategoryWithCofibrations Y]
    (F G : Afin C hC ⥤ Y) (hF : IsCofibrationMorphism F) (hG : IsCofibrationMorphism G)
    (e : HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC ⋙ F ≅
      HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC ⋙ G) (Z : Y) (X : C.Obj)
    (x : ((exactFunctorModel hC G hG).obj Z).presheaf.obj (op X)) :
    (exactFunctorModelIsoApp hC F G hF hG e Z).hom.app (op X) x =
      ((freeRestrictionIso hC F G e).hom.app X) ≫ x := by
  simp [exactFunctorModelIsoApp, exactFunctorPresheafIsoApp,
    Functor.whiskerRight, Functor.isoWhiskerRight, NatTrans.op]
  rfl

/-- The prescribed comparison extends to a natural isomorphism between the associated models. -/
def exactFunctorModelIso {C : GlobularTheory.{u}} (hC : C.IsCoherator)
    {Y : Type v} [Category.{u} Y] [CategoryWithCofibrations Y]
    (F G : Afin C hC ⥤ Y) (hF : IsCofibrationMorphism F) (hG : IsCofibrationMorphism G)
    (e : HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC ⋙ F ≅
      HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC ⋙ G) :
    exactFunctorModel hC G hG ≅ exactFunctorModel hC F hF :=
  NatIso.ofComponents (fun Z => exactFunctorModelIsoApp hC F G hF hG e Z) (by
    intro Z Z' f
    apply NatTrans.ext
    funext X
    ext x
    change (Completion.FinitelyCellular.FreeAfin hC ⋙ G).obj X.unop ⟶ Z at x
    change ((freeRestrictionIso hC F G e).app X.unop).hom ≫ (x ≫ f) =
      (((freeRestrictionIso hC F G e).app X.unop).hom ≫ x) ≫ f
    rw [← Category.assoc])

/-- The model comparison induces a comparison of completion presheaves. -/
def exactFunctorCompletionIso {C : GlobularTheory.{u}} (hC : C.IsCoherator)
    {Y : Type v} [Category.{u} Y] [CategoryWithCofibrations Y]
    (F G : Afin C hC ⥤ Y) (hF : IsCofibrationMorphism F) (hG : IsCofibrationMorphism G)
    (e : HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC ⋙ F ≅
      HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC ⋙ G) :
    exactFunctorCompletion hC G hG ≅ exactFunctorCompletion hC F hF := by
  let hG' := Functor.isoWhiskerLeft (exactFunctorCompletion hC G hG)
    (HomotopyHypothesis.Completion.FinitelyCellular.counitNatIso hC)
  let hF' := Functor.isoWhiskerLeft (exactFunctorCompletion hC F hF)
    (HomotopyHypothesis.Completion.FinitelyCellular.counitNatIso hC)
  exact hG'.symm ≪≫
    Functor.isoWhiskerRight (exactFunctorModelIso hC F G hF hG e)
      (HomotopyHypothesis.Blueprint.Packages.restriction hC) ≪≫ hF'

/-- Evaluation of the completion comparison is an isomorphism of co-Yoneda functors. -/
def exactFunctorRepresentableIso {C : GlobularTheory.{u}} (hC : C.IsCoherator)
    {Y : Type v} [Category.{u} Y] [CategoryWithCofibrations Y]
    (F G : Afin C hC ⥤ Y) (hF : IsCofibrationMorphism F) (hG : IsCofibrationMorphism G)
    (e : HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC ⋙ F ≅
      HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC ⋙ G) (A : Afin C hC) :
    coyoneda.obj (op (G.obj A)) ≅ coyoneda.obj (op (F.obj A)) := by
  exact (exactFunctorEvaluationIso hC G hG A).symm ≪≫
    Functor.isoWhiskerRight (exactFunctorCompletionIso hC F G hF hG e)
      (completionEvaluation hC A) ≪≫
    exactFunctorEvaluationIso hC F hF A

/-- Evaluation of the representable comparison is evaluation of the completion isomorphism. -/
theorem exactFunctorRepresentableIso_hom_app {C : GlobularTheory.{u}} (hC : C.IsCoherator)
    {Y : Type v} [Category.{u} Y] [CategoryWithCofibrations Y]
    (F G : Afin C hC ⥤ Y) (hF : IsCofibrationMorphism F) (hG : IsCofibrationMorphism G)
    (e : HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC ⋙ F ≅
      HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC ⋙ G) (A : Afin C hC)
    (Z : Y) (x : (coyoneda.obj (op (G.obj A))).obj Z) :
    (exactFunctorRepresentableIso hC F G hF hG e A).hom.app Z x =
      ((exactFunctorCompletionIso hC F G hF hG e).app Z).hom.hom.app (op A) x := by
  change (completionEvaluation hC A).map
      ((exactFunctorCompletionIso hC F G hF hG e).app Z).hom x =
    ((exactFunctorCompletionIso hC F G hF hG e).app Z).hom.hom.app (op A) x
  rfl

/-- The co-Yoneda comparison determines an isomorphism of target objects. -/
def exactFunctorComparisonIsoApp {C : GlobularTheory.{u}} (hC : C.IsCoherator)
    {Y : Type v} [Category.{u} Y] [CategoryWithCofibrations Y]
    (F G : Afin C hC ⥤ Y) (hF : IsCofibrationMorphism F) (hG : IsCofibrationMorphism G)
    (e : HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC ⋙ F ≅
      HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC ⋙ G) (A : Afin C hC) :
    F.obj A ≅ G.obj A :=
  (Coyoneda.fullyFaithful (C := Y)).preimageIso
      (exactFunctorRepresentableIso hC F G hF hG e A) |>.unop

/-- The object comparisons are natural as maps in the opposite category. -/
def exactFunctorComparisonOppIso {C : GlobularTheory.{u}} (hC : C.IsCoherator)
    {Y : Type v} [Category.{u} Y] [CategoryWithCofibrations Y]
    (F G : Afin C hC ⥤ Y) (hF : IsCofibrationMorphism F) (hG : IsCofibrationMorphism G)
    (e : HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC ⋙ F ≅
      HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC ⋙ G) :
    G.op ≅ F.op :=
  NatIso.ofComponents
    (fun A => (Coyoneda.fullyFaithful (C := Y)).preimageIso
      (exactFunctorRepresentableIso hC F G hF hG e A.unop))
    (by
      intro A B f
      apply (Coyoneda.fullyFaithful (C := Y)).map_injective
      ext Z g
      let q := exactFunctorCompletionIso hC F G hF hG e
      have hq := (q.app Z).hom.hom.naturality f
      have hqg := congrArg (fun k => k g) hq
      simp only [Functor.map_comp, Functor.FullyFaithful.preimageIso,
        Functor.FullyFaithful.map_preimage, exactFunctorRepresentableIso,
        exactFunctorEvaluationIso]
      exact hqg)

/-- The target functors are naturally isomorphic. -/
def exactFunctorComparisonIso {C : GlobularTheory.{u}} (hC : C.IsCoherator)
    {Y : Type v} [Category.{u} Y] [CategoryWithCofibrations Y]
    (F G : Afin C hC ⥤ Y) (hF : IsCofibrationMorphism F) (hG : IsCofibrationMorphism G)
    (e : HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC ⋙ F ≅
      HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC ⋙ G) : F ≅ G :=
  NatIso.unop (exactFunctorComparisonOppIso hC F G hF hG e)

/-- At a representable model, the completion comparison is the prescribed comparison map. -/
@[simp]
theorem exactFunctorCompletionIso_free_app {C : GlobularTheory.{u}} (hC : C.IsCoherator)
    {Y : Type v} [Category.{u} Y] [CategoryWithCofibrations Y]
    (F G : Afin C hC ⥤ Y) (hF : IsCofibrationMorphism F) (hG : IsCofibrationMorphism G)
    (e : HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC ⋙ F ≅
      HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC ⋙ G)
    (X : C.Obj) (Z : Y)
    (g : G.obj ((HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC).obj X) ⟶ Z) :
    ((exactFunctorCompletionIso hC F G hF hG e).app Z).hom.hom.app
      (op ((HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC).obj X)) g =
        ((freeRestrictionIso hC F G e).app X).hom ≫ g := by
  let PG := (exactFunctorCompletion hC G hG).obj Z
  let PF := (exactFunctorCompletion hC F hF).obj Z
  let A := (HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC).obj X
  let EG := Equiv.ofBijective (Completion.FinitelyCellular.thetaMap hC PG A)
    (Completion.FinitelyCellular.theta_bijective hC PG A)
  let EF := Equiv.ofBijective (Completion.FinitelyCellular.thetaMap hC PF A)
    (Completion.FinitelyCellular.theta_bijective hC PF A)
  let β := exactFunctorModelIsoApp hC F G hF hG e Z
  have hθGapp : (Completion.FinitelyCellular.thetaMap hC PG A g).app (op X) (𝟙 X) = g := by
    change PG.obj.map (Completion.FinitelyCellular.elemMap hC A (𝟙 X)).op g = g
    have helem : Completion.FinitelyCellular.elemMap hC A (𝟙 X) = 𝟙 A := by
      apply ObjectProperty.hom_ext
      show (yonedaEquiv (X := X)).symm (𝟙 X) = 𝟙 (yoneda.obj X)
      have h : yonedaEquiv (X := X) (𝟙 (yoneda.obj X)) = 𝟙 X := rfl
      rw [← h, Equiv.symm_apply_apply]
    rw [helem]
    show PG.obj.map (𝟙 (op A)) g = g
    rw [PG.obj.map_id]
    rfl
  have hθFapp (z : PF.obj.obj (op A)) :
      (Completion.FinitelyCellular.thetaMap hC PF A z).app (op X) (𝟙 X) = z := by
    change PF.obj.map (Completion.FinitelyCellular.elemMap hC A (𝟙 X)).op z = z
    have helem : Completion.FinitelyCellular.elemMap hC A (𝟙 X) = 𝟙 A := by
      apply ObjectProperty.hom_ext
      show (yonedaEquiv (X := X)).symm (𝟙 X) = 𝟙 (yoneda.obj X)
      have h : yonedaEquiv (X := X) (𝟙 (yoneda.obj X)) = 𝟙 X := rfl
      rw [← h, Equiv.symm_apply_apply]
    rw [helem]
    show PF.obj.map (𝟙 (op A)) z = z
    rw [PF.obj.map_id]
    rfl
  have hβ : Completion.FinitelyCellular.thetaMap hC PG A g ≫ β.hom =
      Completion.FinitelyCellular.thetaMap hC PF A (((freeRestrictionIso hC F G e).app X).hom ≫ g) := by
    apply (yonedaEquiv (X := X)).injective
    change (β.hom.app (op X))
        ((Completion.FinitelyCellular.thetaMap hC PG A g).app (op X) (𝟙 X)) =
      (Completion.FinitelyCellular.thetaMap hC PF A (((freeRestrictionIso hC F G e).app X).hom ≫ g)).app
        (op X) (𝟙 X)
    rw [hθGapp,
      hθFapp (((freeRestrictionIso hC F G e).app X).hom ≫ g)]
    exact exactFunctorModelIsoApp_apply hC F G hF hG e Z X g
  change EF.symm (Completion.FinitelyCellular.thetaMap hC PG A g ≫ β.hom) =
    ((freeRestrictionIso hC F G e).app X).hom ≫ g
  rw [hβ]
  exact EF.symm_apply_apply _

/-- The isomorphism of exact functors retains the prescribed components on free models. -/
theorem exactFunctorComparisonIso_restrict {C : GlobularTheory.{u}} (hC : C.IsCoherator)
    {Y : Type v} [Category.{u} Y] [CategoryWithCofibrations Y]
    (F G : Afin C hC ⥤ Y) (hF : IsCofibrationMorphism F) (hG : IsCofibrationMorphism G)
    (e : HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC ⋙ F ≅
      HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC ⋙ G) :
    Functor.isoWhiskerLeft (HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC)
      (exactFunctorComparisonIso hC F G hF hG e) = e := by
  ext X
  apply Quiver.Hom.op_inj
  apply (Coyoneda.fullyFaithful (C := Y)).map_injective
  ext Z g
  have hchain :
      (exactFunctorRepresentableIso hC F G hF hG e
        ((HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC).obj X)).hom.app Z g =
        e.hom.app X ≫ g := by
    have h1 := exactFunctorRepresentableIso_hom_app hC F G hF hG e
      ((HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC).obj X) Z g
    have h2 := exactFunctorCompletionIso_free_app hC F G hF hG e X Z g
    have h3 : (freeRestrictionIso hC F G e).hom.app X ≫ g = e.hom.app X ≫ g := by
      rw [freeRestrictionIso_hom_app]
      rfl
    exact h1.trans (h2.trans h3)
  simpa [exactFunctorComparisonIso, exactFunctorComparisonOppIso] using hchain

/-- The isomorphism of representable restrictions extends to exact functors. -/
theorem afinFunctorComparisonStatement_proof {C : GlobularTheory.{u}} (hC : C.IsCoherator)
    {Y : Type v} [Category.{u} Y] [CategoryWithCofibrations Y] [IsCofibrationCategory Y]
    (F G : Afin C hC ⥤ Y) (hF : IsCofibrationMorphism F) (hG : IsCofibrationMorphism G)
    (e : HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC ⋙ F ≅
      HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC ⋙ G) :
    HomotopyHypothesis.FiniteCategory.Lifting.AfinFunctorComparisonStatement hC F G hF hG e := by
  exact ⟨exactFunctorComparisonIso hC F G hF hG e,
    exactFunctorComparisonIso_restrict hC F G hF hG e⟩

example {C : GlobularTheory.{u}} (hC : C.IsCoherator)
    {Y : Type v} [Category.{u} Y] [CategoryWithCofibrations Y] [IsCofibrationCategory Y]
    (F G : Afin C hC ⥤ Y) (hF : IsCofibrationMorphism F) (hG : IsCofibrationMorphism G)
    (e : HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC ⋙ F ≅
      HomotopyHypothesis.FiniteCategory.Lifting.afinRepresentables hC ⋙ G) :
    HomotopyHypothesis.FiniteCategory.Lifting.AfinFunctorComparisonStatement hC F G hF hG e :=
  afinFunctorComparisonStatement_proof hC F G hF hG e

end HomotopyHypothesis.FiniteCategory.Comparison

#print axioms HomotopyHypothesis.FiniteCategory.Comparison.afinFunctorComparisonStatement_proof
