import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Presentable.Finite
import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.Packages.Classical.FinCellIsCylinderCategory
import HomotopyHypothesis.Blueprint.Henry.Packages.General.CompletionIsSemiModelCategory
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.DiskBoundaryIsFiniteCellComplex
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.FinCellEssentiallySmall
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Blueprint.Henry.Topology
noncomputable section

universe u

open CategoryTheory Limits HomotopicalAlgebra HomotopyHypothesis.Henry Opposite

local instance : Fact (Cardinal.aleph0.{u}).IsRegular := Cardinal.fact_isRegular_aleph0
local instance : OrderBot Cardinal.aleph0.{u}.ord.ToType :=
  Cardinal.orderBotAleph0OrdToType

namespace HomotopyHypothesis.FiniteCategory.Restriction

private theorem unique_of_filtered_colimit {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Type u) (hF : ∀ j, Unique (F.obj j)) :
    Nonempty (Unique (colimit F)) := by
  letI : IsConnected J := IsFiltered.isConnected J
  let eStage : F ≅ (Functor.const J).obj PUnit :=
    NatIso.ofComponents (fun j => by
      letI : Unique (F.obj j) := hF j
      exact Equiv.toIso (Equiv.equivPUnit (F.obj j)))
      (by
        intro j j' f
        ext x
        simp [Equiv.equivPUnit])
  let e : colimit F ≅ PUnit :=
    HasColimit.isoOfNatIso eStage ≪≫ Limits.Types.colimitConstPUnitIsoPUnit (C := J)
  refine ⟨⟨⟨e.inv PUnit.unit⟩, ?_⟩⟩
  intro x
  have hx : ConcreteCategory.hom e.hom x =
      ConcreteCategory.hom e.hom (e.inv PUnit.unit) := Subsingleton.elim _ _
  calc
    x = ConcreteCategory.hom e.inv (ConcreteCategory.hom e.hom x) := by simp
    _ = ConcreteCategory.hom e.inv (ConcreteCategory.hom e.hom (e.inv PUnit.unit)) := by rw [hx]
    _ = e.inv PUnit.unit := by simp

private def evalFamily {C : Type (u + 1)} [Category.{u} C]
    {J : Type u} [SmallCategory J] (F : J ⥤ Cᵒᵖ ⥤ Type u) :
    Cᵒᵖ ⥤ (J ⥤ Type u) where
  obj Z := F ⋙ (evaluation Cᵒᵖ (Type u)).obj Z
  map f :=
    { app j := (F.obj j).map f
      naturality {j j'} g := by
        exact (F.map g).naturality f |>.symm }

private theorem colim_map_eq_colimMap {J : Type u} [SmallCategory J]
    {F G : J ⥤ Type u} (η : F ⟶ G) :
    (colim : (J ⥤ Type u) ⥤ Type u).map η = colimMap η := by
  apply colimit.hom_ext
  intro j
  simp

@[simp] private theorem colimMap_id {J : Type u} [SmallCategory J] (F : J ⥤ Type u) :
    colimMap (𝟙 F) = 𝟙 (colimit F) := by
  apply colimit.hom_ext
  intro j
  simp

private theorem completionInitialColimit
    {C : Type (u + 1)} [Category.{u} C] [CategoryWithCofibrations C]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Cᵒᵖ ⥤ Type u)
    (hF : ∀ j, IsCompletionPresheaf C (F.obj j))
    {I : C} (hI : IsInitial I) :
    Nonempty (Unique ((colimit F).obj (op I))) := by
  letI : IsConnected J := IsFiltered.isConnected J
  have hU (j : J) : Unique ((F.obj j).obj (op I)) := Classical.choice (hF j |>.1 hI)
  have eStage : F ⋙ (evaluation Cᵒᵖ (Type u)).obj (op I) ≅ (Functor.const J).obj PUnit :=
    NatIso.ofComponents (fun j => by
      letI : Unique ((F.obj j).obj (op I)) := hU j
      exact Equiv.toIso (Equiv.equivPUnit ((F.obj j).obj (op I))))
      (by intro j j' f; ext x; simp [Equiv.equivPUnit])
  let e : (colimit F).obj (op I) ≅ PUnit :=
    colimitObjIsoColimitCompEvaluation F (op I) ≪≫
      HasColimit.isoOfNatIso eStage ≪≫ Limits.Types.colimitConstPUnitIsoPUnit (C := J)
  refine ⟨⟨⟨e.inv PUnit.unit⟩, ?_⟩⟩
  intro x
  have hx : ConcreteCategory.hom e.hom x =
      ConcreteCategory.hom e.hom (e.inv PUnit.unit) := Subsingleton.elim _ _
  calc
    x = ConcreteCategory.hom e.inv (ConcreteCategory.hom e.hom x) := by simp
    _ = ConcreteCategory.hom e.inv (ConcreteCategory.hom e.hom (e.inv PUnit.unit)) := by rw [hx]
    _ = e.inv PUnit.unit := by simp

private theorem completionPresheaf_colimit_filtered
    {C : Type (u + 1)} [Category.{u} C] [CategoryWithCofibrations C]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Cᵒᵖ ⥤ Type u)
    (hF : ∀ j, IsCompletionPresheaf C (F.obj j)) :
    IsCompletionPresheaf C (colimit F) := by
  refine ⟨fun I hI => completionInitialColimit F hF hI,
    fun A B X Q i f k g h hi => ?_⟩
  let cosp : WalkingCospan ⥤ Cᵒᵖ := cospan i.op f.op
  let kN := (evalFamily F).map k.op
  let gN := (evalFamily F).map g.op
  let iN := (evalFamily F).map i.op
  let fN := (evalFamily F).map f.op
  have hOpp : k.op ≫ i.op = g.op ≫ f.op := by
    simpa using congrArg Quiver.Hom.op h.w
  have hcomm : kN ≫ iN = gN ≫ fN := by
    ext s
    simp [kN, iN, gN, fN, evalFamily, ← Functor.map_comp, hOpp]
  let hPull (s : J) : IsPullback ((F.obj s).map k.op) ((F.obj s).map g.op)
      ((F.obj s).map i.op) ((F.obj s).map f.op) := (hF s).2 i f k g h hi
  let H : WalkingCospan ⥤ J ⥤ Type u := cospan iN fN
  let cCone : Cone H := PullbackCone.mk kN gN hcomm
  have hStage (s : J) : IsLimit
      (((evaluation J (Type u)).obj s).mapCone cCone) := by
    let ev := (evaluation J (Type u)).obj s
    let eCosp := cospanCompIso ev iN fN
    let cPost := (Cone.postcompose eCosp.inv).obj (hPull s).cone
    have hPost : IsLimit cPost :=
      (IsLimit.postcomposeInvEquiv eCosp (hPull s).cone).symm (hPull s).isLimit
    have eStage : cPost ≅ ev.mapCone cCone := by
      refine Cone.ext (Iso.refl _) ?_
      rintro (⟨⟩ | ⟨⟨⟩⟩)
      · rfl
      · rfl
      · rfl
    exact hPost.ofIsoLimit eStage
  have hCone : IsLimit cCone := evaluationJointlyReflectsLimits cCone hStage
  have hColim : IsLimit ((colim : (J ⥤ Type u) ⥤ Type u).mapCone cCone) :=
    isLimitOfPreserves (colim : (J ⥤ Type u) ⥤ Type u) hCone
  have hEval : evalFamily F = F.flip := rfl
  have hPsh : colimit F ≅ evalFamily F ⋙ colim := by
    simpa only [hEval, Functor.flip_flip] using colimitFlipIsoCompColim (F.flip)
  let hCosp : cosp ⋙ evalFamily F ≅ H := cospanCompIso (evalFamily F) i.op f.op
  let hDiagram : H ⋙ colim ≅ cosp ⋙ colimit F := by
    calc
      _ ≅ (cosp ⋙ evalFamily F) ⋙ colim := Functor.isoWhiskerRight hCosp.symm colim
      _ ≅ cosp ⋙ (evalFamily F ⋙ colim) := Functor.associator _ _ _
      _ ≅ cosp ⋙ colimit F := Functor.isoWhiskerLeft cosp hPsh.symm
  let c1 := (Cone.postcompose hDiagram.hom).obj
    ((colim : (J ⥤ Type u) ⥤ Type u).mapCone cCone)
  have h1 : IsLimit c1 :=
    (IsLimit.postcomposeHomEquiv hDiagram
      ((colim : (J ⥤ Type u) ⥤ Type u).mapCone cCone)).symm hColim
  let eQ : (colimit F).obj (op Q) ≅ colimit (F ⋙ (evaluation Cᵒᵖ (Type u)).obj (op Q)) :=
    hPsh.app (op Q)
  let c2 := c1.extend eQ.hom
  have hExtend : c1 ≅ c2 := Cone.extendIso c1 eQ.symm
  have h2 : IsLimit c2 := IsLimit.ofIsoLimit h1 hExtend
  have hPullback := IsPullback.of_isLimit_cone h2
  have hDiagramLeft : hDiagram.hom.app WalkingCospan.left = hPsh.inv.app (op B) := by
    apply colimit.hom_ext
    intro j
    simp [hDiagram, hCosp, cosp, H]
  have hDiagramRight : hDiagram.hom.app WalkingCospan.right = hPsh.inv.app (op X) := by
    apply colimit.hom_ext
    intro j
    simp [hDiagram, hCosp, cosp, H]
  have hNatK : (colimit F).map k.op ≫ hPsh.hom.app (op B) =
      hPsh.hom.app (op Q) ≫ (colim : (J ⥤ Type u) ⥤ Type u).map
        ((evalFamily F).map k.op) := by
    simpa only [Functor.comp_map] using hPsh.hom.naturality k.op
  have hNatG : (colimit F).map g.op ≫ hPsh.hom.app (op X) =
      hPsh.hom.app (op Q) ≫ (colim : (J ⥤ Type u) ⥤ Type u).map
        ((evalFamily F).map g.op) := by
    simpa only [Functor.comp_map] using hPsh.hom.naturality g.op
  have hColimMapK := colim_map_eq_colimMap ((evalFamily F).map k.op)
  have hColimMapG := colim_map_eq_colimMap ((evalFamily F).map g.op)
  have hNatK' : (colimit F).map k.op ≫ hPsh.hom.app (op B) =
      hPsh.hom.app (op Q) ≫ colimMap ((evalFamily F).map k.op) := by
    rw [← hColimMapK]
    exact hNatK
  have hNatG' : (colimit F).map g.op ≫ hPsh.hom.app (op X) =
      hPsh.hom.app (op Q) ≫ colimMap ((evalFamily F).map g.op) := by
    rw [← hColimMapG]
    exact hNatG
  have hfst : c2.π.app WalkingCospan.left = (colimit F).map k.op := by
    change eQ.hom ≫ _ ≫ hDiagram.hom.app WalkingCospan.left = _
    rw [hDiagramLeft]
    change (hPsh.hom.app (op Q) ≫ colimMap ((evalFamily F).map k.op)) ≫
        hPsh.inv.app (op B) = (colimit F).map k.op
    calc
      _ = ((colimit F).map k.op ≫ hPsh.hom.app (op B)) ≫ hPsh.inv.app (op B) := by
        exact congrArg (fun m => m ≫ hPsh.inv.app (op B)) hNatK'.symm
      _ = (colimit F).map k.op := by
        calc
          _ = (colimit F).map k.op ≫
              (hPsh.hom.app (op B) ≫ hPsh.inv.app (op B)) := by rw [Category.assoc]
          _ = (colimit F).map k.op ≫ 𝟙 _ := by
            rw [hPsh.hom_inv_id_app (op B)]
          _ = (colimit F).map k.op := by simp
  have hsnd : c2.π.app WalkingCospan.right = (colimit F).map g.op := by
    change eQ.hom ≫ _ ≫ hDiagram.hom.app WalkingCospan.right = _
    rw [hDiagramRight]
    change (hPsh.hom.app (op Q) ≫ colimMap ((evalFamily F).map g.op)) ≫
        hPsh.inv.app (op X) = (colimit F).map g.op
    calc
      _ = ((colimit F).map g.op ≫ hPsh.hom.app (op X)) ≫ hPsh.inv.app (op X) := by
        exact congrArg (fun m => m ≫ hPsh.inv.app (op X)) hNatG'.symm
      _ = (colimit F).map g.op := by
        calc
          _ = (colimit F).map g.op ≫
              (hPsh.hom.app (op X) ≫ hPsh.inv.app (op X)) := by rw [Category.assoc]
          _ = (colimit F).map g.op ≫ 𝟙 _ := by
            rw [hPsh.hom_inv_id_app (op X)]
          _ = (colimit F).map g.op := by simp
  simpa [cosp, cospan, c1, c2, hfst, hsnd] using hPullback

private instance completionPresheaf_isClosedUnderIsomorphisms
    {C : Type (u + 1)} [Category.{u} C] [CategoryWithCofibrations C] :
    ObjectProperty.IsClosedUnderIsomorphisms (IsCompletionPresheaf C) where
  of_iso := by
    intro X Y e hX
    refine ⟨?_, ?_⟩
    · intro I hI
      obtain ⟨hU⟩ := hX.1 hI
      letI : Unique (X.obj (op I)) := hU
      letI : Unique (Y.obj (op I)) :=
        Equiv.unique (e.app (op I)).toEquiv.symm
      exact ⟨inferInstance⟩
    · intro A B X Q i f k j h hi
      exact (hX.2 i f k j h hi).of_iso
        (e.app (op Q)) (e.app (op B)) (e.app (op X)) (e.app (op A))
        (by simpa using e.hom.naturality k.op)
        (by simpa using e.hom.naturality j.op)
        (by simpa using e.hom.naturality i.op)
        (by simpa using e.hom.naturality f.op)

private theorem completion_hasFilteredColimitsOfSize
    {C : Type (u + 1)} [Category.{u} C] [CategoryWithCofibrations C] :
    HasFilteredColimitsOfSize.{u, u} (Completion.{u} C) := by
  constructor
  intro J _ hJ
  let P : ObjectProperty (Cᵒᵖ ⥤ Type u) := IsCompletionPresheaf C
  have hClosed : P.IsClosedUnderColimitsOfShape J := by
    rw [ObjectProperty.isClosedUnderColimitsOfShape_iff]
    intro X hX
    rcases hX with ⟨hX⟩
    have hp : P (colimit hX.diag) :=
      completionPresheaf_colimit_filtered hX.diag hX.prop_diag_obj
    let e : colimit hX.diag ≅ X :=
      (colimit.isColimit hX.diag).coconePointUniqueUpToIso hX.isColimit
    exact P.prop_of_iso e hp
  letI : P.IsClosedUnderColimitsOfShape J := hClosed
  exact Limits.hasColimitsOfShape_of_closedUnderColimits J P

theorem finCellCompletion_hasColimits :
    HasColimitsOfSize.{u, u} (Completion.{u} FinCell.{u}) := by
  letI : IsCylinderCategory FinCell.{u} := Packages.finCell_isCylinderCategory
  letI : EssentiallySmall.{u} FinCell.{u} := Packages.finCell_essentiallySmall
  let hSemi := Packages.completion_isSemiModelCategory (C := FinCell.{u})
  letI : HasFiniteColimits (Completion.{u} FinCell.{u}) := hSemi.1.hasFiniteColimits
  letI : HasFilteredColimitsOfSize.{u, u} (Completion.{u} FinCell.{u}) :=
    completion_hasFilteredColimitsOfSize
  exact has_colimits_of_finite_and_filtered

private theorem finCellCompletion_locallySmall [EssentiallySmall.{u} FinCell.{u}] :
    LocallySmall.{u} (Completion.{u} FinCell.{u}) := by
  let S := SmallModel FinCell.{u}
  let e : FinCell.{u} ≌ S := equivSmallModel FinCell.{u}
  let eP : (FinCell.{u}ᵒᵖ ⥤ Type u) ≌ (Sᵒᵖ ⥤ Type u) := e.op.congrLeft
  let F : Completion.{u} FinCell.{u} ⥤ (Sᵒᵖ ⥤ Type u) :=
    ObjectProperty.ι (IsCompletionPresheaf FinCell.{u}) ⋙ eP.functor
  have hF : F.Faithful := by infer_instance
  exact locallySmall_of_faithful F

noncomputable def completionYonedaRawIso (A : FinCell.{u}) :
    (ObjectProperty.ι (IsCompletionPresheaf FinCell.{u})).obj
      ((Completion.yoneda FinCell.{u}).obj A) ≅ yoneda.obj A := by
  let W : (FinCell.{u}ᵒᵖ ⥤ Type u) ⥤ (FinCell.{u}ᵒᵖ ⥤ Type u) :=
    (Functor.whiskeringLeft _ _ _).obj (𝟭 FinCell.{u}).op
  let eW : W ≅ 𝟭 (FinCell.{u}ᵒᵖ ⥤ Type u) :=
    (Functor.whiskeringLeft _ _ _).mapIso (Functor.opId FinCell.{u}) ≪≫
      Functor.whiskeringLeftObjIdIso
  let eY : yoneda ⋙ W ≅ yoneda := by
    exact Functor.isoWhiskerLeft (yoneda : FinCell.{u} ⥤ FinCell.{u}ᵒᵖ ⥤ Type u) eW
  let P : ObjectProperty (FinCell.{u}ᵒᵖ ⥤ Type u) := IsCompletionPresheaf FinCell.{u}
  let y := (Completion.yoneda FinCell.{u}).obj A
  have eA : (P.ι.obj y) ≅ yoneda.obj A := by
    change W.obj (yoneda.obj A) ≅ yoneda.obj A
    exact eY.app A
  exact eA

private noncomputable def finCellRawYoneda :
    FinCell.{u} ⥤ Completion.{u} FinCell.{u} :=
  ObjectProperty.lift (IsCompletionPresheaf FinCell.{u}) yoneda fun A =>
    ObjectProperty.prop_of_iso (IsCompletionPresheaf FinCell.{u}) (completionYonedaRawIso A)
      ((Completion.yoneda FinCell.{u}).obj A).property

private noncomputable def finCellRawYonedaEquiv (A : FinCell.{u})
    (X : Completion.{u} FinCell.{u}) :
    ((finCellRawYoneda.{u}).obj A ⟶ X) ≃ X.1.obj (op A) where
  toFun f := yonedaEquiv f.hom
  invFun x := ObjectProperty.homMk (P := IsCompletionPresheaf FinCell.{u})
    (yonedaEquiv.symm x)
  left_inv f := by
    apply ObjectProperty.hom_ext
    change yonedaEquiv.symm (yonedaEquiv f.hom) = f.hom
    exact Equiv.symm_apply_apply _ _
  right_inv x := by
    change yonedaEquiv (yonedaEquiv.symm x) = x
    exact Equiv.apply_symm_apply _ _

private theorem finCellRawYonedaEquiv_comp {A : FinCell.{u}}
    {X Y : Completion.{u} FinCell.{u}}
    (f : (finCellRawYoneda.{u}).obj A ⟶ X) (g : X ⟶ Y) :
    finCellRawYonedaEquiv A Y (f ≫ g) =
      g.hom.app (op A) (finCellRawYonedaEquiv A X f) := by
  change yonedaEquiv (f.hom ≫ g.hom) = g.hom.app (op A) (yonedaEquiv f.hom)
  exact yonedaEquiv_comp f.hom g.hom

private theorem finCellRawYonedaEquiv_map {A B : FinCell.{u}} (i : A ⟶ B) :
    finCellRawYonedaEquiv A ((finCellRawYoneda.{u}).obj B)
      ((finCellRawYoneda.{u}).map i) = i := by
  change yonedaEquiv (yoneda.map i) = i
  exact yonedaEquiv_yoneda_map i

private theorem finCellRawYonedaEquiv_precomp {A B : FinCell.{u}}
    {X : Completion.{u} FinCell.{u}} (i : A ⟶ B)
    (f : (finCellRawYoneda.{u}).obj B ⟶ X) :
    finCellRawYonedaEquiv A X ((finCellRawYoneda.{u}).map i ≫ f) =
      X.1.map i.op (finCellRawYonedaEquiv B X f) := by
  rw [finCellRawYonedaEquiv_comp, finCellRawYonedaEquiv_map]
  exact (map_yonedaEquiv f.hom i).symm

noncomputable def completionYonedaEquiv (A : FinCell.{u})
    (X : Completion.{u} FinCell.{u}) :
    ((Completion.yoneda FinCell.{u}).obj A ⟶ X) ≃ X.1.obj (op A) :=
  (ObjectProperty.fullyFaithfulι (IsCompletionPresheaf FinCell.{u})).homEquiv.trans
    ((Iso.homCongr (completionYonedaRawIso A) (Iso.refl X.1)).trans
      (yonedaEquiv (X := A) (F := X.1)))

@[simp]
theorem completionYonedaEquiv_apply {A : FinCell.{u}}
    {X : Completion.{u} FinCell.{u}} (f : (Completion.yoneda FinCell.{u}).obj A ⟶ X) :
    completionYonedaEquiv A X f =
      yonedaEquiv ((completionYonedaRawIso A).inv ≫ f.hom) := by
  rfl

theorem completionYonedaEquiv_comp {A : FinCell.{u}}
    {X Y : Completion.{u} FinCell.{u}}
    (f : (Completion.yoneda FinCell.{u}).obj A ⟶ X) (g : X ⟶ Y) :
    completionYonedaEquiv A Y (f ≫ g) =
      g.hom.app (op A) (completionYonedaEquiv A X f) := by
  rw [completionYonedaEquiv_apply, completionYonedaEquiv_apply]
  change yonedaEquiv ((completionYonedaRawIso A).inv ≫ (f ≫ g).hom) = _
  simpa [ObjectProperty.FullSubcategory.comp_hom, Category.assoc] using
    (yonedaEquiv_comp ((completionYonedaRawIso A).inv ≫ f.hom) g.hom)

private theorem completionYonedaRawIso_inv_naturality {A B : FinCell.{u}} (i : A ⟶ B) :
    (completionYonedaRawIso A).inv ≫ ((Completion.yoneda FinCell.{u}).map i).hom =
      yoneda.map i ≫ (completionYonedaRawIso B).inv := by
  let W : (FinCell.{u}ᵒᵖ ⥤ Type u) ⥤ (FinCell.{u}ᵒᵖ ⥤ Type u) :=
    (Functor.whiskeringLeft _ _ _).obj (𝟭 FinCell.{u}).op
  let eW : W ≅ 𝟭 (FinCell.{u}ᵒᵖ ⥤ Type u) :=
    (Functor.whiskeringLeft _ _ _).mapIso (Functor.opId FinCell.{u}) ≪≫
      Functor.whiskeringLeftObjIdIso
  let eY : yoneda ⋙ W ≅ yoneda := by
    exact Functor.isoWhiskerLeft (yoneda : FinCell.{u} ⥤ FinCell.{u}ᵒᵖ ⥤ Type u) eW
  have h := eY.inv.naturality i
  simpa [completionYonedaRawIso, Completion.yoneda, restrictionAlong,
    ObjectProperty.lift, W, eW, eY] using h.symm

theorem completionYonedaEquiv_precomp {A B : FinCell.{u}}
    {X : Completion.{u} FinCell.{u}} (i : A ⟶ B)
    (f : (Completion.yoneda FinCell.{u}).obj B ⟶ X) :
    completionYonedaEquiv A X ((Completion.yoneda FinCell.{u}).map i ≫ f) =
      X.1.map i.op (completionYonedaEquiv B X f) := by
  rw [completionYonedaEquiv_apply, completionYonedaEquiv_apply]
  change yonedaEquiv (((completionYonedaRawIso A).inv ≫
    ((Completion.yoneda FinCell.{u}).map i).hom) ≫ f.hom) = _
  rw [completionYonedaRawIso_inv_naturality, Category.assoc]
  let f' := (completionYonedaRawIso B).inv ≫ f.hom
  calc
    _ = f'.app (op A) i := by
      change yonedaEquiv (yoneda.map i ≫ f') = _
      rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    _ = X.1.map i.op (completionYonedaEquiv B X f) := by
      rw [completionYonedaEquiv_apply]
      change f'.app (op A) i = X.1.map i.op (yonedaEquiv f')
      exact (map_yonedaEquiv f' i).symm

theorem completionYoneda_map_cofPushout
    {A B X Q : FinCell.{u}} (i : A ⟶ B) (f : A ⟶ X)
    (k : B ⟶ Q) (j : X ⟶ Q) (h : IsPushout i f k j)
    (hi : cofibrations FinCell.{u} i) :
    IsPushout ((Completion.yoneda FinCell.{u}).map i)
      ((Completion.yoneda FinCell.{u}).map f)
      ((Completion.yoneda FinCell.{u}).map k)
      ((Completion.yoneda FinCell.{u}).map j) := by
  let y := Completion.yoneda FinCell.{u}
  apply IsPushout.mk'
  · simpa only [Functor.map_comp] using congrArg y.map h.w
  · intro T m n hm hn
    apply (completionYonedaEquiv Q T).injective
    have hm' : T.1.map k.op (completionYonedaEquiv Q T m) =
        T.1.map k.op (completionYonedaEquiv Q T n) := by
      have h := congrArg (completionYonedaEquiv B T) hm
      simpa only [completionYonedaEquiv_precomp] using h
    have hn' : T.1.map j.op (completionYonedaEquiv Q T m) =
        T.1.map j.op (completionYonedaEquiv Q T n) := by
      have h := congrArg (completionYonedaEquiv X T) hn
      simpa only [completionYonedaEquiv_precomp] using h
    let hPull := T.property.2 i f k j h hi
    let One := ULift.{u} PUnit
    let mFun : One ⟶ T.1.obj (op Q) := ↾fun _ => completionYonedaEquiv Q T m
    let nFun : One ⟶ T.1.obj (op Q) := ↾fun _ => completionYonedaEquiv Q T n
    have hmFun : mFun ≫ T.1.map k.op = nFun ≫ T.1.map k.op := by
      ext x
      simpa [mFun, nFun] using hm'
    have hnFun : mFun ≫ T.1.map j.op = nFun ≫ T.1.map j.op := by
      ext x
      simpa [mFun, nFun] using hn'
    have hFun := hPull.hom_ext hmFun hnFun
    exact congrArg (fun g : One ⟶ T.1.obj (op Q) =>
      (g : One → T.1.obj (op Q)) (ULift.up PUnit.unit)) hFun
  · intro T a b hab
    let hPull := T.property.2 i f k j h hi
    have hab' : T.1.map i.op (completionYonedaEquiv B T a) =
        T.1.map f.op (completionYonedaEquiv X T b) := by
      have h := congrArg (completionYonedaEquiv A T) hab
      simpa only [completionYonedaEquiv_precomp] using h
    let One := ULift.{u} PUnit
    let top : One ⟶ T.1.obj (op B) := ↾fun _ => completionYonedaEquiv B T a
    let bottom : One ⟶ T.1.obj (op X) := ↾fun _ => completionYonedaEquiv X T b
    have habFun : top ≫ T.1.map i.op = bottom ≫ T.1.map f.op := by
      ext x
      simpa [top, bottom] using hab'
    let zFun := hPull.lift top bottom habFun
    let z := ConcreteCategory.hom zFun (ULift.up PUnit.unit)
    have hzK : T.1.map k.op z = completionYonedaEquiv B T a := by
      have hz := hPull.lift_fst top bottom habFun
      exact congrArg (fun g : One ⟶ T.1.obj (op B) =>
        (g : One → T.1.obj (op B)) (ULift.up PUnit.unit)) hz
    have hzJ : T.1.map j.op z = completionYonedaEquiv X T b := by
      have hz := hPull.lift_snd top bottom habFun
      exact congrArg (fun g : One ⟶ T.1.obj (op X) =>
        (g : One → T.1.obj (op X)) (ULift.up PUnit.unit)) hz
    refine ⟨(completionYonedaEquiv Q T).symm z, ?_, ?_⟩
    · apply (completionYonedaEquiv B T).injective
      calc
        _ = T.1.map k.op z := by rw [completionYonedaEquiv_precomp]; simp
        _ = completionYonedaEquiv B T a := hzK
    · apply (completionYonedaEquiv X T).injective
      calc
        _ = T.1.map j.op z := by rw [completionYonedaEquiv_precomp]; simp
        _ = completionYonedaEquiv X T b := hzJ

noncomputable def finCellBoundaryObj (n : ℕ) : FinCell.{u} :=
  ⟨TopCat.diskBoundary n, Packages.diskBoundary_isFiniteCellComplex n⟩

noncomputable def finCellDiskObj (n : ℕ) : FinCell.{u} := by
  refine ⟨TopCat.disk n, ?_⟩
  change Top.relativeFiniteCellComplexes (initial.to (TopCat.disk n))
  have hBoundary : Top.relativeFiniteCellComplexes (TopCat.diskBoundaryInclusion n) := by
    apply MorphismProperty.le_multiplicativeClosure
    apply Or.inl
    apply MorphismProperty.le_pushouts
    exact ⟨n⟩
  letI : Top.relativeFiniteCellComplexes.IsMultiplicative := by
    unfold Top.relativeFiniteCellComplexes
    infer_instance
  simpa using Top.relativeFiniteCellComplexes.comp_mem _ _
    (Packages.diskBoundary_isFiniteCellComplex n) hBoundary

noncomputable def finCellBoundaryMap (n : ℕ) :
    finCellBoundaryObj n ⟶ finCellDiskObj n :=
  ⟨TopCat.diskBoundaryInclusion n⟩

noncomputable def finCellBoundaryGenMap (n : ℕ) :
    (Completion.yoneda FinCell.{u}).obj (finCellBoundaryObj n) ⟶
      (Completion.yoneda FinCell.{u}).obj (finCellDiskObj n) :=
  (Completion.yoneda FinCell.{u}).map (finCellBoundaryMap n)

noncomputable def finCellBoundaryGenerators :
    MorphismProperty (Completion.{u} FinCell.{u}) :=
  MorphismProperty.ofHoms finCellBoundaryGenMap

theorem completionYoneda_isCardinalPresentable (A : FinCell.{u}) :
    IsCardinalPresentable.{u} ((Completion.yoneda FinCell.{u}).obj A) Cardinal.aleph0.{u} := by
  refine IsCardinalPresentable.mk (κ := Cardinal.aleph0.{u}) ?_
  intro J _ hJ F c hc
  letI : IsFiltered J := isFiltered_of_isCardinalFiltered J Cardinal.aleph0
  let P : ObjectProperty (FinCell.{u}ᵒᵖ ⥤ Type u) := IsCompletionPresheaf FinCell.{u}
  letI : HasColimitsOfShape J (Type u) := inferInstance
  letI : HasColimitsOfShape J (FinCell.{u}ᵒᵖ ⥤ Type u) := inferInstance
  have hClosed : P.IsClosedUnderColimitsOfShape J := by
    rw [ObjectProperty.isClosedUnderColimitsOfShape_iff]
    intro Z hZ
    rcases hZ with ⟨hZ⟩
    letI : HasColimit hZ.diag := hZ.hasColimit
    have hp : P (colimit hZ.diag) :=
      completionPresheaf_colimit_filtered hZ.diag hZ.prop_diag_obj
    let e : colimit hZ.diag ≅ Z :=
      (colimit.isColimit hZ.diag).coconePointUniqueUpToIso hZ.isColimit
    exact P.prop_of_iso e hp
  letI : P.IsClosedUnderColimitsOfShape J := hClosed
  letI : HasColimitsOfShape J P.FullSubcategory :=
    Limits.hasColimitsOfShape_of_closedUnderColimits J P
  letI : PreservesColimitsOfShape J P.ι := by infer_instance
  let rawF : J ⥤ (FinCell.{u}ᵒᵖ ⥤ Type u) := F ⋙ P.ι
  let rawC := P.ι.mapCocone c
  have hRawC : IsColimit rawC := isColimitOfPreserves P.ι hc
  let ev := (evaluation FinCell.{u}ᵒᵖ (Type u)).obj (op A)
  let evalC := ev.mapCocone rawC
  have hEvalC : IsColimit evalC := isColimitOfPreserves ev hRawC
  constructor
  · intro g
    let x := completionYonedaEquiv A c.pt g
    obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hEvalC x
    refine ⟨j, (completionYonedaEquiv A (F.obj j)).symm y, ?_⟩
    apply (completionYonedaEquiv A c.pt).injective
    rw [completionYonedaEquiv_comp]
    simp only [Equiv.apply_symm_apply]
    change ConcreteCategory.hom (ev.map (c.ι.app j).hom) y = x
    exact hy
  · intro j f₁ f₂ hfg
    let x₁ := completionYonedaEquiv A (F.obj j) f₁
    let x₂ := completionYonedaEquiv A (F.obj j) f₂
    have hx : ((c.ι.app j).hom.app (op A)) x₁ =
        ((c.ι.app j).hom.app (op A)) x₂ := by
      have hh := congrArg (completionYonedaEquiv A c.pt) hfg
      rw [completionYonedaEquiv_comp, completionYonedaEquiv_comp] at hh
      simpa [x₁, x₂, evalC, rawC, rawF] using hh
    have hx' : evalC.ι.app j x₁ = evalC.ι.app j x₂ := by
      change ((c.ι.app j).hom.app (op A)) x₁ =
        ((c.ι.app j).hom.app (op A)) x₂
      exact hx
    obtain ⟨j', a, ha⟩ :=
      Types.FilteredColimit.isColimit_eq_iff' hEvalC (i := j) x₁ x₂ |>.1 hx'
    refine ⟨j', a, ?_⟩
    apply (completionYonedaEquiv A (F.obj j')).injective
    rw [completionYonedaEquiv_comp, completionYonedaEquiv_comp]
    simpa [x₁, x₂, ha, evalC, rawC, rawF]

private theorem finCellBoundaryGenerators_smallObjectArgument :
    MorphismProperty.IsCardinalForSmallObjectArgument.{u}
      (finCellBoundaryGenerators.{u}) Cardinal.aleph0 := by
  letI : EssentiallySmall.{u} FinCell.{u} := Packages.finCell_essentiallySmall
  letI : HasColimitsOfSize.{u, u} (Completion.{u} FinCell.{u}) :=
    finCellCompletion_hasColimits
  letI : LocallySmall.{u} (Completion.{u} FinCell.{u}) :=
    finCellCompletion_locallySmall
  letI : Small.{u} ℕ := inferInstance
  refine
    { isSmall := MorphismProperty.isSmall_ofHoms (finCellBoundaryGenMap.{u})
      preservesColimit := ?_ }
  intro A B X Y i hi f hf
  have hA : IsCardinalPresentable.{u} A Cardinal.aleph0 := by
    obtain ⟨n, hn⟩ :=
      (MorphismProperty.ofHoms_iff (finCellBoundaryGenMap.{u}) i).1 hi
    obtain ⟨hA, hB, hEq⟩ :=
      (Arrow.mk_eq_mk_iff i (finCellBoundaryGenMap.{u} n)).1 hn
    subst A
    simpa using (completionYoneda_isCardinalPresentable.{u} (finCellBoundaryObj.{u} n))
  letI : IsCardinalPresentable.{u} A Cardinal.aleph0 := hA
  have hPres : PreservesColimitsOfShape (Cardinal.aleph0.ord.ToType)
      (coyoneda.obj (Opposite.op A)) :=
    preservesColimitsOfShape_of_isCardinalPresentable A Cardinal.aleph0 _
  letI : PreservesColimitsOfShape (Cardinal.aleph0.ord.ToType)
      (coyoneda.obj (Opposite.op A)) := hPres
  infer_instance

private theorem finCellRawYoneda_isCardinalPresentable (A : FinCell.{u}) :
    IsCardinalPresentable.{u} (finCellRawYoneda.{u}.obj A) Cardinal.aleph0.{u} := by
  let e : (Completion.yoneda FinCell.{u}).obj A ≅ finCellRawYoneda.obj A :=
    ObjectProperty.isoMk (IsCompletionPresheaf FinCell.{u}) (completionYonedaRawIso A)
  letI : IsCardinalPresentable.{u} ((Completion.yoneda FinCell.{u}).obj A)
      Cardinal.aleph0.{u} := completionYoneda_isCardinalPresentable A
  exact isCardinalPresentable_of_iso e Cardinal.aleph0.{u}

private noncomputable def finCellCofibrationGen [EssentiallySmall.{u} FinCell.{u}] :=
  Σ (A : SmallModel FinCell.{u}), Σ (B : SmallModel FinCell.{u}),
    {i : A ⟶ B // cofibrations FinCell.{u} ((equivSmallModel FinCell.{u}).inverse.map i)}

private noncomputable def finCellGenMap [EssentiallySmall.{u} FinCell.{u}]
    (g : finCellCofibrationGen.{u}) :
    (finCellRawYoneda.{u}).obj ((equivSmallModel FinCell.{u}).inverse.obj g.1) ⟶
      (finCellRawYoneda.{u}).obj ((equivSmallModel FinCell.{u}).inverse.obj g.2.1) :=
  (finCellRawYoneda.{u}).map ((equivSmallModel FinCell.{u}).inverse.map g.2.2.1)

private noncomputable def finCellRepresentableCofibrations
    [EssentiallySmall.{u} FinCell.{u}] :
    MorphismProperty (Completion.{u} FinCell.{u}) :=
  MorphismProperty.ofHoms finCellGenMap

private theorem finCellRepresentableCofibrations_smallObjectArgument
    [EssentiallySmall.{u} FinCell.{u}] :
    MorphismProperty.IsCardinalForSmallObjectArgument.{u}
      (finCellRepresentableCofibrations.{u}) Cardinal.aleph0 := by
  letI : HasColimitsOfSize.{u, u} (Completion.{u} FinCell.{u}) :=
    finCellCompletion_hasColimits
  letI : LocallySmall.{u} (Completion.{u} FinCell.{u}) :=
    finCellCompletion_locallySmall
  letI : Small.{u} (finCellCofibrationGen.{u}) := inferInstance
  refine
    { isSmall := MorphismProperty.isSmall_ofHoms (finCellGenMap.{u})
      preservesColimit := ?_ }
  intro A B X Y i hi f hf
  have hA : IsCardinalPresentable.{u} A Cardinal.aleph0 := by
    obtain ⟨g, hg⟩ :=
      (MorphismProperty.ofHoms_iff finCellGenMap i).1 hi
    obtain ⟨hA, hB, hEq⟩ := (Arrow.mk_eq_mk_iff i (finCellGenMap g)).1 hg
    subst A
    exact finCellRawYoneda_isCardinalPresentable
      ((equivSmallModel FinCell.{u}).inverse.obj g.1)
  letI : IsCardinalPresentable.{u} A Cardinal.aleph0 := hA
  have hPres : PreservesColimitsOfShape (Cardinal.aleph0.ord.ToType)
      (coyoneda.obj (Opposite.op A)) :=
    preservesColimitsOfShape_of_isCardinalPresentable A Cardinal.aleph0 _
  letI : PreservesColimitsOfShape (Cardinal.aleph0.ord.ToType)
      (coyoneda.obj (Opposite.op A)) := hPres
  infer_instance

private theorem finCellBoundaryMap_mem_llp (n : ℕ) :
    (finCellBoundaryGenerators.{u}).rlp.llp
      ((Completion.yoneda FinCell.{u}).map (finCellBoundaryMap n)) := by
  apply MorphismProperty.le_llp_rlp
  exact MorphismProperty.ofHoms.mk n

private noncomputable def topRestriction_yonedaIso
    (hι : IsCellularRealization (ObjectProperty.ι Top.IsFiniteCellComplex.{u}))
    (A : FinCell.{u}) :
    (topRestriction hι).obj A.obj ≅ (Completion.yoneda FinCell.{u}).obj A := by
  let e : ((topRestriction hι).obj A.obj).1 ≅
      ((Completion.yoneda FinCell.{u}).obj A).1 :=
    NatIso.ofComponents (fun Z => Equiv.toIso
      ((ObjectProperty.fullyFaithfulι Top.IsFiniteCellComplex).homEquiv
        (X := unop Z) (Y := A)).symm) (by
      intro Z Z' f
      ext x
      apply (ObjectProperty.fullyFaithfulι Top.IsFiniteCellComplex).map_injective
      simp [topRestriction, restrictionAlong, Completion.yoneda]
      apply TopCat.hom_ext
      rfl)
  exact ObjectProperty.isoMk (IsCompletionPresheaf FinCell.{u}) e

private theorem topRestriction_yonedaIso_naturality
    (hι : IsCellularRealization (ObjectProperty.ι Top.IsFiniteCellComplex.{u}))
    {A B : FinCell.{u}} (i : A ⟶ B) :
    (topRestriction_yonedaIso hι A).hom ≫
        (Completion.yoneda FinCell.{u}).map i =
      (topRestriction hι).map ((ObjectProperty.ι _).map i) ≫
        (topRestriction_yonedaIso hι B).hom := by
  apply ObjectProperty.hom_ext
  ext Z x
  apply (ObjectProperty.fullyFaithfulι Top.IsFiniteCellComplex).map_injective
  simp [topRestriction_yonedaIso, topRestriction, restrictionAlong,
    Completion.yoneda]
  apply TopCat.hom_ext
  rfl

theorem finCellBoundaryMap_cof (n : ℕ) :
    cofibrations FinCell.{u} (finCellBoundaryMap n) := by
  change Top.relativeFiniteCellComplexes (TopCat.diskBoundaryInclusion n)
  have hBoundary : Top.relativeFiniteCellComplexes (TopCat.diskBoundaryInclusion n) := by
    apply MorphismProperty.le_multiplicativeClosure
    apply Or.inl
    apply MorphismProperty.le_pushouts
    exact ⟨n⟩
  exact hBoundary

private theorem topRestriction_pushoutBoundary_mem_llp
    (hι : IsCellularRealization (ObjectProperty.ι Top.IsFiniteCellComplex.{u}))
    {A B : TopCat.{u}} (i : A ⟶ B) (hA : Top.IsFiniteCellComplex A)
    (hi : Top.cellBoundaries.pushouts i) :
    (finCellBoundaryGenerators.{u}).rlp.llp ((topRestriction hι).map i) := by
  let R := topRestriction hι
  let J := (finCellBoundaryGenerators.{u}).rlp.llp
  have hiCells : Top.cellBoundaries.pushouts i := hi
  rcases hi with ⟨A₀, B₀, p, att, cell, hp, hPush⟩
  have hIRel : Top.relativeFiniteCellComplexes i := by
    change (Top.cellBoundaries.pushouts ⊔
      MorphismProperty.isomorphisms TopCat.{u}).multiplicativeClosure i
    exact MorphismProperty.le_multiplicativeClosure _ _ (Or.inl hiCells)
  have hB : Top.IsFiniteCellComplex B := by
    change Top.relativeFiniteCellComplexes (initial.to B)
    letI : Top.relativeFiniteCellComplexes.IsMultiplicative := by
      unfold Top.relativeFiniteCellComplexes
      infer_instance
    simpa using Top.relativeFiniteCellComplexes.comp_mem _ _ hA hIRel
  obtain ⟨n, hn⟩ := (MorphismProperty.ofHoms_iff
    (fun n : ℕ => TopCat.diskBoundaryInclusion n) p).1 hp
  let e : Arrow.mk p ≅ Arrow.mk (TopCat.diskBoundaryInclusion n) := eqToIso hn
  let eA : A₀ ≅ TopCat.diskBoundary n := Arrow.leftFunc.mapIso e
  let eB : B₀ ≅ TopCat.disk n := Arrow.rightFunc.mapIso e
  let att' : TopCat.diskBoundary n ⟶ A := eA.inv ≫ att
  let cell' : TopCat.disk n ⟶ B := eB.inv ≫ cell
  have hPush' : IsPushout att' (TopCat.diskBoundaryInclusion n) i cell' := by
    apply hPush.of_iso eA (Iso.refl A) eB (Iso.refl B)
    · simp [att']
    · exact e.hom.w.symm
    · simp
    · simp [cell']
  let A' : FinCell.{u} := ⟨A, hA⟩
  let B' : FinCell.{u} := ⟨B, hB⟩
  let att'' : finCellBoundaryObj n ⟶ A' := ⟨att'⟩
  let cell'' : finCellDiskObj n ⟶ B' := ⟨cell'⟩
  let i' : A' ⟶ B' := ⟨i⟩
  let sq : Square FinCell.{u} :=
    { f₁₂ := finCellBoundaryMap n
      f₁₃ := att''
      f₂₄ := cell''
      f₃₄ := i'
      fac := by
        apply (ObjectProperty.ι Top.IsFiniteCellComplex).map_injective
        exact hPush'.flip.w }
  have hTop : (sq.map (ObjectProperty.ι Top.IsFiniteCellComplex)).IsPushout := by
    change IsPushout (TopCat.diskBoundaryInclusion n) att' cell' i
    exact hPush'.flip
  have hSquare : IsPushout (finCellBoundaryMap n) att'' cell'' i' :=
    Square.IsPushout.of_map (ObjectProperty.ι Top.IsFiniteCellComplex) hTop
  have hYonedaSquare := completionYoneda_map_cofPushout
    (finCellBoundaryMap n) att'' cell'' i' hSquare (finCellBoundaryMap_cof n)
  have hJ' : J ((Completion.yoneda FinCell.{u}).map i') :=
    MorphismProperty.of_isPushout hYonedaSquare.flip (finCellBoundaryMap_mem_llp n)
  let eA' := topRestriction_yonedaIso hι A'
  let eB' := topRestriction_yonedaIso hι B'
  have hNat := topRestriction_yonedaIso_naturality hι i'
  have hArrow : Arrow.mk (R.map i) ≅
      Arrow.mk ((Completion.yoneda FinCell.{u}).map i') :=
    Arrow.isoMk eA' eB' (by simpa [eA', eB', R] using hNat)
  exact (J.arrow_mk_iso_iff hArrow).2 hJ'

private theorem topRestriction_relativeFiniteCell_map_mem_llp
    (hι : IsCellularRealization (ObjectProperty.ι Top.IsFiniteCellComplex.{u}))
    {A B : TopCat.{u}} (i : A ⟶ B) (hA : Top.IsFiniteCellComplex A)
    (hi : Top.relativeFiniteCellComplexes i) :
    (finCellBoundaryGenerators.{u}).rlp.llp ((topRestriction hι).map i) := by
  let R := topRestriction hι
  let J := (finCellBoundaryGenerators.{u}).rlp.llp
  let W : MorphismProperty TopCat.{u} :=
    (Top.cellBoundaries.pushouts ⊔ MorphismProperty.isomorphisms TopCat.{u})
  let P : MorphismProperty TopCat.{u} := fun X Y f =>
    Top.relativeFiniteCellComplexes f ∧
      (Top.IsFiniteCellComplex X → J (R.map f))
  letI : Top.relativeFiniteCellComplexes.IsMultiplicative := by
    unfold Top.relativeFiniteCellComplexes
    infer_instance
  have hPMul : P.IsMultiplicative := by
    refine { id_mem := ?_, comp_mem := ?_ }
    · intro X
      refine ⟨Top.relativeFiniteCellComplexes.id_mem X, ?_⟩
      intro hX
      simpa [R, J] using J.id_mem (R.obj X)
    · intro X Y Z f g hf hg
      refine ⟨Top.relativeFiniteCellComplexes.comp_mem f g hf.1 hg.1, ?_⟩
      intro hX
      have hY : Top.IsFiniteCellComplex Y := by
        change Top.relativeFiniteCellComplexes (initial.to Y)
        simpa using Top.relativeFiniteCellComplexes.comp_mem _ _ hX hf.1
      simpa [R] using J.comp_mem (R.map f) (R.map g) (hf.2 hX) (hg.2 hY)
  letI : P.IsMultiplicative := hPMul
  have hW : W ≤ P := by
    intro X Y f hf
    rcases hf with hCells | hIso
    · refine ⟨MorphismProperty.le_multiplicativeClosure _ _ (Or.inl hCells), ?_⟩
      intro hX
      exact topRestriction_pushoutBoundary_mem_llp hι f hX hCells
    · refine ⟨MorphismProperty.le_multiplicativeClosure _ _ (Or.inr hIso), ?_⟩
      intro hX
      rw [MorphismProperty.isomorphisms.iff] at hIso
      letI : IsIso f := hIso
      letI : IsIso (R.map f) := Functor.map_isIso R f
      exact MorphismProperty.llp_of_isIso
        (finCellBoundaryGenerators.{u}).rlp _
  have hClosure : W.multiplicativeClosure ≤ P :=
    (MorphismProperty.multiplicativeClosure_le_iff W P).2 hW
  exact (hClosure _ hi).2 hA

private theorem finCellBoundaryGenerators_rlp_le_trivialFibrations
    (hι : IsCellularRealization (ObjectProperty.ι Top.IsFiniteCellComplex.{u})) :
    (finCellBoundaryGenerators.{u}).rlp ≤
      Completion.trivialFibrations FinCell.{u} := by
  intro X Y f hf
  change presheafTrivialFibrations f.hom
  intro A B i hi a b hab
  change Top.relativeFiniteCellComplexes ((ObjectProperty.ι _).map i) at hi
  have hR : (finCellBoundaryGenerators.{u}).rlp.llp
      ((topRestriction hι).map ((ObjectProperty.ι _).map i)) :=
    topRestriction_relativeFiniteCell_map_mem_llp hι ((ObjectProperty.ι _).map i)
      A.property hi
  let eA := topRestriction_yonedaIso hι A
  let eB := topRestriction_yonedaIso hι B
  have hNat := topRestriction_yonedaIso_naturality hι i
  have hArrow : Arrow.mk ((topRestriction hι).map ((ObjectProperty.ι _).map i)) ≅
      Arrow.mk ((Completion.yoneda FinCell.{u}).map i) :=
    Arrow.isoMk eA eB hNat
  have hY : (finCellBoundaryGenerators.{u}).rlp.llp
      ((Completion.yoneda FinCell.{u}).map i) :=
    ((finCellBoundaryGenerators.{u}).rlp.llp.arrow_mk_iso_iff hArrow).1 hR
  have hLift : HasLiftingProperty ((Completion.yoneda FinCell.{u}).map i) f := hY f hf
  let aArrow := (completionYonedaEquiv A X).symm a
  let bArrow := (completionYonedaEquiv B Y).symm b
  have hSquare : aArrow ≫ f = (Completion.yoneda FinCell.{u}).map i ≫ bArrow := by
    apply (completionYonedaEquiv A Y).injective
    rw [completionYonedaEquiv_comp, completionYonedaEquiv_precomp]
    simpa [aArrow, bArrow] using hab
  let sq : CommSq aArrow ((Completion.yoneda FinCell.{u}).map i) f bArrow := ⟨hSquare⟩
  letI : HasLiftingProperty ((Completion.yoneda FinCell.{u}).map i) f := hLift
  let l := sq.lift
  have hl : (Completion.yoneda FinCell.{u}).map i ≫ l = aArrow := sq.fac_left
  have hr : l ≫ f = bArrow := sq.fac_right
  refine ⟨completionYonedaEquiv B X l, ?_, ?_⟩
  · have h := congrArg (completionYonedaEquiv A X) hl
    rw [completionYonedaEquiv_precomp] at h
    simpa [aArrow] using h
  · have h := congrArg (completionYonedaEquiv B Y) hr
    rw [completionYonedaEquiv_comp] at h
    simpa [bArrow] using h

theorem exists_retract_of_boundaryCellular
    (hι : IsCellularRealization (ObjectProperty.ι Top.IsFiniteCellComplex.{u}))
    {I X : Completion.{u} FinCell.{u}} (hI : IsInitial I)
    (hX : IsCofibrantFor (Completion.cofibrations FinCell.{u}) X) :
    ∃ (C : Completion.{u} FinCell.{u}) (s : X ⟶ C) (p : C ⟶ X),
      s ≫ p = 𝟙 X ∧
      Nonempty (HomotopicalAlgebra.RelativeCellComplex.{u}
        (fun (_ : Cardinal.aleph0.{u}.ord.ToType) =>
          (finCellBoundaryGenerators.{u}).homFamily) (hI.to C)) := by
  letI : IsCylinderCategory FinCell.{u} := Packages.finCell_isCylinderCategory
  letI : EssentiallySmall.{u} FinCell.{u} := Packages.finCell_essentiallySmall
  letI : HasColimitsOfSize.{u, u} (Completion.{u} FinCell.{u}) :=
    finCellCompletion_hasColimits
  letI : LocallySmall.{u} (Completion.{u} FinCell.{u}) :=
    finCellCompletion_locallySmall
  letI : MorphismProperty.IsCardinalForSmallObjectArgument.{u}
      (finCellBoundaryGenerators.{u}) Cardinal.aleph0 :=
    finCellBoundaryGenerators_smallObjectArgument
  let i : I ⟶ X := hI.to X
  have hiCof : (Completion.trivialFibrations FinCell.{u}).llp i := by
    change Completion.cofibrations FinCell.{u} i
    exact hX hI
  have hiGen : (finCellBoundaryGenerators.{u}).rlp.llp i :=
    MorphismProperty.antitone_llp (finCellBoundaryGenerators_rlp_le_trivialFibrations hι)
      i hiCof
  let C := CategoryTheory.SmallObject.obj
    (finCellBoundaryGenerators.{u}) Cardinal.aleph0 i
  let j := CategoryTheory.SmallObject.ιObj
    (finCellBoundaryGenerators.{u}) Cardinal.aleph0 i
  let p := CategoryTheory.SmallObject.πObj
    (finCellBoundaryGenerators.{u}) Cardinal.aleph0 i
  have hjp : j ≫ p = i :=
    CategoryTheory.SmallObject.ιObj_πObj
      (finCellBoundaryGenerators.{u}) Cardinal.aleph0 i
  have hp : (finCellBoundaryGenerators.{u}).rlp p :=
    CategoryTheory.SmallObject.rlp_πObj
      (finCellBoundaryGenerators.{u}) Cardinal.aleph0 i
  have hCell : HomotopicalAlgebra.RelativeCellComplex.{u}
      (fun (_ : Cardinal.aleph0.{u}.ord.ToType) =>
        (finCellBoundaryGenerators.{u}).homFamily) j :=
    CategoryTheory.SmallObject.relativeCellComplexιObj
      (finCellBoundaryGenerators.{u}) Cardinal.aleph0 i
  have hLift : HasLiftingProperty i p := hiGen p hp
  let sq : CommSq j i p (𝟙 X) := ⟨by simp [hjp]⟩
  letI : HasLiftingProperty i p := hLift
  let s := sq.lift
  have hs : s ≫ p = 𝟙 X := sq.fac_right
  have hj : j = hI.to C := hI.hom_ext _ _
  have hCell' : HomotopicalAlgebra.RelativeCellComplex.{u}
      (fun (_ : Cardinal.aleph0.{u}.ord.ToType) =>
        (finCellBoundaryGenerators.{u}).homFamily) (hI.to C) := by
    rw [← hj]
    exact hCell
  exact ⟨C, s, p, hs, ⟨hCell'⟩⟩

private theorem finCellCofibrations_respectsIso :
    (cofibrations FinCell.{u}).RespectsIso := by
  let hC : IsCofibrationCategory FinCell.{u} :=
    Packages.finCell_isCylinderCategory.toIsCofibrationCategory
  apply MorphismProperty.RespectsIso.mk
  · intro X Y Z e f hf
    have he : cofibrations FinCell.{u} e.hom :=
      hC.isomorphisms_le e.hom (by infer_instance)
    exact hC.isMultiplicative.comp_mem e.hom f he hf
  · intro X Y Z e f hf
    have he : cofibrations FinCell.{u} e.hom :=
      hC.isomorphisms_le e.hom (by infer_instance)
    exact hC.isMultiplicative.comp_mem f e.hom hf he

private theorem finCellRepresentableCofibrations_rlp_le_trivialFibrations
    [EssentiallySmall.{u} FinCell.{u}] :
    (finCellRepresentableCofibrations.{u}).rlp ≤
      Completion.trivialFibrations FinCell.{u} := by
  letI : IsCylinderCategory FinCell.{u} := Packages.finCell_isCylinderCategory
  letI : (cofibrations FinCell.{u}).RespectsIso := finCellCofibrations_respectsIso
  let e : FinCell.{u} ≌ SmallModel FinCell.{u} := equivSmallModel FinCell.{u}
  intro X Y f hf
  change presheafTrivialFibrations f.hom
  intro A B i hi a b hab
  let A' := e.functor.obj A
  let B' := e.functor.obj B
  let i' := e.inverse.map (e.functor.map i)
  let A₀ := e.inverse.obj A'
  let B₀ := e.inverse.obj B'
  let uA := e.unitIso.app A
  let uB := e.unitIso.app B
  have hUnit : i ≫ uB.hom = uA.hom ≫ i' := by
    simpa only [uA, uB, i', Functor.id_obj, Functor.id_map,
      Functor.comp_obj, Functor.comp_map, Iso.app_hom] using
      e.unitIso.hom.naturality i
  have hiB : cofibrations FinCell.{u} (i ≫ uB.hom) :=
    MorphismProperty.RespectsIso.postcomp (cofibrations FinCell.{u}) uB.hom i hi
  have hiComp : cofibrations FinCell.{u} (uA.hom ≫ i') := by
    rw [← hUnit]
    exact hiB
  have hi' : cofibrations FinCell.{u} i' := by
    have h := MorphismProperty.RespectsIso.precomp (cofibrations FinCell.{u})
      uA.inv (uA.hom ≫ i') hiComp
    simpa [Category.assoc] using h
  let gen : finCellCofibrationGen.{u} := ⟨A', B', ⟨e.functor.map i, hi'⟩⟩
  let aArrow := (finCellRawYonedaEquiv A X).symm a
  let bArrow := (finCellRawYonedaEquiv B Y).symm b
  let a0 := (finCellRawYoneda.{u}).map uA.inv ≫ aArrow
  let b0 := (finCellRawYoneda.{u}).map uB.inv ≫ bArrow
  have haArrow : finCellRawYonedaEquiv A X aArrow = a := Equiv.apply_symm_apply _ _
  have hbArrow : finCellRawYonedaEquiv B Y bArrow = b := Equiv.apply_symm_apply _ _
  have hElemA : finCellRawYonedaEquiv A₀ X a0 = X.1.map uA.inv.op a := by
    calc
      _ = X.1.map uA.inv.op (finCellRawYonedaEquiv A X aArrow) :=
        finCellRawYonedaEquiv_precomp uA.inv aArrow
      _ = X.1.map uA.inv.op a := by rw [haArrow]
  have hElemB : finCellRawYonedaEquiv B₀ Y b0 = Y.1.map uB.inv.op b := by
    calc
      _ = Y.1.map uB.inv.op (finCellRawYonedaEquiv B Y bArrow) :=
        finCellRawYonedaEquiv_precomp uB.inv bArrow
      _ = Y.1.map uB.inv.op b := by rw [hbArrow]
  have hUnitInv : i' ≫ uB.inv = uA.inv ≫ i := by
    calc
      i' ≫ uB.inv = uA.inv ≫ (uA.hom ≫ i') ≫ uB.inv := by simp [Category.assoc]
      _ = uA.inv ≫ (i ≫ uB.hom) ≫ uB.inv := by rw [← hUnit]
      _ = uA.inv ≫ i := by simp [Category.assoc]
  have hOpp : uB.inv.op ≫ i'.op = i.op ≫ uA.inv.op := by
    simpa using congrArg Quiver.Hom.op hUnitInv
  have hSquareElements :
      f.hom.app (op A₀) (X.1.map uA.inv.op a) =
        Y.1.map i'.op (Y.1.map uB.inv.op b) := by
    calc
      _ = Y.1.map uA.inv.op (f.hom.app (op A) a) :=
        f.hom.naturality_apply uA.inv.op a
      _ = Y.1.map uA.inv.op (Y.1.map i.op b) := by rw [hab]
      _ = Y.1.map (i.op ≫ uA.inv.op) b := by rw [← Functor.map_comp_apply]
      _ = Y.1.map (uB.inv.op ≫ i'.op) b := by rw [← hOpp]
      _ = Y.1.map i'.op (Y.1.map uB.inv.op b) := by rw [Functor.map_comp_apply]
  have hBattach :
      b0.hom.app (op A₀) i' = Y.1.map i'.op (Y.1.map uB.inv.op b) := by
    calc
      _ = Y.1.map i'.op (finCellRawYonedaEquiv B₀ Y b0) := by
        exact (map_yonedaEquiv b0.hom i').symm
      _ = Y.1.map i'.op (Y.1.map uB.inv.op b) := by rw [hElemB]
  have hGenMap : finCellGenMap gen = (finCellRawYoneda.{u}).map i' := rfl
  have hSquare : a0 ≫ f = (finCellGenMap gen) ≫ b0 := by
    apply (finCellRawYonedaEquiv A₀ Y).injective
    change finCellRawYonedaEquiv A₀ Y (a0 ≫ f) =
      finCellRawYonedaEquiv A₀ Y ((finCellRawYoneda.{u}).map i' ≫ b0)
    calc
      _ = f.hom.app (op A₀) (finCellRawYonedaEquiv A₀ X a0) :=
        finCellRawYonedaEquiv_comp a0 f
      _ = Y.1.map i'.op (Y.1.map uB.inv.op b) := by
        rw [hElemA]
        exact hSquareElements
      _ = b0.hom.app (op A₀) i' := hBattach.symm
      _ = Y.1.map i'.op (finCellRawYonedaEquiv B₀ Y b0) := hBattach
      _ = finCellRawYonedaEquiv A₀ Y ((finCellRawYoneda.{u}).map i' ≫ b0) :=
        (finCellRawYonedaEquiv_precomp i' b0).symm
  let sq : CommSq a0 (finCellGenMap gen) f b0 := ⟨hSquare⟩
  have hRlp : HasLiftingProperty (finCellGenMap gen) f :=
    hf (finCellGenMap gen) (MorphismProperty.ofHoms.mk gen)
  letI : HasLiftingProperty (finCellGenMap gen) f := hRlp
  let l0 := sq.lift
  have hl0 : finCellGenMap gen ≫ l0 = a0 := sq.fac_left
  have hr0 : l0 ≫ f = b0 := sq.fac_right
  let l := (finCellRawYoneda.{u}).map uB.hom ≫ l0
  have hTopArrow : (finCellRawYoneda.{u}).map i ≫ l = aArrow := by
    dsimp [l]
    calc
      _ = ((finCellRawYoneda.{u}).map i ≫
          (finCellRawYoneda.{u}).map uB.hom) ≫ l0 := by rw [Category.assoc]
      _ = (finCellRawYoneda.{u}).map (i ≫ uB.hom) ≫ l0 := by rw [← Functor.map_comp]
      _ = (finCellRawYoneda.{u}).map (uA.hom ≫ i') ≫ l0 := by rw [hUnit]
      _ = ((finCellRawYoneda.{u}).map uA.hom ≫
          (finCellRawYoneda.{u}).map i') ≫ l0 := by rw [Functor.map_comp]
      _ = ((finCellRawYoneda.{u}).map uA.hom ≫ finCellGenMap gen) ≫ l0 := by rw [hGenMap]
      _ = (finCellRawYoneda.{u}).map uA.hom ≫ a0 := by rw [Category.assoc, hl0]
      _ = ((finCellRawYoneda.{u}).map uA.hom ≫
          (finCellRawYoneda.{u}).map uA.inv) ≫ aArrow := by rw [Category.assoc]
      _ = aArrow := by simp [Functor.map_comp]
  have hBottomArrow : l ≫ f = bArrow := by
    dsimp [l]
    calc
      _ = (finCellRawYoneda.{u}).map uB.hom ≫ (l0 ≫ f) := by rw [Category.assoc]
      _ = (finCellRawYoneda.{u}).map uB.hom ≫ b0 := by rw [hr0]
      _ = ((finCellRawYoneda.{u}).map uB.hom ≫
          (finCellRawYoneda.{u}).map uB.inv) ≫ bArrow := by rw [Category.assoc]
      _ = bArrow := by simp [Functor.map_comp]
  let lElem := finCellRawYonedaEquiv B X l
  have hTop : X.1.map i.op lElem = a := by
    have h := congrArg (finCellRawYonedaEquiv A X) hTopArrow
    rw [finCellRawYonedaEquiv_comp, finCellRawYonedaEquiv_map] at h
    calc
      X.1.map i.op lElem = l.hom.app (op A) i := map_yonedaEquiv l.hom i
      _ = a := by simpa [aArrow] using h
  have hBottom : f.hom.app (op B) lElem = b := by
    have h := congrArg (finCellRawYonedaEquiv B Y) hBottomArrow
    rw [finCellRawYonedaEquiv_comp] at h
    simpa [bArrow] using h
  exact ⟨lElem, hTop, hBottom⟩

private def topRestrictionEvalEquiv
    (hι : IsCellularRealization (ObjectProperty.ι Top.IsFiniteCellComplex.{u}))
    (A : FinCell.{u}) (Y : TopCat.{u}) :
    ((topRestriction hι).obj Y).1.obj (op A) ≃ (A.obj ⟶ Y) := by
  dsimp [topRestriction, restrictionAlong]
  rfl

@[simp] private theorem topRestrictionEvalEquiv_apply
    (hι : IsCellularRealization (ObjectProperty.ι Top.IsFiniteCellComplex.{u}))
    (A : FinCell.{u}) (Y : TopCat.{u}) (x : ((topRestriction hι).obj Y).1.obj (op A)) :
    topRestrictionEvalEquiv hι A Y x = x := by
  dsimp [topRestrictionEvalEquiv, topRestriction, restrictionAlong]
  rfl

@[simp] private theorem topRestrictionEvalEquiv_symm_apply
    (hι : IsCellularRealization (ObjectProperty.ι Top.IsFiniteCellComplex.{u}))
    (A : FinCell.{u}) (Y : TopCat.{u}) (x : A.obj ⟶ Y) :
    (topRestrictionEvalEquiv hι A Y).symm x = x := by
  dsimp [topRestrictionEvalEquiv, topRestriction, restrictionAlong]
  rfl

private theorem topRestrictionEvalEquiv_map
    (hι : IsCellularRealization (ObjectProperty.ι Top.IsFiniteCellComplex.{u}))
    {A B : FinCell.{u}} (i : A ⟶ B) (Y : TopCat.{u})
    (x : ((topRestriction hι).obj Y).1.obj (op B)) :
    topRestrictionEvalEquiv hι A Y (((topRestriction hι).obj Y).1.map i.op x) =
      (ObjectProperty.ι Top.IsFiniteCellComplex).map i ≫
        topRestrictionEvalEquiv hι B Y x := by
  dsimp [topRestrictionEvalEquiv, topRestriction, restrictionAlong]
  rfl

private noncomputable def finCellRestriction_representableIso
    (hι : IsCellularRealization (ObjectProperty.ι Top.IsFiniteCellComplex.{u}))
    {L : Completion.{u} FinCell.{u} ⥤ TopCat.{u}}
    (adj : L ⊣ topRestriction hι) (A : FinCell.{u}) :
    A.obj ≅ L.obj ((Completion.yoneda FinCell.{u}).obj A) := by
  let R := topRestriction hι
  let y := (Completion.yoneda FinCell.{u}).obj A
  let E (Y : TopCat.{u}) :
      (L.obj ((Completion.yoneda FinCell.{u}).obj A) ⟶ Y) ≃ (A.obj ⟶ Y) :=
    (adj.homEquiv ((Completion.yoneda FinCell.{u}).obj A) Y).trans
      ((completionYonedaEquiv A (R.obj Y)).trans (topRestrictionEvalEquiv hι A Y))
  have hE (Y Z : TopCat.{u}) (g : Y ⟶ Z) (f : L.obj y ⟶ Y) :
      E Z (f ≫ g) = E Y f ≫ g := by
    dsimp [E]
    rw [adj.homEquiv_naturality_right, completionYonedaEquiv_comp]
    rfl
  have hEInv (Y Z : TopCat.{u}) (g : A.obj ⟶ Y) (f : Y ⟶ Z) :
      (E Z).symm (g ≫ f) = (E Y).symm g ≫ f := by
    apply (E Z).injective
    rw [hE]
    simp
  let η : A.obj ⟶ L.obj y := E (L.obj y) (𝟙 _)
  let ε : L.obj y ⟶ A.obj := (E A.obj).symm (𝟙 _)
  refine ⟨η, ε, ?_, ?_⟩
  · apply (E A.obj).symm.injective
    rw [hEInv]
    simp [η, ε, y]
  · apply (E (L.obj y)).injective
    rw [hE]
    simp [η, ε, y]

private theorem finCellRestriction_unitEval
    (hι : IsCellularRealization (ObjectProperty.ι Top.IsFiniteCellComplex.{u}))
    {L : Completion.{u} FinCell.{u} ⥤ TopCat.{u}}
    (adj : L ⊣ topRestriction hι) (A : FinCell.{u}) :
    topRestrictionEvalEquiv hι A (L.obj ((Completion.yoneda FinCell.{u}).obj A))
      (completionYonedaEquiv A ((topRestriction hι).obj
        (L.obj ((Completion.yoneda FinCell.{u}).obj A)))
        (adj.unit.app ((Completion.yoneda FinCell.{u}).obj A))) =
      (finCellRestriction_representableIso hι adj A).hom := by
  let y := (Completion.yoneda FinCell.{u}).obj A
  change
    ((adj.homEquiv y (L.obj y)).trans
      ((completionYonedaEquiv A ((topRestriction hι).obj (L.obj y))).trans
        (topRestrictionEvalEquiv hι A (L.obj y)))) (𝟙 (L.obj y)) = _
  simp [finCellRestriction_representableIso, adj.homEquiv_unit]
  rw [completionYonedaEquiv_apply]

private theorem topRestrictionEvalEquiv_mapTarget
    (hι : IsCellularRealization (ObjectProperty.ι Top.IsFiniteCellComplex.{u}))
    (A : FinCell.{u}) {Y Z : TopCat.{u}} (f : Y ⟶ Z)
    (x : ((topRestriction hι).obj Y).1.obj (op A)) :
    topRestrictionEvalEquiv hι A Z (((topRestriction hι).map f).hom.app (op A) x) =
      topRestrictionEvalEquiv hι A Y x ≫ f := by
  rfl

private theorem finCellRestriction_representableIso_naturality
    (hι : IsCellularRealization (ObjectProperty.ι Top.IsFiniteCellComplex.{u}))
    {L : Completion.{u} FinCell.{u} ⥤ TopCat.{u}}
    (adj : L ⊣ topRestriction hι) {A B : FinCell.{u}} (i : A ⟶ B) :
    (ObjectProperty.ι Top.IsFiniteCellComplex).map i ≫
        (finCellRestriction_representableIso hι adj B).hom =
      (finCellRestriction_representableIso hι adj A).hom ≫
        L.map ((Completion.yoneda FinCell.{u}).map i) := by
  let yA := (Completion.yoneda FinCell.{u}).obj A
  let yB := (Completion.yoneda FinCell.{u}).obj B
  let R := topRestriction hι
  let eA := finCellRestriction_representableIso hι adj A
  let eB := finCellRestriction_representableIso hι adj B
  have hUnit := adj.unit.naturality ((Completion.yoneda FinCell.{u}).map i)
  have hEval := congrArg (completionYonedaEquiv A (R.obj (L.obj yB))) hUnit
  simp only [Functor.id_map] at hEval
  rw [completionYonedaEquiv_precomp] at hEval
  rw [completionYonedaEquiv_comp] at hEval
  simp only [Functor.comp_map] at hEval
  have hTop := congrArg (topRestrictionEvalEquiv hι A (L.obj yB)) hEval
  rw [topRestrictionEvalEquiv_map] at hTop
  rw [topRestrictionEvalEquiv_mapTarget] at hTop
  simp only [R, yA, yB, Functor.comp_obj] at hTop
  rw [finCellRestriction_unitEval hι adj B, finCellRestriction_unitEval hι adj A] at hTop
  simpa [R, yA, yB, eA, eB] using hTop

private theorem topRelativeFiniteCellComplexes_respectsIso :
    (Top.relativeFiniteCellComplexes : MorphismProperty TopCat.{u}).RespectsIso := by
  letI : (Top.relativeFiniteCellComplexes : MorphismProperty TopCat.{u}).IsMultiplicative := by
    unfold Top.relativeFiniteCellComplexes
    infer_instance
  apply MorphismProperty.RespectsIso.mk
  · intro X Y Z e f hf
    have he : (Top.relativeFiniteCellComplexes : MorphismProperty TopCat.{u}) e.hom := by
      change (Top.cellBoundaries.pushouts ⊔
        MorphismProperty.isomorphisms TopCat.{u}).multiplicativeClosure e.hom
      exact MorphismProperty.le_multiplicativeClosure _ _
        (Or.inr (MorphismProperty.isomorphisms.infer_property e.hom))
    exact (Top.relativeFiniteCellComplexes : MorphismProperty TopCat.{u}).comp_mem e.hom f he hf
  · intro X Y Z e f hf
    have he : (Top.relativeFiniteCellComplexes : MorphismProperty TopCat.{u}) e.hom := by
      change (Top.cellBoundaries.pushouts ⊔
        MorphismProperty.isomorphisms TopCat.{u}).multiplicativeClosure e.hom
      exact MorphismProperty.le_multiplicativeClosure _ _
        (Or.inr (MorphismProperty.isomorphisms.infer_property e.hom))
    exact (Top.relativeFiniteCellComplexes : MorphismProperty TopCat.{u}).comp_mem f e.hom hf he

private theorem finCellBoundaryGenMap_L_mem_relativeFiniteCell
    (hι : IsCellularRealization (ObjectProperty.ι Top.IsFiniteCellComplex.{u}))
    {L : Completion.{u} FinCell.{u} ⥤ TopCat.{u}}
    (adj : L ⊣ topRestriction hι) (n : ℕ) :
    Top.relativeFiniteCellComplexes (L.map (finCellBoundaryGenMap n)) := by
  let A := finCellBoundaryObj n
  let B := finCellDiskObj n
  let eA := finCellRestriction_representableIso hι adj A
  let eB := finCellRestriction_representableIso hι adj B
  have hNat := finCellRestriction_representableIso_naturality hι adj (finCellBoundaryMap n)
  letI : (Top.relativeFiniteCellComplexes : MorphismProperty TopCat.{u}).RespectsIso :=
    topRelativeFiniteCellComplexes_respectsIso
  have hArrow : Arrow.mk (TopCat.diskBoundaryInclusion n) ≅
      Arrow.mk (L.map (finCellBoundaryGenMap n)) := by
    exact Arrow.isoMk eA eB
      (by simpa [A, B, eA, eB, finCellBoundaryObj, finCellDiskObj,
        finCellBoundaryGenMap, finCellBoundaryMap] using hNat.symm)
  have hBoundary : Top.relativeFiniteCellComplexes (TopCat.diskBoundaryInclusion n) :=
    finCellBoundaryMap_cof n
  exact (Top.relativeFiniteCellComplexes.arrow_mk_iso_iff hArrow).1 hBoundary

theorem finCellBoundaryGenerators_map_mem_relativeFiniteCell
    (hι : IsCellularRealization (ObjectProperty.ι Top.IsFiniteCellComplex.{u}))
    {L : Completion.{u} FinCell.{u} ⥤ TopCat.{u}}
    (adj : L ⊣ topRestriction hι) {A B : Completion.{u} FinCell.{u}}
    (f : A ⟶ B) (hf : finCellBoundaryGenerators.{u} f) :
    Top.relativeFiniteCellComplexes (L.map f) := by
  obtain ⟨n, hn⟩ := (MorphismProperty.ofHoms_iff (finCellBoundaryGenMap.{u}) f).1 hf
  let e : Arrow.mk f ≅ Arrow.mk (finCellBoundaryGenMap n) := eqToIso hn
  let eL : Arrow.mk (L.map f) ≅ Arrow.mk (L.map (finCellBoundaryGenMap n)) :=
    (Functor.mapArrow L).mapIso e
  let e' : Arrow.mk (TopCat.diskBoundaryInclusion n) ≅
      Arrow.mk (L.map (finCellBoundaryGenMap n)) := by
    let A := finCellBoundaryObj n
    let B := finCellDiskObj n
    exact Arrow.isoMk (finCellRestriction_representableIso hι adj A)
      (finCellRestriction_representableIso hι adj B) (by
      simpa [A, B, finCellBoundaryObj, finCellDiskObj, finCellBoundaryGenMap,
        finCellBoundaryMap] using
          (finCellRestriction_representableIso_naturality hι adj
            (finCellBoundaryMap n)).symm)
  have e'' : Arrow.mk (TopCat.diskBoundaryInclusion n) ≅ Arrow.mk (L.map f) :=
    e' ≪≫ eL.symm
  letI : (Top.relativeFiniteCellComplexes : MorphismProperty TopCat.{u}).RespectsIso :=
    topRelativeFiniteCellComplexes_respectsIso
  have hBoundary : Top.relativeFiniteCellComplexes (TopCat.diskBoundaryInclusion n) :=
    finCellBoundaryMap_cof n
  exact (Top.relativeFiniteCellComplexes.arrow_mk_iso_iff e'').1 hBoundary

private noncomputable def mapCompletionAttachCells
    {α : Type (u + 1)} {A B : α → Completion.{u} FinCell.{u}}
    {X₁ X₂ : Completion.{u} FinCell.{u}} {g : ∀ a, A a ⟶ B a}
    {f : X₁ ⟶ X₂} (c : HomotopicalAlgebra.AttachCells g f)
    (L : Completion.{u} FinCell.{u} ⥤ TopCat.{u})
    [PreservesColimitsOfShape (Discrete c.ι) L]
    [PreservesColimit (span c.g₁ c.m) L] :
    HomotopicalAlgebra.AttachCells (fun a => L.map (g a)) (L.map f) where
  ι := c.ι
  π := c.π
  cofan₁ := Cofan.mk (L.obj c.cofan₁.pt) (fun a => L.map (c.cofan₁.inj a))
  cofan₂ := Cofan.mk (L.obj c.cofan₂.pt) (fun a => L.map (c.cofan₂.inj a))
  isColimit₁ := by
    let d₁ : (Discrete.functor (fun a => A (c.π a)) ⋙ L) ≅
        Discrete.functor (fun a => L.obj (A (c.π a))) :=
      Discrete.natIso (fun ⟨a⟩ => Iso.refl _)
    let c' : Cofan (fun a => L.obj (A (c.π a))) :=
      Cofan.mk (L.obj c.cofan₁.pt) (fun a => L.map (c.cofan₁.inj a))
    let cMap := L.mapCocone c.cofan₁
    let cPre := (Cocone.precompose d₁.hom).obj c'
    have e : cMap ≅ cPre := Cocone.ext (Iso.refl _) (by rintro ⟨a⟩; rfl)
    have hMap : IsColimit cMap := isColimitOfPreserves L c.isColimit₁
    exact (IsColimit.precomposeHomEquiv d₁ c').1 (IsColimit.ofIsoColimit hMap e)
  isColimit₂ := by
    let d₂ : (Discrete.functor (fun a => B (c.π a)) ⋙ L) ≅
        Discrete.functor (fun a => L.obj (B (c.π a))) :=
      Discrete.natIso (fun ⟨a⟩ => Iso.refl _)
    let c' : Cofan (fun a => L.obj (B (c.π a))) :=
      Cofan.mk (L.obj c.cofan₂.pt) (fun a => L.map (c.cofan₂.inj a))
    let cMap := L.mapCocone c.cofan₂
    let cPre := (Cocone.precompose d₂.hom).obj c'
    have e : cMap ≅ cPre := Cocone.ext (Iso.refl _) (by rintro ⟨a⟩; rfl)
    have hMap : IsColimit cMap := isColimitOfPreserves L c.isColimit₂
    exact (IsColimit.precomposeHomEquiv d₂ c').1 (IsColimit.ofIsoColimit hMap e)
  m := L.map c.m
  hm a := by
    change L.map (c.cofan₁.inj a) ≫ L.map c.m =
      L.map (g (c.π a)) ≫ L.map (c.cofan₂.inj a)
    simpa only [Functor.map_comp] using congrArg L.map (c.hm a)
  g₁ := L.map c.g₁
  g₂ := L.map c.g₂
  isPushout := c.isPushout.map L

private noncomputable def mapCompletionRelativeCellComplex
    (hι : IsCellularRealization (ObjectProperty.ι Top.IsFiniteCellComplex.{u}))
    {L : Completion.{u} FinCell.{u} ⥤ TopCat.{u}}
    (adj : L ⊣ topRestriction hι)
    {J : Type u} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
    {α : J → Type (u + 1)} {A B : (j : J) → α j → Completion.{u} FinCell.{u}}
    {g : ∀ j a, A j a ⟶ B j a} {X Y : Completion.{u} FinCell.{u}}
    {f : X ⟶ Y} (c : HomotopicalAlgebra.RelativeCellComplex g f) :
    HomotopicalAlgebra.RelativeCellComplex (fun j a => L.map (g j a)) (L.map f) := by
  letI : PreservesColimitsOfSize.{u, u} L := adj.leftAdjoint_preservesColimits
  letI : PreservesColimitsOfShape J L := inferInstance
  letI : PreservesWellOrderContinuousOfShape J L := by
    constructor
    intro j hj
    infer_instance
  exact
    { toTransfiniteCompositionOfShape := c.toTransfiniteCompositionOfShape.map L
      attachCells j hj := by
        letI : PreservesColimitsOfShape (Discrete (c.attachCells j hj).ι) L := inferInstance
        letI : PreservesColimit (span (c.attachCells j hj).g₁ (c.attachCells j hj).m) L :=
          inferInstance
        exact mapCompletionAttachCells (c.attachCells j hj) L }

private theorem boundaryCellular_L_cells_relativeFinite
    (hι : IsCellularRealization (ObjectProperty.ι Top.IsFiniteCellComplex.{u}))
    {L : Completion.{u} FinCell.{u} ⥤ TopCat.{u}}
    (adj : L ⊣ topRestriction hι) {I X : Completion.{u} FinCell.{u}}
    [PreservesColimitsOfSize.{u, u} L]
    (hI : IsInitial I)
    (hCell : HomotopicalAlgebra.RelativeCellComplex.{u}
      (fun (_ : Cardinal.aleph0.{u}.ord.ToType) =>
        (finCellBoundaryGenerators.{u}).homFamily) (hI.to X)) :
    ∀ c : (mapCompletionRelativeCellComplex hι adj hCell).Cells,
      Top.relativeFiniteCellComplexes
        (L.map ((finCellBoundaryGenerators.{u}).homFamily c.i)) := by
  letI : PreservesColimitsOfSize.{u, u} L := adj.leftAdjoint_preservesColimits
  intro c
  apply finCellBoundaryGenerators_map_mem_relativeFiniteCell hι adj
  exact (MorphismProperty.mem_toSet_iff (finCellBoundaryGenerators.{u}) c.i.1).1 c.i.2

private theorem boundaryCellular_L_isTransfiniteCoproductPushout
    (hι : IsCellularRealization (ObjectProperty.ι Top.IsFiniteCellComplex.{u}))
    {L : Completion.{u} FinCell.{u} ⥤ TopCat.{u}}
    (adj : L ⊣ topRestriction hι) {I X : Completion.{u} FinCell.{u}}
    [PreservesColimitsOfSize.{u, u} L]
    (hI : IsInitial I)
    (hCell : HomotopicalAlgebra.RelativeCellComplex.{u}
      (fun (_ : Cardinal.aleph0.{u}.ord.ToType) =>
        (finCellBoundaryGenerators.{u}).homFamily) (hI.to X)) :
    Nonempty (MorphismProperty.TransfiniteCompositionOfShape
      ((MorphismProperty.coproducts.{u} Top.relativeFiniteCellComplexes).pushouts)
      Cardinal.aleph0.{u}.ord.ToType (L.map (hI.to X))) := by
  let cTop := mapCompletionRelativeCellComplex hι adj hCell
  exact ⟨cTop.transfiniteCompositionOfShape'
    (boundaryCellular_L_cells_relativeFinite hι adj hI hCell)⟩

theorem finCellRestriction_unit_isIso_yoneda
    (hι : IsCellularRealization (ObjectProperty.ι Top.IsFiniteCellComplex.{u}))
    {L : Completion.{u} FinCell.{u} ⥤ TopCat.{u}}
    (adj : L ⊣ topRestriction hι) (A : FinCell.{u}) :
    IsIso (adj.unit.app ((Completion.yoneda FinCell.{u}).obj A)) := by
  let R := topRestriction hι
  let y := (Completion.yoneda FinCell.{u}).obj A
  let T := (R.obj (L.obj y)).1
  let H := completionYonedaRawIso A
  let eRep := finCellRestriction_representableIso hι adj A
  let η : A.obj ⟶ L.obj y := eRep.hom
  let inc := ObjectProperty.ι Top.IsFiniteCellComplex
  let incFF := ObjectProperty.fullyFaithfulι Top.IsFiniteCellComplex
  let φ (Z : FinCell.{u}ᵒᵖ) : y.1.obj Z ≃ T.obj Z :=
    (H.app Z).toEquiv.trans
      ((incFF.homEquiv).trans
        ((Iso.homCongr (Iso.refl (unop Z).obj) eRep).trans
          (topRestrictionEvalEquiv hι (unop Z) (L.obj y)).symm))
  let hPsh : y.1 ≅ T := NatIso.ofComponents (fun Z => Equiv.toIso (φ Z)) (by
    intro Z Z' g
    ext x
    change φ Z' ((y.1.map g) x) = T.map g (φ Z x)
    apply (topRestrictionEvalEquiv hι (unop Z') (L.obj y)).injective
    have hMap :
        (topRestrictionEvalEquiv hι (unop Z') (L.obj y)) (T.map g (φ Z x)) =
          inc.map (g.unop) ≫ (topRestrictionEvalEquiv hι (unop Z) (L.obj y)) (φ Z x) := by
      simpa [T, inc] using topRestrictionEvalEquiv_map hι (g.unop) (L.obj y) (φ Z x)
    rw [hMap]
    change inc.map (H.hom.app Z' ((y.1.map g) x)) ≫ η =
      inc.map (g.unop) ≫ (inc.map (H.hom.app Z x) ≫ η)
    have hNat : H.hom.app Z' ((y.1.map g) x) =
        g.unop ≫ H.hom.app Z x := by
      exact H.hom.naturality_apply g x
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun f => inc.map f ≫ η) hNat)
  let e : y ≅ R.obj (L.obj y) :=
    ObjectProperty.isoMk (IsCompletionPresheaf FinCell.{u}) hPsh
  have hIsoElem :
      completionYonedaEquiv A (R.obj (L.obj y)) e.hom =
        (topRestrictionEvalEquiv hι A (L.obj y)).symm η := by
    apply (topRestrictionEvalEquiv hι A (L.obj y)).injective
    rw [completionYonedaEquiv_apply]
    change
      (topRestrictionEvalEquiv hι A (L.obj y))
        (yonedaEquiv (H.inv ≫ hPsh.hom)) = η
    simp [yonedaEquiv, H, hPsh, φ, incFF, η, Category.assoc, eRep]
    change inc.map (𝟙 A) ≫ eRep.hom = eRep.hom
    simp
  have hUnitElem :
      (topRestrictionEvalEquiv hι A (L.obj y))
          (completionYonedaEquiv A (R.obj (L.obj y)) (adj.unit.app y)) = η := by
    change
      ((adj.homEquiv y (L.obj y)).trans
        ((completionYonedaEquiv A (R.obj (L.obj y))).trans
          (topRestrictionEvalEquiv hι A (L.obj y)))) (𝟙 (L.obj y)) = η
    simp [η, eRep, finCellRestriction_representableIso, adj.homEquiv_unit]
    exact Equiv.apply_symm_apply _ _
  have hEval :
      completionYonedaEquiv A (R.obj (L.obj y)) e.hom =
        completionYonedaEquiv A (R.obj (L.obj y)) (adj.unit.app y) := by
    apply (topRestrictionEvalEquiv hι A (L.obj y)).injective
    rw [hIsoElem, hUnitElem]
    exact Equiv.apply_symm_apply _ _
  have hEq : e.hom = adj.unit.app y :=
    (completionYonedaEquiv A (R.obj (L.obj y))).injective hEval
  rw [← hEq]
  infer_instance

example {J : Type u} [SmallCategory J] [IsFiltered J] :
    PreservesFiniteLimits (colim : (J ⥤ Type u) ⥤ Type u) := by
  infer_instance

end HomotopyHypothesis.FiniteCategory.Restriction
