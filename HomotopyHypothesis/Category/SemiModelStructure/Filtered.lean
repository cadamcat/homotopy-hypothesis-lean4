import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Category.SemiModelConstruction.Colimits
import HomotopyHypothesis.Category.SemiModelConstruction.Limits
import HomotopyHypothesis.Category.SemiModelConstruction.YonedaLifting
/-!
# Filtered colimits in the completion

Filtered colimits of the completion are computed objectwise, so representable objects are finitely
presentable, and a filtered colimit of weak equivalences is a weak equivalence.
-/

universe w v u

open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace HomotopyHypothesis.Category.SemiModelStructure

open Henry Category.SemiModelConstruction

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]

private theorem filteredColimit_preservesLimit
    {J : Type w} [SmallCategory J] [IsFiltered J]
    {K : Type} [SmallCategory K] [FinCategory K]
    (G : K ⥤ Cᵒᵖ) (c : Cone G) (hc : IsLimit c)
    (F : J ⥤ (Cᵒᵖ ⥤ Type w))
    (hF : ∀ j, PreservesLimit G (F.obj j)) :
    PreservesLimit G (colimit F) := by
  letI : HasLimit G := ⟨c, hc⟩
  let E := (Functor.whiskeringLeft K Cᵒᵖ (Type w)).obj G
  let H : J ⥤ K ⥤ Type w := F ⋙ E
  let D : K ⥤ J ⥤ Type w := H.flip
  let e₁ : F ⋙ (evaluation Cᵒᵖ (Type w)).obj (limit G) ≅ H ⋙ lim :=
    NatIso.ofComponents
      (fun j => by
        letI := hF j
        exact preservesLimitIso (F.obj j) G)
      (by
        intro j j' f
        apply limit.hom_ext
        intro k
        dsimp [E, H]
        simp only [preservesLimitIso_hom_π, limMap_π, Category.assoc]
        rw [preservesLimitIso_hom_π_assoc]
        exact ((F.map f).naturality (limit.π G k)).symm)
  let e := e₁ ≪≫ (limitIsoFlipCompLim D).symm
  let e₀ := colimitObjIsoColimitCompEvaluation F (limit G)
  let e₂ := HasColimit.isoOfNatIso e
  let e₃ := colimitLimitIso D
  let e₄ := HasLimit.isoOfNatIso (colimitCompWhiskeringLeftIsoCompColimit F G)
  let α : (colimit F).obj (limit G) ≅ limit (G ⋙ colimit F) := e₀ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄
  have hpost : limit.post G (colimit F) = α.hom := by
    apply limit.hom_ext
    intro k
    apply colimit_obj_ext
    intro j
    have hcomp :
        (colimit.ι F j).app (limit G) ≫ α.hom ≫ limit.π (G ⋙ colimit F) k =
          (F.obj j).map (limit.π G k) ≫ (colimit.ι F j).app (G.obj k) := by
      dsimp [α]
      calc
        (colimit.ι F j).app (limit G) ≫ e₀.hom ≫ e₂.hom ≫ e₃.hom ≫ e₄.hom ≫
            limit.π (G ⋙ colimit F) k =
          colimit.ι (F ⋙ (evaluation Cᵒᵖ (Type w)).obj (limit G)) j ≫ e₂.hom ≫
            e₃.hom ≫ e₄.hom ≫ limit.π (G ⋙ colimit F) k := by
              exact colimitObjIsoColimitCompEvaluation_ι_app_hom_assoc F j (limit G)
                (e₂.hom ≫ e₃.hom ≫ e₄.hom ≫ limit.π (G ⋙ colimit F) k)
        _ = e.hom.app j ≫ colimit.ι (limit D) j ≫ e₃.hom ≫ e₄.hom ≫
            limit.π (G ⋙ colimit F) k := by
              exact HasColimit.ι_isoOfNatIso_hom_assoc e j
                (e₃.hom ≫ e₄.hom ≫ limit.π (G ⋙ colimit F) k)
        _ = e.hom.app j ≫ colimit.ι (limit D) j ≫ e₃.hom ≫
            limit.π (colimit D.flip) k ≫
              (colimitCompWhiskeringLeftIsoCompColimit F G).hom.app k := by
              dsimp only [e₄]
              rw [HasLimit.isoOfNatIso_hom_π]
              simpa only [D, H, E, Functor.flip_flip]
        _ = e.hom.app j ≫ (limit.π D k).app j ≫ (colimit.ι D.flip j).app k ≫
            (colimitCompWhiskeringLeftIsoCompColimit F G).hom.app k := by
              dsimp only [e₃]
              exact congrArg (fun q => e.hom.app j ≫ q) <|
                (show colimit.ι (limit D) j ≫ (colimitLimitIso D).hom ≫
                    limit.π (colimit D.flip) k ≫
                      (colimitCompWhiskeringLeftIsoCompColimit F G).hom.app k =
                  (limit.π D k).app j ≫ (colimit.ι D.flip j).app k ≫
                    (colimitCompWhiskeringLeftIsoCompColimit F G).hom.app k from
                  ι_colimitLimitIso_limit_π_assoc D j k
                    ((colimitCompWhiskeringLeftIsoCompColimit F G).hom.app k))
        _ = (F.obj j).map (limit.π G k) ≫ (colimit.ι F j).app (G.obj k) := by
              have hι :
                  (colimit.ι D.flip j).app k ≫
                    (colimitCompWhiskeringLeftIsoCompColimit F G).hom.app k =
                    (colimit.ι F j).app (G.obj k) := by
                have hn := congrArg (fun η => η.app k)
                  (ι_colimitCompWhiskeringLeftIsoCompColimit_hom F G j)
                simpa only [NatTrans.comp_app, D, H, E, Functor.flip_flip,
                  Functor.whiskerLeft_app] using hn
              simp [e, e₁, limitIsoFlipCompLim]
              calc
                _ = (F.obj j).map (limit.π G k) ≫
                    ((colimit.ι D.flip j).app k ≫
                      (colimitCompWhiskeringLeftIsoCompColimit F G).hom.app k) :=
                  preservesLimitIso_hom_π_assoc (F.obj j) G k _
                _ = (F.obj j).map (limit.π G k) ≫ (colimit.ι F j).app (G.obj k) := by
                  rw [hι]
                _ = (colimit.ι F j).app (limit G) ≫ (colimit F).map (limit.π G k) := by
                  rw [(colimit.ι F j).naturality]
    calc
      (colimit.ι F j).app (limit G) ≫ limit.post G (colimit F) ≫
          limit.π (G ⋙ colimit F) k =
        (F.obj j).map (limit.π G k) ≫ (colimit.ι F j).app (G.obj k) := by
          rw [limit.post_π, (colimit.ι F j).naturality]
      _ = (colimit.ι F j).app (limit G) ≫ α.hom ≫ limit.π (G ⋙ colimit F) k := hcomp.symm
  haveI : IsIso (limit.post G (colimit F)) := by
    rw [hpost]
    infer_instance
  exact preservesLimit_of_isIso_post (F := G) (G := colimit F)

/-- Filtered colimits in the completion are computed objectwise. -/
theorem completion_isColimit_evaluation {J : Type w} [SmallCategory J] [IsFiltered J]
    {F : J ⥤ Completion.{w} C} {c : Cocone F} (hc : IsColimit c) (A : C) :
    Nonempty (IsColimit ((ObjectProperty.ι (IsCompletionPresheaf.{w} C) ⋙
      (evaluation Cᵒᵖ (Type w)).obj (op A)).mapCocone c)) := by
  let P : ObjectProperty (Cᵒᵖ ⥤ Type w) := IsCompletionPresheaf.{w} C
  letI : ObjectProperty.IsClosedUnderColimitsOfShape P J := by
    constructor
    intro Y ⟨p⟩
    refine ⟨fun I hI => ?_, fun A B X Q i f k j h hi => ?_⟩
    · have hF : ∀ t, PreservesLimit (Functor.empty.{0} Cᵒᵖ) (p.diag.obj t) := by
        intro t
        exact completionPresheaf_preservesTerminal _ (p.prop_diag_obj t) hI
      have hcI : IsLimit (asEmptyCone (op I)) := hI.op
      have hcol := filteredColimit_preservesLimit (C := C)
        (Functor.empty.{0} Cᵒᵖ) (asEmptyCone (op I)) hcI p.diag hF
      haveI : PreservesLimit (Functor.empty.{0} Cᵒᵖ) Y :=
        (preservesLimit_iff_of_natIso (Functor.empty.{0} Cᵒᵖ)
          (IsColimit.coconePointUniqueUpToIso p.isColimit (colimit.isColimit p.diag))).2 hcol
      exact ⟨Types.isTerminalEquivUnique _ (hI.op.isTerminalObj Y _)⟩
    · have hF : ∀ t, PreservesLimit (cospan i.op f.op) (p.diag.obj t) := by
        intro t
        exact completionPresheaf_preservesCofibrationPushout _ (p.prop_diag_obj t)
          i f k j h hi
      let hpb := h.op.flip
      have hcol := filteredColimit_preservesLimit (C := C)
        (cospan i.op f.op) hpb.cone hpb.isLimit p.diag hF
      haveI : PreservesLimit (cospan i.op f.op) Y :=
        (preservesLimit_iff_of_natIso (cospan i.op f.op)
          (IsColimit.coconePointUniqueUpToIso p.isColimit (colimit.isColimit p.diag))).2 hcol
      exact h.op.flip.map Y
  have h₁ := isColimitOfPreserves (ObjectProperty.ι P) hc
  have h₂ := isColimitOfPreserves ((evaluation Cᵒᵖ (Type w)).obj (op A)) h₁
  exact ⟨h₂⟩

theorem completion_colimit_exists_rep {J : Type w} [SmallCategory J] [IsFiltered J]
    {F : J ⥤ Completion.{w} C} {c : Cocone F} (hc : IsColimit c) {A : C}
    (x : c.pt.obj.obj (op A)) :
    ∃ (j : J) (y : (F.obj j).obj.obj (op A)), (c.ι.app j).hom.app (op A) y = x := by
  obtain ⟨hcA⟩ := completion_isColimit_evaluation hc A
  exact Types.jointly_surjective_of_isColimit hcA x

theorem completion_colimit_exists_eq {J : Type w} [SmallCategory J] [IsFiltered J]
    {F : J ⥤ Completion.{w} C} {c : Cocone F} (hc : IsColimit c) {A : C} {j : J}
    (x y : (F.obj j).obj.obj (op A))
    (h : (c.ι.app j).hom.app (op A) x = (c.ι.app j).hom.app (op A) y) :
    ∃ (k : J) (f : j ⟶ k), (F.map f).hom.app (op A) x = (F.map f).hom.app (op A) y := by
  obtain ⟨hcA⟩ := completion_isColimit_evaluation hc A
  exact (Types.FilteredColimit.isColimit_eq_iff' hcA x y).mp h

/-- A filtered colimit of weak equivalences of the completion is a weak equivalence. -/
theorem completion_weakEquivalence_of_isColimit [CategoryWithWeakEquivalences C]
    {J : Type w} [SmallCategory J] [IsFiltered J]
    {F₁ F₂ : J ⥤ Completion.{w} C} (t : F₁ ⟶ F₂)
    (ht : ∀ j, Completion.weakEquivalences C (t.app j))
    {c₁ : Cocone F₁} (hc₁ : IsColimit c₁) {c₂ : Cocone F₂} (hc₂ : IsColimit c₂)
    (u : c₁.pt ⟶ c₂.pt) (hu : ∀ j, c₁.ι.app j ≫ u = t.app j ≫ c₂.ι.app j) :
    Completion.weakEquivalences C u := by
  change Henry.presheafWeakEquivalences u.hom
  intro A B i hi a b hab
  obtain ⟨j, x, hx⟩ := completion_colimit_exists_rep hc₁ a
  obtain ⟨j', y, hy⟩ := completion_colimit_exists_rep hc₂ b
  let k := IsFiltered.max j j'
  let f : j ⟶ k := IsFiltered.leftToMax j j'
  let g : j' ⟶ k := IsFiltered.rightToMax j j'
  let x₀ := (F₁.map f).hom.app (op A) x
  let y₀ := (F₂.map g).hom.app (op B) y
  have hx₀ : (c₁.ι.app k).hom.app (op A) x₀ = a := by
    have h := congrArg (fun q => q.hom.app (op A)) (c₁.w f)
    have h' := congrArg (fun q => q x) h
    change (c₁.ι.app k).hom.app (op A)
      ((F₁.map f).hom.app (op A) x) = (c₁.ι.app j).hom.app (op A) x at h'
    exact h'.trans hx
  have hy₀ : (c₂.ι.app k).hom.app (op B) y₀ = b := by
    have h := congrArg (fun q => q.hom.app (op B)) (c₂.w g)
    have h' := congrArg (fun q => q y) h
    change (c₂.ι.app k).hom.app (op B)
      ((F₂.map g).hom.app (op B) y) = (c₂.ι.app j').hom.app (op B) y at h'
    exact h'.trans hy
  have hu₀ : u.hom.app (op A) ((c₁.ι.app k).hom.app (op A) x₀) =
      (c₂.ι.app k).hom.app (op A) ((t.app k).hom.app (op A) x₀) := by
    have h := congrArg (fun q => q.hom.app (op A)) (hu k)
    have h' := congrArg (fun q => q x₀) h
    exact h'
  have hboundaryAtColimit :
      (c₂.ι.app k).hom.app (op A) ((t.app k).hom.app (op A) x₀) =
        (c₂.ι.app k).hom.app (op A) ((F₂.obj k).obj.map i.op y₀) := by
    calc
      (c₂.ι.app k).hom.app (op A) ((t.app k).hom.app (op A) x₀) =
          u.hom.app (op A) ((c₁.ι.app k).hom.app (op A) x₀) := hu₀.symm
      _ = u.hom.app (op A) a := by rw [hx₀]
      _ = c₂.pt.obj.map i.op b := hab
      _ = (c₂.ι.app k).hom.app (op A) ((F₂.obj k).obj.map i.op y₀) := by
        rw [← hy₀, ← NatTrans.naturality_apply]
  obtain ⟨l, q, hq⟩ := completion_colimit_exists_eq hc₂
    (x := (t.app k).hom.app (op A) x₀)
    (y := (F₂.obj k).obj.map i.op y₀) hboundaryAtColimit
  let x₁ := (F₁.map q).hom.app (op A) x₀
  let y₁ := (F₂.map q).hom.app (op B) y₀
  have hboundary : (t.app l).hom.app (op A) x₁ = (F₂.obj l).obj.map i.op y₁ := by
    calc
      (t.app l).hom.app (op A) x₁ =
          (F₂.map q).hom.app (op A) ((t.app k).hom.app (op A) x₀) := by
        have h := congrArg (fun z => z.hom.app (op A)) (t.naturality q)
        have h' := congrArg (fun z => z x₀) h
        exact h'
      _ = (F₂.map q).hom.app (op A) ((F₂.obj k).obj.map i.op y₀) := hq
      _ = (F₂.obj l).obj.map i.op y₁ := by
        exact NatTrans.naturality_apply (F₂.map q).hom i.op y₀
  obtain ⟨lift, cyl, H, hLift, h₀, h₁⟩ := ht l i hi x₁ y₁ hboundary
  have hx₁ : (c₁.ι.app l).hom.app (op A) x₁ = a := by
    have h := congrArg (fun z => z.hom.app (op A)) (c₁.w q)
    have h' := congrArg (fun z => z x₀) h
    change (c₁.ι.app l).hom.app (op A)
      ((F₁.map q).hom.app (op A) x₀) = (c₁.ι.app k).hom.app (op A) x₀ at h'
    exact h'.trans hx₀
  have hy₁ : (c₂.ι.app l).hom.app (op B) y₁ = b := by
    have h := congrArg (fun z => z.hom.app (op B)) (c₂.w q)
    have h' := congrArg (fun z => z y₀) h
    change (c₂.ι.app l).hom.app (op B)
      ((F₂.map q).hom.app (op B) y₀) = (c₂.ι.app k).hom.app (op B) y₀ at h'
    exact h'.trans hy₀
  refine ⟨(c₁.ι.app l).hom.app (op B) lift, cyl,
    (c₂.ι.app l).hom.app (op cyl.I) H, ?_, ?_, ?_⟩
  · rw [← NatTrans.naturality_apply, hLift, hx₁]
  · calc
      c₂.pt.obj.map (cyl.j₀ ≫ cyl.c).op
          ((c₂.ι.app l).hom.app (op cyl.I) H) =
          (c₂.ι.app l).hom.app (op B)
            ((F₂.obj l).obj.map (cyl.j₀ ≫ cyl.c).op H) := by
              rw [← NatTrans.naturality_apply]
      _ = (c₂.ι.app l).hom.app (op B) ((t.app l).hom.app (op B) lift) := by
        rw [h₀]
      _ = u.hom.app (op B) ((c₁.ι.app l).hom.app (op B) lift) := by
        have h := congrArg (fun z => z.hom.app (op B)) (hu l)
        have h' := congrArg (fun z => z lift) h
        exact h'.symm
  · calc
      c₂.pt.obj.map (cyl.j₁ ≫ cyl.c).op
          ((c₂.ι.app l).hom.app (op cyl.I) H) =
          (c₂.ι.app l).hom.app (op B)
            ((F₂.obj l).obj.map (cyl.j₁ ≫ cyl.c).op H) := by
              rw [← NatTrans.naturality_apply]
      _ = (c₂.ι.app l).hom.app (op B) y₁ := by rw [h₁]
      _ = b := hy₁

/-- The completion of an essentially small category is locally small. -/
theorem completion_locallySmall [EssentiallySmall.{w} C] :
    LocallySmall.{w} (Completion.{w} C) := by
  haveI := presheaves_locallyPresentable.{w} (C := C)
  change LocallySmall.{w} (ObjectProperty.FullSubcategory (IsCompletionPresheaf.{w} C))
  infer_instance

/-- Representable objects of the completion are finitely presentable. -/
theorem completionSmallYoneda_isFinitelyPresentable [LocallySmall.{w} C] (A : C) :
    IsFinitelyPresentable.{w} (completionSmallYoneda.{w}.obj A) := by
  rw [isFinitelyPresentable_iff_preservesFilteredColimitsOfSize]
  let E₀ : Completion.{w} C ⥤ Type w :=
    ObjectProperty.ι (IsCompletionPresheaf.{w} C) ⋙
      (evaluation Cᵒᵖ (Type w)).obj (op A)
  let E : Completion.{w} C ⥤ Type (max u w) := E₀ ⋙ uliftFunctor.{u, w}
  let H : Completion.{w} C ⥤ Type (max u w) :=
    coyoneda.obj (op (completionSmallYoneda.{w}.obj A))
  let e : H ≅ E := NatIso.ofComponents
    (fun X => Equiv.toIso
      ((completionSmallYonedaHomEquiv A X).trans Equiv.ulift.{u, w}.symm))
    (by
      intro X Y f
      ext g
      change ULift.up (completionSmallYonedaHomEquiv A Y (g ≫ f)) =
        ULift.up (f.hom.app (op A) (completionSmallYonedaHomEquiv A X g))
      apply ULift.ext
      change shrinkYonedaEquiv (g.hom ≫ f.hom) =
        f.hom.app (op A) (shrinkYonedaEquiv g.hom)
      rw [shrinkYonedaEquiv_comp])
  refine ⟨fun J _ _ => ?_⟩
  haveI : PreservesColimitsOfShape J E := by
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨isColimitOfPreserves (uliftFunctor.{u, w})
      (Classical.choice (completion_isColimit_evaluation hc A))⟩
  exact preservesColimitsOfShape_of_natIso e.symm

end HomotopyHypothesis.Category.SemiModelStructure
