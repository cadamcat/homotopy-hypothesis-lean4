import OAI.CategoryTheory.Globular.Main
import HomotopyHypothesis.Blueprint.Henry.All
import HomotopyHypothesis.Challenge
/-!
# Definitions of the outer blueprint

The statement of `HomotopyHypothesis.Challenge` restated on OpenAI's library definitions
(`OAI.Grothendieck`), and the small cylinder category `A_fin` of finitely cellular models used in
the comparison with Henry's framework.

* `OAIStatement`: the statement `HomotopyHypothesis.Statement` with OpenAI's globular theories,
  models and weak equivalences in place of the copies in `Challenge.lean`. The topological globes,
  realizations, `Π_∞` and weak homotopy equivalences are defined exactly as there.
* `Afin C hC`: the full subcategory of `C.Model` on finitely cellular models (finite composites of
  pushouts of the boundary inclusions `I C n : ∂Dₙ ⟶ Dₙ`), with the finite boundary-cell maps as
  cofibrations and the restriction of the weak equivalences of models as weak equivalences
  (OpenAI, *The Grothendieck homotopy hypothesis via elementary expansions*, proof of Cor. 4.2;
  S. Henry, arXiv:1609.04622, Def. 5.3.2 and Prop. 5.3.6).
-/

noncomputable section

namespace HomotopyHypothesis.Blueprint

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck

/-! ### The topological globes on OpenAI's globe category -/

/-- The topological globes on morphisms of OpenAI's globe category (same maps as
`HomotopyHypothesis.globeMap`). -/
def oaiGlobeMap : ∀ {m n : ℕ}, OAI.Grothendieck.Globe.Face m n → C(Ball m, Ball n)
  | _, _, .id _ => ContinuousMap.id _
  | _, _, .face h b => ballFace h b

theorem oaiGlobeMap_comp {m n k : ℕ} (f : OAI.Grothendieck.Globe.Face m n)
    (g : OAI.Grothendieck.Globe.Face n k) :
    oaiGlobeMap (f.comp g) = (oaiGlobeMap g).comp (oaiGlobeMap f) := by
  cases f with
  | id => rfl
  | face h b =>
    cases g with
    | id => rfl
    | face h' b' =>
      refine ContinuousMap.ext fun x => Subtype.ext ?_
      exact (faceVec_faceVec h b b' x.1 (mem_closedBall_zero_iff.1 x.2)).symm

/-- Ara's topological globes on OpenAI's globe category. -/
def oaiTopGlobes : OAI.Grothendieck.Globe ⥤ TopCat.{u} where
  obj n := TopCat.disk.{u} n.dim
  map f := TopCat.ofHom
    ⟨fun x => ULift.up (oaiGlobeMap f x.down),
      continuous_uliftUp.comp ((oaiGlobeMap f).continuous.comp continuous_uliftDown)⟩
  map_id _ := rfl
  map_comp f g :=
    TopCat.ext fun x => congrArg ULift.up (DFunLike.congr_fun (oaiGlobeMap_comp f g) x.down)

/-! ### Realizations, `Π_∞` and the statement on OpenAI's definitions -/

/-- A topological realization of an OpenAI globular theory (as `HomotopyHypothesis.TopRealization`).
-/
structure OAIRealization (C : GlobularTheory.{u}) where
  /-- The underlying functor. -/
  functor : C.Obj ⥤ TopCat.{u}
  /-- On globes, the functor is the standard topological globes. -/
  onGlobes : C.globes ⋙ functor ≅ oaiTopGlobes.{u}
  /-- The functor sends globular sums to pushouts. -/
  sums : ∀ (S : Shape) (b h : ℕ) (hl : b < S.1) (hr : b < h),
    IsPushout (functor.map (C.toTheoryData.arity.map (S.seam hl)))
      (functor.map (C.toTheoryData.arity.map (Shape.face hr false)))
      (functor.map (C.toTheoryData.arity.map (S.inl b h hl hr)))
      (functor.map (C.toTheoryData.arity.map (S.inr b h hl hr)))

/-- The fundamental ∞-groupoid of a space for a realization. -/
def OAIRealization.groupoid {C : GlobularTheory.{u}} (R : OAIRealization C) (X : TopCat.{u}) :
    C.Model where
  presheaf := R.functor.op ⋙ yoneda.obj X
  sums T b h hl hr := ((R.sums T b h hl hr).op.map (yoneda.obj X)).flip

/-- The fundamental ∞-groupoid functor `Π_∞ : Top → ∞-Gpd_C` of a realization. -/
def OAIRealization.Pi {C : GlobularTheory.{u}} (R : OAIRealization C) :
    TopCat.{u} ⥤ C.Model where
  obj := R.groupoid
  map f := show (R.functor.op ⋙ yoneda.obj _) ⟶ (R.functor.op ⋙ yoneda.obj _) from
    Functor.whiskerLeft R.functor.op (yoneda.map f)
  map_id _ := by apply NatTrans.ext; funext; rfl
  map_comp _ _ := by apply NatTrans.ext; funext; rfl

/-- The weak equivalences of models of an OpenAI coherator. -/
def W {C : GlobularTheory.{u}} (hC : C.IsCoherator) : MorphismProperty C.Model :=
  fun _ _ f => GlobularTheory.Model.WeakEquivalence hC f

/-- `HomotopyHypothesis.Statement` on OpenAI's definitions. -/
def OAIStatement : Prop :=
  ∀ (C : GlobularTheory.{u}) (hC : C.IsCoherator),
    Nonempty (OAIRealization C) ∧
    ∀ R : OAIRealization C,
      weakHomotopyEquivalences ≤ (W hC).inverseImage R.Pi ∧
        (R.Pi ⋙ (W hC).Q).IsLocalization weakHomotopyEquivalences

/-! ### The cylinder category `A_fin` of finitely cellular models -/

section Afin

variable (C : GlobularTheory.{u})

/-- The finite boundary-cell maps: finite composites of isomorphisms and pushouts of the boundary
inclusions `I C n : ∂Dₙ ⟶ Dₙ`. -/
def finiteCellMaps : MorphismProperty C.Model :=
  ((MorphismProperty.ofHoms (fun n : ℕ => GlobularTheory.Model.I C n)).pushouts ⊔
    MorphismProperty.isomorphisms C.Model).multiplicativeClosure

/-- Finitely cellular models (Henry Def. 5.3.2): the map from the initial model is a finite
boundary-cell map. -/
def IsFinitelyCellular : ObjectProperty C.Model := fun X =>
  finiteCellMaps C (initial.to X)

/-- The category `A_fin` of finitely cellular models, with finite boundary-cell maps as
cofibrations and weak equivalences of models as weak equivalences. -/
def Afin (_hC : C.IsCoherator) : Type (u + 1) :=
  ObjectProperty.FullSubcategory (IsFinitelyCellular C)

variable {C} (hC : C.IsCoherator)

instance : Category.{u} (Afin C hC) :=
  inferInstanceAs (Category (ObjectProperty.FullSubcategory (IsFinitelyCellular C)))

/-- The inclusion `A_fin ⥤ C.Model`. -/
def Afin.ι : Afin C hC ⥤ C.Model := ObjectProperty.ι (IsFinitelyCellular C)

instance : (Afin.ι hC).Full := inferInstanceAs (ObjectProperty.ι _).Full
instance : (Afin.ι hC).Faithful := inferInstanceAs (ObjectProperty.ι _).Faithful

instance : CategoryWithCofibrations (Afin C hC) where
  cofibrations := (finiteCellMaps C).inverseImage (Afin.ι hC)

instance : CategoryWithWeakEquivalences (Afin C hC) where
  weakEquivalences := (W hC).inverseImage (Afin.ι hC)

/-- The marked object `D₀` of `A_fin`. -/
def Afin.disk0 (h : IsFinitelyCellular C (GlobularTheory.Model.disk C 0)) : Afin C hC :=
  ⟨GlobularTheory.Model.disk C 0, h⟩

end Afin

end HomotopyHypothesis.Blueprint
