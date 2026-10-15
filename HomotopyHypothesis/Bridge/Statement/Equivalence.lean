import HomotopyHypothesis.Bridge.Statement.Shapes
import HomotopyHypothesis.Bridge.Statement.Theory
import HomotopyHypothesis.Bridge.Statement.Weak
import HomotopyHypothesis.Blueprint.Bridge.GlobeOfOAI
import HomotopyHypothesis.Blueprint.Bridge.GlobeToOAI
import HomotopyHypothesis.Blueprint.Bridge.GlobeToOAICompGlobeOfOAI
import HomotopyHypothesis.Blueprint.Bridge.TopGlobesEq
import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Challenge
/-!
# The bridge from OpenAI's statement to the statement

The restriction of models along the underlying functor of a transported theory is an equivalence
of categories which preserves and reflects weak equivalences; realizations transport in both
directions; the localization property transports along the resulting equivalence of localized
categories.
-/

noncomputable section

namespace HomotopyHypothesis.Bridge.Statement

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

/-! ### Shapes: the other direction -/

/-- Shapes of the statement as OpenAI's shapes. -/
def shapeToOAI (S : Grothendieck.Shape) : OAI.Grothendieck.Shape := ⟨S.1, tableToOAI S.2⟩

theorem shapeOfOAI_shapeToOAI (S : Grothendieck.Shape) : shapeOfOAI (shapeToOAI S) = S := by
  obtain ⟨n, T⟩ := S
  change (⟨n, tableOfOAI (tableToOAI T)⟩ : Grothendieck.Shape) = ⟨n, T⟩
  rw [tableOfOAI_tableToOAI]

theorem height_tableOfOAI {n : ℕ} (T : OAI.Grothendieck.Table n) :
    (tableOfOAI T).height = T.height := by
  induction T with
  | globe => rfl
  | attach T b h hl hr ih =>
    change max (tableOfOAI T).height h = max T.height h
    rw [ih]

/-! ### Squares and natural isomorphisms -/

theorem isPullback_of_natIso {A B : Type*} [Category A] [Category B] {F G : A ⥤ B} (η : F ≅ G)
    {P X Y Z : A} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback (G.map fst) (G.map snd) (G.map f) (G.map g)) :
    IsPullback (F.map fst) (F.map snd) (F.map f) (F.map g) :=
  h.of_iso (η.app P).symm (η.app X).symm (η.app Y).symm (η.app Z).symm
    (η.inv.naturality _) (η.inv.naturality _) (η.inv.naturality _) (η.inv.naturality _)

theorem isPushout_of_natIso {A B : Type*} [Category A] [Category B] {F G : A ⥤ B} (η : F ≅ G)
    {Z X Y P : A} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
    (h : IsPushout (G.map f) (G.map g) (G.map inl) (G.map inr)) :
    IsPushout (F.map f) (F.map g) (F.map inl) (F.map inr) :=
  h.of_iso (η.app Z).symm (η.app X).symm (η.app Y).symm (η.app P).symm
    (η.inv.naturality _) (η.inv.naturality _) (η.inv.naturality _) (η.inv.naturality _)

/-! ### The underlying functor is an equivalence -/

section Equivalence

variable (C : Grothendieck.GlobularTheory.{v})

instance : (objFunctor C.toTheoryData).EssSurj where
  mem_essImage Y :=
    ⟨⟨shapeToOAI Y.shape⟩, ⟨C.arity.mapIso (eqToIso (shapeOfOAI_shapeToOAI Y.shape))⟩⟩

instance : (objFunctor C.toTheoryData).IsEquivalence where

/-- Precomposition with the underlying functor, as an equivalence of presheaf categories. -/
abbrev whiskerEquiv : (C.Objᵒᵖ ⥤ Type v) ≌ ((theoryToOAI C).Objᵒᵖ ⥤ Type v) :=
  ((objFunctor C.toTheoryData).asEquivalence.op.symm).congrLeft

instance : (modelToOAI C).Faithful where
  map_injective {_ _} _ _ h := (whiskerEquiv C).fullyFaithfulFunctor.map_injective h

instance : (modelToOAI C).Full where
  map_surjective {_ _} g :=
    ⟨(whiskerEquiv C).fullyFaithfulFunctor.preimage g,
      (whiskerEquiv C).fullyFaithfulFunctor.map_preimage g⟩

/-- A model of the transported theory as a model of the original theory. -/
def modelOfOAI (Y : (theoryToOAI C).Model) : C.Model where
  presheaf := (whiskerEquiv C).inverse.obj Y.presheaf
  sums S b h hl hr := by
    obtain ⟨S', rfl⟩ : ∃ S', shapeOfOAI S' = S := ⟨shapeToOAI S, shapeOfOAI_shapeToOAI S⟩
    have H := isPullback_of_natIso ((whiskerEquiv C).counitIso.app Y.presheaf)
      (Y.sums S' b h hl hr)
    change IsPullback
      (((whiskerEquiv C).inverse.obj Y.presheaf).map
        (C.arity.map (shapeFunctor.map (S'.inl b h hl hr))).op)
      (((whiskerEquiv C).inverse.obj Y.presheaf).map
        (C.arity.map (shapeFunctor.map (S'.inr b h hl hr))).op)
      (((whiskerEquiv C).inverse.obj Y.presheaf).map
        (C.arity.map (shapeFunctor.map (S'.seam hl))).op)
      (((whiskerEquiv C).inverse.obj Y.presheaf).map
        (C.arity.map (shapeFunctor.map (OAI.Grothendieck.Shape.face hr false))).op) at H
    rw [shapeFunctor_inl S' b h hl hr, shapeFunctor_inr S' b h hl hr, shapeFunctor_seam S' hl,
      shapeFunctor_face hr false] at H
    exact H

/-- The restriction of `modelOfOAI C Y` is isomorphic to `Y`. -/
def modelOfOAIIso (Y : (theoryToOAI C).Model) : (modelToOAI C).obj (modelOfOAI C Y) ≅ Y where
  hom := ((whiskerEquiv C).counitIso.app Y.presheaf).hom
  inv := ((whiskerEquiv C).counitIso.app Y.presheaf).inv
  hom_inv_id := ((whiskerEquiv C).counitIso.app Y.presheaf).hom_inv_id
  inv_hom_id := ((whiskerEquiv C).counitIso.app Y.presheaf).inv_hom_id

instance : (modelToOAI C).EssSurj where
  mem_essImage Y := ⟨modelOfOAI C Y, ⟨modelOfOAIIso C Y⟩⟩

instance : (modelToOAI C).IsEquivalence where

end Equivalence

/-! ### Weak equivalences of OpenAI's models are closed under composition and isomorphisms -/

section OAIWeak

variable {D : OAI.Grothendieck.GlobularTheory.{v}} (hD : D.IsCoherator)

theorem oai_componentsMap_comp {X Y Z : D.Model} (f : X ⟶ Y) (g : Y ⟶ Z) :
    OAI.Grothendieck.GlobularTheory.Model.componentsMap (f ≫ g) =
      OAI.Grothendieck.GlobularTheory.Model.componentsMap g ∘
        OAI.Grothendieck.GlobularTheory.Model.componentsMap f := by
  funext q
  induction q using Quot.ind
  rfl

theorem oai_componentsMap_id (X : D.Model) :
    OAI.Grothendieck.GlobularTheory.Model.componentsMap (𝟙 X) = id := by
  funext q
  induction q using Quot.ind
  rfl

theorem oai_homotopyMap_comp {X Y Z : D.Model} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : X.underlying.Cell 0) (n : ℕ) :
    OAI.Grothendieck.GlobularTheory.Model.homotopyMap (f ≫ g) hD x n =
      OAI.Grothendieck.GlobularTheory.Model.homotopyMap g hD _ n ∘
        OAI.Grothendieck.GlobularTheory.Model.homotopyMap f hD x n := by
  funext q
  induction q using Quot.ind
  rfl

theorem oai_homotopyMap_id (X : D.Model) (x : X.underlying.Cell 0) (n : ℕ) :
    OAI.Grothendieck.GlobularTheory.Model.homotopyMap (𝟙 X) hD x n = id := by
  funext q
  induction q using Quot.ind
  rfl

theorem oai_weakEquivalence_comp {X Y Z : D.Model} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : OAI.Grothendieck.GlobularTheory.Model.WeakEquivalence hD f)
    (hg : OAI.Grothendieck.GlobularTheory.Model.WeakEquivalence hD g) :
    OAI.Grothendieck.GlobularTheory.Model.WeakEquivalence hD (f ≫ g) := by
  refine ⟨?_, fun x n => ?_⟩
  · rw [oai_componentsMap_comp]
    exact hg.1.comp hf.1
  · rw [oai_homotopyMap_comp]
    exact (hg.2 _ n).comp (hf.2 x n)

theorem oai_weakEquivalence_of_iso {X Y : D.Model} (e : X ≅ Y) :
    OAI.Grothendieck.GlobularTheory.Model.WeakEquivalence hD e.hom := by
  refine ⟨Function.bijective_iff_has_inverse.2
    ⟨OAI.Grothendieck.GlobularTheory.Model.componentsMap e.inv, fun q => ?_, fun q => ?_⟩,
    fun x n => ⟨?_, ?_⟩⟩
  · change (OAI.Grothendieck.GlobularTheory.Model.componentsMap e.inv ∘
      OAI.Grothendieck.GlobularTheory.Model.componentsMap e.hom) q = q
    rw [← oai_componentsMap_comp, e.hom_inv_id, oai_componentsMap_id]
    rfl
  · change (OAI.Grothendieck.GlobularTheory.Model.componentsMap e.hom ∘
      OAI.Grothendieck.GlobularTheory.Model.componentsMap e.inv) q = q
    rw [← oai_componentsMap_comp, e.inv_hom_id, oai_componentsMap_id]
    rfl
  · have h1 : Function.Injective
        (OAI.Grothendieck.GlobularTheory.Model.homotopyMap (e.hom ≫ e.inv) hD x n) := by
      rw [e.hom_inv_id, oai_homotopyMap_id]
      exact Function.injective_id
    rw [oai_homotopyMap_comp] at h1
    exact h1.of_comp
  · have h2 : ∀ y, Function.Surjective
        (OAI.Grothendieck.GlobularTheory.Model.homotopyMap (e.inv ≫ e.hom) hD y n) := by
      intro y
      rw [e.inv_hom_id, oai_homotopyMap_id]
      exact Function.surjective_id
    have h3 := h2 ((OAI.Grothendieck.GlobularTheory.Model.underlyingMap e.hom).app 0 x)
    rw [oai_homotopyMap_comp] at h3
    have h4 := h3.of_comp
    have hc : (show X.presheaf ⟶ X.presheaf from e.hom ≫ e.inv) = 𝟙 X.presheaf := e.hom_inv_id
    have hx : (OAI.Grothendieck.GlobularTheory.Model.underlyingMap e.inv).app 0
        ((OAI.Grothendieck.GlobularTheory.Model.underlyingMap e.hom).app 0 x) = x :=
      ConcreteCategory.congr_hom
        (NatTrans.congr_app hc (Opposite.op (D.globes.obj (OAI.Grothendieck.Globe.mk 0)))) x
    have key : ∀ x₁ x₂ : X.underlying.Cell 0, x₁ = x₂ → Function.Surjective
        (OAI.Grothendieck.GlobularTheory.Model.homotopyMap e.hom hD x₁ n) → Function.Surjective
        (OAI.Grothendieck.GlobularTheory.Model.homotopyMap e.hom hD x₂ n) := by
      intro x₁ x₂ h hs
      subst h
      exact hs
    exact key _ _ hx h4

end OAIWeak

/-! ### Realizations from the transported theory -/

/-- A realization of the transported theory as a realization of the original theory. -/
def realizationOfOAI {C : Grothendieck.GlobularTheory.{u}}
    (R : HomotopyHypothesis.Blueprint.OAIRealization (theoryToOAI C)) :
    HomotopyHypothesis.TopRealization C where
  functor := (objFunctor C.toTheoryData).inv ⋙ R.functor
  onGlobes := by
    have hg : C.globes = HomotopyHypothesis.Blueprint.globeToOAI ⋙
        ((theoryToOAI C).globes ⋙ objFunctor C.toTheoryData) := by
      rw [globes_comp_objFunctor, ← Functor.assoc,
        HomotopyHypothesis.Blueprint.globeToOAI_comp_globeOfOAI, Functor.id_comp]
    exact eqToIso (by rw [hg]; rfl) ≪≫
      Functor.isoWhiskerLeft
        (HomotopyHypothesis.Blueprint.globeToOAI ⋙ (theoryToOAI C).globes)
        (Functor.isoWhiskerRight (objFunctor C.toTheoryData).asEquivalence.unitIso.symm
          R.functor ≪≫ R.functor.leftUnitor) ≪≫
      Functor.isoWhiskerLeft HomotopyHypothesis.Blueprint.globeToOAI R.onGlobes ≪≫
      eqToIso HomotopyHypothesis.Blueprint.topGlobes_eq.symm
  sums S b h hl hr := by
    obtain ⟨S', rfl⟩ : ∃ S', shapeOfOAI S' = S := ⟨shapeToOAI S, shapeOfOAI_shapeToOAI S⟩
    have H := isPushout_of_natIso
      (F := (objFunctor C.toTheoryData ⋙ (objFunctor C.toTheoryData).inv) ⋙ R.functor)
      (Functor.isoWhiskerRight (objFunctor C.toTheoryData).asEquivalence.unitIso.symm
          R.functor ≪≫ R.functor.leftUnitor)
      (R.sums S' b h hl hr)
    change IsPushout
      (((objFunctor C.toTheoryData).inv ⋙ R.functor).map
        (C.arity.map (shapeFunctor.map (S'.seam hl))))
      (((objFunctor C.toTheoryData).inv ⋙ R.functor).map
        (C.arity.map (shapeFunctor.map (OAI.Grothendieck.Shape.face hr false))))
      (((objFunctor C.toTheoryData).inv ⋙ R.functor).map
        (C.arity.map (shapeFunctor.map (S'.inl b h hl hr))))
      (((objFunctor C.toTheoryData).inv ⋙ R.functor).map
        (C.arity.map (shapeFunctor.map (S'.inr b h hl hr)))) at H
    rw [shapeFunctor_inl S' b h hl hr, shapeFunctor_inr S' b h hl hr, shapeFunctor_seam S' hl,
      shapeFunctor_face hr false] at H
    exact H

/-! ### Fillers of the transported theory -/

theorem parallel_theoryToOAI_iff {C : Grothendieck.GlobularTheory.{v}} {S : OAI.Grothendieck.Shape}
    (n : ℕ) (s t : (theoryToOAI C).Hom (OAI.Grothendieck.Shape.globe n) S) :
    (theoryToOAI C).Parallel n s t ↔ C.Parallel n s t := by
  cases n with
  | zero => exact ⟨fun _ => trivial, fun _ => trivial⟩
  | succ n =>
    change C.comp (C.base (shapeFunctor.map
          (OAI.Grothendieck.Shape.face (Nat.lt_succ_self n) false))) s =
        C.comp (C.base (shapeFunctor.map
          (OAI.Grothendieck.Shape.face (Nat.lt_succ_self n) false))) t ∧
        C.comp (C.base (shapeFunctor.map
          (OAI.Grothendieck.Shape.face (Nat.lt_succ_self n) true))) s =
        C.comp (C.base (shapeFunctor.map
          (OAI.Grothendieck.Shape.face (Nat.lt_succ_self n) true))) t ↔
      C.comp (C.base (Grothendieck.Shape.face (Nat.lt_succ_self n) false)) s =
        C.comp (C.base (Grothendieck.Shape.face (Nat.lt_succ_self n) false)) t ∧
        C.comp (C.base (Grothendieck.Shape.face (Nat.lt_succ_self n) true)) s =
        C.comp (C.base (Grothendieck.Shape.face (Nat.lt_succ_self n) true)) t
    rw [shapeFunctor_face, shapeFunctor_face]
    exact Iff.rfl

theorem fillers_theoryToOAI {C : Grothendieck.GlobularTheory.{v}} (hC : C.IsCoherator)
    (p : (theoryToOAI C).AdmissiblePair) :
    ∃ z, OAI.Grothendieck.GlobularTheory.Fills
      (OAI.Grothendieck.GlobularTheory.Morphism.id (theoryToOAI C)) p z := by
  obtain ⟨z, hz⟩ := hC.2
    { n := p.n
      arity := shapeOfOAI p.arity
      height := (height_tableOfOAI p.arity.2).trans_le p.height
      source := p.source
      target := p.target
      parallel := (parallel_theoryToOAI_iff p.n p.source p.target).1 p.parallel }
  refine ⟨z, ?_⟩
  change C.comp (C.base (shapeFunctor.map
        (OAI.Grothendieck.Shape.face (Nat.lt_succ_self p.n) false))) z = p.source ∧
      C.comp (C.base (shapeFunctor.map
        (OAI.Grothendieck.Shape.face (Nat.lt_succ_self p.n) true))) z = p.target
  rw [shapeFunctor_face, shapeFunctor_face]
  exact hz

end HomotopyHypothesis.Bridge.Statement
