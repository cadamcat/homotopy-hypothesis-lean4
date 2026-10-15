import HomotopyHypothesis.Blueprint.Defs
noncomputable section

namespace HomotopyHypothesis.FiniteCategory.Subcategory

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open HomotopicalAlgebra
open OAI.Grothendieck
open HomotopyHypothesis.Blueprint
open HomotopyHypothesis.Henry

private def finiteCellGenerators (C : GlobularTheory.{u}) : MorphismProperty C.Model :=
  (MorphismProperty.ofHoms (fun n : ℕ => GlobularTheory.Model.I C n)).pushouts ⊔
    MorphismProperty.isomorphisms C.Model

private theorem finiteCellGenerators_stableUnderCobaseChange (C : GlobularTheory.{u}) :
    (finiteCellGenerators C).IsStableUnderCobaseChange := by
  refine { of_isPushout := ?_ }
  intro A B X Y f g k j hsq hf
  rcases hf with h | h
  · exact Or.inl (MorphismProperty.of_isPushout hsq h)
  · exact Or.inr (MorphismProperty.of_isPushout hsq h)

private theorem finiteCellMaps_stableUnderCobaseChange {C : GlobularTheory.{u}}
    {A B X Y : C.Model} {f : A ⟶ B} {g : A ⟶ X} {k : B ⟶ Y} {j : X ⟶ Y}
    (hsq : IsPushout f g k j) (hf : finiteCellMaps C f) : finiteCellMaps C j := by
  let G := finiteCellGenerators C
  have hGstable := finiteCellGenerators_stableUnderCobaseChange C
  change G.multiplicativeClosure f at hf
  change G.multiplicativeClosure j
  rw [MorphismProperty.multiplicativeClosure_eq_multiplicativeClosure' G] at hf ⊢
  revert X Y g k j hsq
  induction hf with
  | of f hf =>
      intro X Y g k j hsq
      exact MorphismProperty.multiplicativeClosure'.of j
        (hGstable.of_isPushout hsq.flip hf)
  | id A =>
      intro X Y g k j hsq
      haveI : IsIso j := hsq.isIso_inr_of_isIso
      exact MorphismProperty.multiplicativeClosure'.of j
        (Or.inr (MorphismProperty.isomorphisms.infer_property j))
  | of_comp f g hf hg ih =>
      intro X Y s k j hsq
      have hf₁ : G (pushout.inr f s) :=
        hGstable.of_isPushout (IsPushout.of_hasPushout f s).flip hf
      have hg₁ : G.multiplicativeClosure' (pushout.inr g (pushout.inl f s)) :=
        ih (g := pushout.inl f s) (hsq := IsPushout.of_hasPushout g (pushout.inl f s))
      have hcomp : G.multiplicativeClosure'
          (pushout.inr f s ≫ pushout.inr g (pushout.inl f s)) :=
        MorphismProperty.multiplicativeClosure'.of_comp _ _ hf₁ hg₁
      have hIsoG : G (pushoutRightPushoutInlIso f s g).hom :=
        Or.inr (MorphismProperty.isomorphisms.infer_property
          (pushoutRightPushoutInlIso f s g).hom)
      have hStd : G.multiplicativeClosure' (pushout.inr (f ≫ g) s) := by
        have hcomp' : G.multiplicativeClosure
            (pushout.inr f s ≫ pushout.inr g (pushout.inl f s)) := by
          rw [MorphismProperty.multiplicativeClosure_eq_multiplicativeClosure' G]
          exact hcomp
        have hcomp'' : G.multiplicativeClosure
            ((pushout.inr f s ≫ pushout.inr g (pushout.inl f s)) ≫
              (pushoutRightPushoutInlIso f s g).hom) :=
          MorphismProperty.multiplicativeClosure.comp_of _ _ hcomp' hIsoG
        rw [Category.assoc, inr_inr_pushoutRightPushoutInlIso_hom f s g] at hcomp''
        exact MorphismProperty.multiplicativeClosure_eq_multiplicativeClosure' G ▸ hcomp''
      let hsquare : IsPushout (f ≫ g) s (pushout.inl (f ≫ g) s)
          (pushout.inr (f ≫ g) s) := IsPushout.of_hasPushout (f ≫ g) s
      let e₂ := hsq.isoIsPushout _ _ hsquare
      have hArrow : j ≫ e₂.hom = pushout.inr (f ≫ g) s :=
        hsq.inr_isoIsPushout_hom _ _ hsquare
      have hIsoInvG : G e₂.inv :=
        Or.inr (MorphismProperty.isomorphisms.infer_property e₂.inv)
      have hj : G.multiplicativeClosure (j) := by
        have hStd' : G.multiplicativeClosure (pushout.inr (f ≫ g) s) := by
          rw [MorphismProperty.multiplicativeClosure_eq_multiplicativeClosure' G]
          exact hStd
        have h' : G.multiplicativeClosure ((pushout.inr (f ≫ g) s) ≫ e₂.inv) :=
          MorphismProperty.multiplicativeClosure.comp_of _ _ hStd' hIsoInvG
        have heq : pushout.inr (f ≫ g) s ≫ e₂.inv = j := by
          calc
            pushout.inr (f ≫ g) s ≫ e₂.inv = (j ≫ e₂.hom) ≫ e₂.inv := by rw [hArrow]
            _ = j := by simp [Category.assoc]
        rw [heq] at h'
        exact h'
      rw [← MorphismProperty.multiplicativeClosure_eq_multiplicativeClosure' G]
      exact hj

theorem afin_ι_map_isPushout_proof {C : GlobularTheory.{u}} (hC : C.IsCoherator) :
    ∀ ⦃A B X Q : ObjectProperty.FullSubcategory (IsFinitelyCellular C)⦄
      (i : A ⟶ B) (f : A ⟶ X) (k : B ⟶ Q) (j : X ⟶ Q),
      IsPushout i f k j → cofibrations (Afin C hC) i →
      IsPushout ((ObjectProperty.ι (IsFinitelyCellular C)).map i)
        ((ObjectProperty.ι (IsFinitelyCellular C)).map f)
        ((ObjectProperty.ι (IsFinitelyCellular C)).map k)
        ((ObjectProperty.ι (IsFinitelyCellular C)).map j) := by
  intro A B X Q i f k j hsq hi
  let ι : ObjectProperty.FullSubcategory (IsFinitelyCellular C) ⥤ C.Model :=
    ObjectProperty.ι (IsFinitelyCellular C)
  let i₀ := ι.map i
  let f₀ := ι.map f
  let k₀ := ι.map k
  let j₀ := ι.map j
  change IsPushout i₀ f₀ k₀ j₀
  change finiteCellMaps C i₀ at hi
  let P := pushout i₀ f₀
  have hCell : IsFinitelyCellular C P := by
    change finiteCellMaps C (initial.to P)
    have hX : finiteCellMaps C (initial.to X.obj) := X.property
    have hAttach : finiteCellMaps C (pushout.inr i₀ f₀) :=
      finiteCellMaps_stableUnderCobaseChange (IsPushout.of_hasPushout i₀ f₀) hi
    have hmul : (finiteCellGenerators C).multiplicativeClosure.IsMultiplicative := inferInstance
    change (finiteCellGenerators C).multiplicativeClosure (initial.to X.obj) at hX
    change (finiteCellGenerators C).multiplicativeClosure (pushout.inr i₀ f₀) at hAttach
    have hComp : (finiteCellGenerators C).multiplicativeClosure
        (initial.to X.obj ≫ pushout.inr i₀ f₀) :=
      hmul.toIsStableUnderComposition.comp_mem _ _ hX hAttach
    have hInitialEq : initial.to P = initial.to X.obj ≫ pushout.inr i₀ f₀ :=
      initialIsInitial.hom_ext _ _
    rw [hInitialEq]
    exact hComp
  let P₀ : ObjectProperty.FullSubcategory (IsFinitelyCellular C) := ⟨P, hCell⟩
  let pInl : B ⟶ P₀ := ObjectProperty.homMk (pushout.inl i₀ f₀)
  let pInr : X ⟶ P₀ := ObjectProperty.homMk (pushout.inr i₀ f₀)
  have hCompat : i ≫ pInl = f ≫ pInr := by
    apply ObjectProperty.hom_ext
    exact pushout.condition
  let qSub : Q ⟶ P₀ := hsq.desc pInl pInr hCompat
  have hCompat0 : i₀ ≫ k₀ = f₀ ≫ j₀ := by
    simpa only [i₀, f₀, k₀, j₀, Functor.map_comp] using
      congrArg ι.map hsq.w
  let pMap : P ⟶ Q.obj := pushout.desc k₀ j₀ hCompat0
  let pSub : P₀ ⟶ Q := ObjectProperty.homMk pMap
  have hk₀ : k₀ = k.hom := by
    change ι.map k = k.hom
    exact ObjectProperty.ι_map (P := IsFinitelyCellular C)
  have hj₀ : j₀ = j.hom := by
    change ι.map j = j.hom
    exact ObjectProperty.ι_map (P := IsFinitelyCellular C)
  have hpInl : pushout.inl i₀ f₀ ≫ pMap = k.hom := by
    change pushout.inl i₀ f₀ ≫ pushout.desc k₀ j₀ hCompat0 = k₀
    simpa only [hk₀] using pushout.inl_desc k₀ j₀ hCompat0
  have hpInr : pushout.inr i₀ f₀ ≫ pMap = j.hom := by
    change pushout.inr i₀ f₀ ≫ pushout.desc k₀ j₀ hCompat0 = j₀
    simpa only [hj₀] using pushout.inr_desc k₀ j₀ hCompat0
  have hqInl : k.hom ≫ qSub.hom = pInl.hom :=
    by
      change ι.map k ≫ ι.map qSub = ι.map pInl
      exact congrArg ι.map (hsq.inl_desc pInl pInr hCompat)
  have hqInr : j.hom ≫ qSub.hom = pInr.hom :=
    by
      change ι.map j ≫ ι.map qSub = ι.map pInr
      exact congrArg ι.map (hsq.inr_desc pInl pInr hCompat)
  have hPQ : pMap ≫ qSub.hom = 𝟙 P := by
    apply (IsPushout.of_hasPushout i₀ f₀).hom_ext
    · calc
        pushout.inl i₀ f₀ ≫ (pMap ≫ qSub.hom) =
            (pushout.inl i₀ f₀ ≫ pMap) ≫ qSub.hom :=
              (Category.assoc _ _ _).symm
        _ = k.hom ≫ qSub.hom := congrArg (fun a => a ≫ qSub.hom) hpInl
        _ = pInl.hom := hqInl
        _ = pushout.inl i₀ f₀ := rfl
        _ = pushout.inl i₀ f₀ ≫ 𝟙 P := (Category.comp_id _).symm
    · calc
        pushout.inr i₀ f₀ ≫ (pMap ≫ qSub.hom) =
            (pushout.inr i₀ f₀ ≫ pMap) ≫ qSub.hom :=
              (Category.assoc _ _ _).symm
        _ = j.hom ≫ qSub.hom := congrArg (fun a => a ≫ qSub.hom) hpInr
        _ = pInr.hom := hqInr
        _ = pushout.inr i₀ f₀ := rfl
        _ = pushout.inr i₀ f₀ ≫ 𝟙 P := (Category.comp_id _).symm
  have hpSubInl : pInl ≫ pSub = k := by
    apply ObjectProperty.hom_ext
    exact hpInl
  have hpSubInr : pInr ≫ pSub = j := by
    apply ObjectProperty.hom_ext
    exact hpInr
  have hQPSub : qSub ≫ pSub = 𝟙 Q := by
    apply hsq.hom_ext
    · calc
        k ≫ qSub ≫ pSub = (k ≫ qSub) ≫ pSub := (Category.assoc _ _ _).symm
        _ = pInl ≫ pSub := by rw [hsq.inl_desc pInl pInr hCompat]
        _ = k := hpSubInl
        _ = k ≫ 𝟙 Q := by simp
    · calc
        j ≫ qSub ≫ pSub = (j ≫ qSub) ≫ pSub := (Category.assoc _ _ _).symm
        _ = pInr ≫ pSub := by rw [hsq.inr_desc pInl pInr hCompat]
        _ = j := hpSubInr
        _ = j ≫ 𝟙 Q := by simp
  have hQP : qSub.hom ≫ pMap = 𝟙 Q.obj := by
    exact congrArg (fun r => r.hom) hQPSub
  let e : P ≅ Q.obj := ⟨pMap, qSub.hom, hPQ, hQP⟩
  have hStd : IsPushout i₀ f₀ (pushout.inl i₀ f₀) (pushout.inr i₀ f₀) :=
    IsPushout.of_hasPushout i₀ f₀
  refine hStd.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e ?_ ?_ ?_ ?_
  · simp [i₀]
  · simp [f₀]
  · simpa [e, ι, hk₀] using hpInl
  · simpa [e, ι, hj₀] using hpInr

#print axioms afin_ι_map_isPushout_proof

end HomotopyHypothesis.FiniteCategory.Subcategory
