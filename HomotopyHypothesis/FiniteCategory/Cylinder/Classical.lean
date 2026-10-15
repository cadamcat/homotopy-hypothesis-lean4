import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Topology.UnitInterval
import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.HomotopyEquivalenceOfIsPushout
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.RelativeLiftOfHomotopyEquivalence
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Blueprint.Henry.Topology
universe u

open CategoryTheory Limits HomotopicalAlgebra TopCat CartesianMonoidalCategory
open scoped MonoidalCategory

namespace HomotopyHypothesis.FiniteCategory.Cylinder

open HomotopyHypothesis.Henry

lemma homotopyEquivalences_comp {X Y Z : TopCat.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : Top.homotopyEquivalences f) (hg : Top.homotopyEquivalences g) :
    Top.homotopyEquivalences (f ≫ g) := by
  rcases hf with ⟨f', hf₀, hf₁⟩
  rcases hg with ⟨g', hg₀, hg₁⟩
  refine ⟨g' ≫ f', ?_, ?_⟩
  · have hmid : ((f ≫ (g ≫ g')) ≫ f').hom.Homotopic ((f ≫ (𝟙 Y)) ≫ f').hom := by
      have h₁ := hg₀.comp (ContinuousMap.Homotopic.refl f.hom)
      have h₂ := (ContinuousMap.Homotopic.refl f'.hom).comp h₁
      simpa using h₂
    exact hmid.trans (by simpa using hf₀)
  · have hmid : ((g' ≫ (f' ≫ f)) ≫ g).hom.Homotopic ((g' ≫ (𝟙 Y)) ≫ g).hom := by
      have h₁ := hf₁.comp (ContinuousMap.Homotopic.refl g'.hom)
      have h₂ := (ContinuousMap.Homotopic.refl g.hom).comp h₁
      simpa using h₂
    exact hmid.trans (by simpa using hg₁)

lemma homotopyEquivalences_twoOutOfSix :
    TwoOutOfSix TopCat.{u} Top.homotopyEquivalences := by
  intro X Y Z T f g h hfg hgh
  rcases hfg with ⟨u, hfg₀, hfg₁⟩
  rcases hgh with ⟨v, hgh₀, hgh₁⟩
  have huv : (h ≫ v).hom.Homotopic (u ≫ f).hom := by
    have h₁ : ((u ≫ f ≫ g) ≫ h ≫ v).hom.Homotopic (h ≫ v).hom := by
      have hfg' : ((u ≫ f ≫ g).hom).Homotopic ((𝟙 Z : Z ⟶ Z).hom) := by
        simpa [Category.assoc] using hfg₁
      have hcomp := (ContinuousMap.Homotopic.refl (h ≫ v).hom).comp hfg'
      simpa [Category.assoc] using hcomp
    have h₂ : ((u ≫ f ≫ g) ≫ h ≫ v).hom.Homotopic (u ≫ f).hom := by
      have hcomp := hgh₀.comp (ContinuousMap.Homotopic.refl (u ≫ f).hom)
      simpa [Category.assoc] using hcomp
    exact h₁.symm.trans h₂
  have hg₀ : (g ≫ (u ≫ f)).hom.Homotopic ((𝟙 Y : Y ⟶ Y).hom) := by
    have hcomp := huv.comp (ContinuousMap.Homotopic.refl g.hom)
    exact hcomp.symm.trans (by simpa [Category.assoc] using hgh₀)
  have hg₁ : ((u ≫ f) ≫ g).hom.Homotopic ((𝟙 Z : Z ⟶ Z).hom) := by
    simpa [Category.assoc] using hfg₁
  have hf₀ : (f ≫ (g ≫ u)).hom.Homotopic ((𝟙 X : X ⟶ X).hom) := by
    simpa [Category.assoc] using hfg₀
  have hf₁ : ((g ≫ u) ≫ f).hom.Homotopic ((𝟙 Y : Y ⟶ Y).hom) := by
    simpa [Category.assoc] using hg₀
  have hh₀ : (h ≫ (v ≫ g)).hom.Homotopic ((𝟙 Z : Z ⟶ Z).hom) := by
    have hcomp := (ContinuousMap.Homotopic.refl g.hom).comp huv
    exact hcomp.trans (by simpa [Category.assoc] using hfg₁)
  have hh₁ : ((v ≫ g) ≫ h).hom.Homotopic ((𝟙 T : T ⟶ T).hom) := by
    simpa [Category.assoc] using hgh₁
  refine ⟨⟨g ≫ u, hf₀, hf₁⟩, ⟨u ≫ f, hg₀, hg₁⟩, ⟨v ≫ g, hh₀, hh₁⟩, ?_⟩
  exact homotopyEquivalences_comp (f := f ≫ g) (g := h)
    (homotopyEquivalences_comp (f := f) (g := g)
      ⟨g ≫ u, hf₀, hf₁⟩ ⟨u ≫ f, hg₀, hg₁⟩)
    ⟨v ≫ g, hh₀, hh₁⟩

lemma homotopyEquivalences_id (X : TopCat.{u}) :
    Top.homotopyEquivalences (𝟙 X) := by
  refine ⟨𝟙 X, ?_, ?_⟩ <;>
    simpa using ContinuousMap.Homotopic.refl ((𝟙 X : X ⟶ X).hom)

instance : (Top.homotopyEquivalences : MorphismProperty TopCat.{u}).IsMultiplicative where
  id_mem := homotopyEquivalences_id
  comp_mem := fun _ _ hf hg ↦ homotopyEquivalences_comp hf hg

lemma homotopyEquivalences_of_isIso {X Y : TopCat.{u}} (f : X ⟶ Y) [IsIso f] :
    Top.homotopyEquivalences f := by
  refine ⟨inv f, ?_, ?_⟩
  · simpa using ContinuousMap.Homotopic.refl ((𝟙 X : X ⟶ X).hom)
  · simpa using ContinuousMap.Homotopic.refl ((𝟙 Y : Y ⟶ Y).hom)

lemma cellBoundaryPushouts_le_relativeFiniteCellComplexes :
    Top.cellBoundaries.pushouts ≤ Top.relativeFiniteCellComplexes := by
  intro X Y f hf
  change ((Top.cellBoundaries.pushouts ⊔ MorphismProperty.isomorphisms TopCat).multiplicativeClosure) f
  exact .of f (Or.inl hf)

lemma isomorphisms_le_relativeFiniteCellComplexes :
    MorphismProperty.isomorphisms TopCat.{u} ≤ Top.relativeFiniteCellComplexes := by
  intro X Y f hf
  change ((Top.cellBoundaries.pushouts ⊔ MorphismProperty.isomorphisms TopCat).multiplicativeClosure) f
  exact .of f (Or.inr hf)

lemma respectsIso_of_isomorphisms_le {C : Type*} [Category C] (P : MorphismProperty C)
    [P.IsMultiplicative] (hIso : MorphismProperty.isomorphisms C ≤ P) : P.RespectsIso := by
  apply MorphismProperty.RespectsIso.mk P
  · intro X Y Z e f hf
    exact P.comp_mem e.hom f (hIso e.hom (by infer_instance)) hf
  · intro X Y Z e f hf
    exact P.comp_mem f e.hom hf (hIso e.hom (by infer_instance))

lemma multiplicativeClosure_stableUnderCobaseChange {C : Type*} [Category C]
    (P : MorphismProperty C) [P.IsStableUnderCobaseChange] [HasPushouts C]
    (hIso : MorphismProperty.isomorphisms C ≤ P) :
    P.multiplicativeClosure.IsStableUnderCobaseChange := by
  let Q := P.multiplicativeClosure
  haveI : Q.IsMultiplicative := inferInstance
  have hIsoQ : MorphismProperty.isomorphisms C ≤ Q := fun X Y f hf => .of f (hIso f hf)
  haveI : Q.RespectsIso := respectsIso_of_isomorphisms_le Q hIsoQ
  refine MorphismProperty.IsStableUnderCobaseChange.mk' (P := Q) ?_
  intro A B A' f g _ hf
  change Q f at hf
  revert B g
  induction hf with
  | of f hf =>
      intro B g hpush
      exact .of (pushout.inr f g) <| by
        exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout
          (IsPushout.of_hasPushout f g).flip hf
  | id A =>
      intro B g hpush
      have hs := IsPushout.of_hasPushout (𝟙 A) g
      have hi : IsIso (pushout.inr (𝟙 A) g) := hs.isIso_inr_of_isIso
      exact hIsoQ _ (by simpa using hi)
  | comp_of f₁ f₂ hf₁ hf₂ ih =>
      intro B g hpush
      let j₁ := pushout.inr f₁ g
      let j₂ := pushout.inr f₂ (pushout.inl f₁ g)
      have hj₁ : Q j₁ := ih B g
      have hj₂ : Q j₂ := .of j₂ <| by
        exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout
          (IsPushout.of_hasPushout f₂ (pushout.inl f₁ g)).flip hf₂
      have hj : Q (j₁ ≫ j₂) := Q.comp_mem j₁ j₂ hj₁ hj₂
      have hs₁ : IsPushout f₁ g (pushout.inl f₁ g) j₁ := IsPushout.of_hasPushout f₁ g
      have hs₂ : IsPushout f₂ (pushout.inl f₁ g)
          (pushout.inl f₂ (pushout.inl f₁ g)) j₂ :=
        IsPushout.of_hasPushout f₂ (pushout.inl f₁ g)
      have hs := hs₁.paste_horiz hs₂
      rw [← hs.inr_isoPushout_hom]
      exact MorphismProperty.RespectsIso.postcomp Q hs.isoPushout.hom (j₁ ≫ j₂) hj

lemma relativeFiniteCellComplexes_isStableUnderCobaseChange :
    Top.relativeFiniteCellComplexes.{u}.IsStableUnderCobaseChange := by
  let S := Top.cellBoundaries.{u}.pushouts ⊔ MorphismProperty.isomorphisms TopCat.{u}
  haveI : S.IsStableUnderCobaseChange := by
    constructor
    intro A A' B B' f g f' g' sq hf
    rcases hf with hf | hf
    · exact Or.inl (MorphismProperty.IsStableUnderCobaseChange.of_isPushout sq hf)
    · exact Or.inr (MorphismProperty.IsStableUnderCobaseChange.of_isPushout sq hf)
  have hIso : MorphismProperty.isomorphisms TopCat.{u} ≤ S := fun _ _ f hf => Or.inr hf
  have hS := multiplicativeClosure_stableUnderCobaseChange S hIso
  simpa [Top.relativeFiniteCellComplexes, S] using hS

lemma finiteCell_pushout_obj {A B X P : TopCat.{u}} (i : A ⟶ B) (f : A ⟶ X)
    (k : B ⟶ P) (j : X ⟶ P) (hsq : IsPushout i f k j)
    (hi : Top.relativeFiniteCellComplexes i) (hX : Top.IsFiniteCellComplex X) :
    Top.IsFiniteCellComplex P := by
  letI : Top.relativeFiniteCellComplexes.{u}.IsStableUnderCobaseChange :=
    relativeFiniteCellComplexes_isStableUnderCobaseChange
  have hj : Top.relativeFiniteCellComplexes j :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout hsq.flip hi
  have hm : Top.relativeFiniteCellComplexes.{u}.IsMultiplicative := by
    change ((Top.cellBoundaries.{u}.pushouts ⊔
      MorphismProperty.isomorphisms TopCat.{u}).multiplicativeClosure).IsMultiplicative
    infer_instance
  change Top.relativeFiniteCellComplexes (initial.to P)
  change Top.relativeFiniteCellComplexes (initial.to X) at hX
  have hEq : initial.to P = initial.to X ≫ j := initialIsInitial.hom_ext _ _
  rw [hEq]
  exact hm.comp_mem (initial.to X) j hX hj

noncomputable def finCell_createsPushout {A B X : FinCell.{u}} (i : A ⟶ B) (f : A ⟶ X)
    (hi : cofibrations FinCell.{u} i) :
    CreatesColimit (span i f) (ObjectProperty.ι Top.IsFiniteCellComplex.{u}) := by
  let J : FinCell.{u} ⥤ TopCat.{u} := ObjectProperty.ι _
  let F : WalkingSpan ⥤ FinCell.{u} := span i f
  let i' := J.map i
  let f' := J.map f
  haveI : HasPushout i' f' := inferInstance
  have hP : Top.IsFiniteCellComplex (pushout i' f') :=
    finiteCell_pushout_obj i' f' (pushout.inl i' f') (pushout.inr i' f')
      (IsPushout.of_hasPushout i' f') hi X.property
  let α := spanCompIso J i f
  let cTop : Cocone (span i' f') := colimit.cocone (span i' f')
  let c : Cocone (F ⋙ J) := (Cocone.precompose α.hom).obj cTop
  have hcolTop : IsColimit cTop := colimit.isColimit (span i' f')
  have hw : (Cocone.precompose α.inv).obj c ≅ cTop := by
    refine Cocone.ext (Iso.refl _) ?_
    intro j
    simp [c, Cocone.precompose]
  have hcol : IsColimit c :=
    (IsColimit.equivOfNatIsoOfIso α c cTop hw).symm hcolTop
  exact Limits.createsColimitFullSubcategoryInclusion' F (c := c) hcol hP

lemma finCell_hasPushout {A B X : FinCell.{u}} (i : A ⟶ B) (f : A ⟶ X)
    (hi : cofibrations FinCell.{u} i) : HasPushout i f := by
  let J : FinCell.{u} ⥤ TopCat.{u} := ObjectProperty.ι _
  letI : CreatesColimit (span i f) J := finCell_createsPushout i f hi
  exact HasPushout.of_createsColimit J i f

noncomputable def finCell_createsPushout_symm {A B X : FinCell.{u}} (i : A ⟶ B)
    (f : A ⟶ X) (hi : cofibrations FinCell.{u} i) :
    CreatesColimit (span f i) (ObjectProperty.ι Top.IsFiniteCellComplex.{u}) := by
  let J : FinCell.{u} ⥤ TopCat.{u} := ObjectProperty.ι _
  let F : WalkingSpan ⥤ FinCell.{u} := span f i
  let i' := J.map i
  let f' := J.map f
  haveI : HasPushout f' i' := inferInstance
  have hsq : IsPushout i' f' (pushout.inr f' i') (pushout.inl f' i') :=
    (IsPushout.of_hasPushout f' i').flip
  have hP : Top.IsFiniteCellComplex (pushout f' i') :=
    finiteCell_pushout_obj i' f' (pushout.inr f' i') (pushout.inl f' i') hsq hi X.property
  let α := spanCompIso J f i
  let cTop : Cocone (span f' i') := colimit.cocone (span f' i')
  let c : Cocone (F ⋙ J) := (Cocone.precompose α.hom).obj cTop
  have hcolTop : IsColimit cTop := colimit.isColimit (span f' i')
  have hw : (Cocone.precompose α.inv).obj c ≅ cTop := by
    refine Cocone.ext (Iso.refl _) ?_
    intro j
    simp [c, Cocone.precompose]
  have hcol : IsColimit c :=
    (IsColimit.equivOfNatIsoOfIso α c cTop hw).symm hcolTop
  exact Limits.createsColimitFullSubcategoryInclusion' F (c := c) hcol hP

lemma finCell_isCofibrationCategory : IsCofibrationCategory FinCell.{u} := by
  let J : FinCell.{u} ⥤ TopCat.{u} := ObjectProperty.ι _
  letI : Top.relativeFiniteCellComplexes.{u}.IsMultiplicative := by
    change ((Top.cellBoundaries.{u}.pushouts ⊔
      MorphismProperty.isomorphisms TopCat.{u}).multiplicativeClosure).IsMultiplicative
    infer_instance
  let ITop : TopCat.{u} := ⊥_ TopCat.{u}
  have hInitTop : IsInitial ITop := initialIsInitial
  have hInitFin : Top.IsFiniteCellComplex ITop := by
    change Top.relativeFiniteCellComplexes (initial.to ITop)
    have heq : initial.to ITop = 𝟙 ITop := initialIsInitial.hom_ext _ _
    rw [heq]
    have hi : IsIso (𝟙 ITop) := by infer_instance
    exact isomorphisms_le_relativeFiniteCellComplexes _
      (MorphismProperty.isomorphisms.iff (𝟙 ITop) |>.2 hi)
  let I₀ : FinCell.{u} := ⟨ITop, hInitFin⟩
  have hInitFinSub : IsInitial I₀ := by
    refine IsInitial.ofUniqueHom (fun X => ObjectProperty.homMk
      (initial.to X.obj)) ?_
    intro X f
    apply ObjectProperty.hom_ext
    exact initialIsInitial.hom_ext _ _
  refine {
    isomorphisms_le := ?_
    isMultiplicative := ?_
    exists_initial := ⟨I₀, ⟨hInitFinSub⟩⟩
    initial_cofibration := ?_
    hasPushout := finCell_hasPushout
    isStableUnderCobaseChange := ?_ }
  · intro A B f hf
    change Top.relativeFiniteCellComplexes (J.map f)
    exact isomorphisms_le_relativeFiniteCellComplexes _ (by
      simpa using (inferInstance : IsIso (J.map f)))
  · change (Top.relativeFiniteCellComplexes.inverseImage J).IsMultiplicative
    infer_instance
  · intro I hI X
    change Top.relativeFiniteCellComplexes (J.map (hI.to X))
    letI : Top.relativeFiniteCellComplexes.{u}.RespectsIso :=
      respectsIso_of_isomorphisms_le _ isomorphisms_le_relativeFiniteCellComplexes
    have hIso : IsIso (J.map (hI.to I₀)) := by
      haveI : IsIso (hI.to I₀) := by
        let e := hI.uniqueUpToIso hInitFinSub
        change IsIso e.hom
        infer_instance
      infer_instance
    have hComp : hI.to X = hI.to I₀ ≫ hInitFinSub.to X := hI.hom_ext _ _
    have hbase : Top.relativeFiniteCellComplexes (J.map (hInitFinSub.to X)) := by
      have hCanon : J.map (hInitFinSub.to X) = initial.to X.obj :=
        initialIsInitial.hom_ext _ _
      rw [hCanon]
      exact X.property
    have hrel : Top.relativeFiniteCellComplexes
        (J.map (hI.to I₀) ≫ J.map (hInitFinSub.to X)) :=
      MorphismProperty.RespectsIso.precomp _ _ _ hbase
    have hmapComp : J.map (hI.to X) =
        J.map (hI.to I₀) ≫ J.map (hInitFinSub.to X) := by
      rw [← Functor.map_comp, hComp]
    rw [hmapComp]
    exact hrel
  · letI : Top.relativeFiniteCellComplexes.{u}.IsStableUnderCobaseChange :=
      relativeFiniteCellComplexes_isStableUnderCobaseChange
    constructor
    intro A A' B B' i f k j hsq hi
    letI : CreatesColimit (span f i) J := finCell_createsPushout_symm i f hi
    have hsqTop : IsPushout (J.map f) (J.map i) (J.map k) (J.map j) :=
      Functor.map_isPushout J hsq
    change Top.relativeFiniteCellComplexes (J.map i) at hi
    change Top.relativeFiniteCellComplexes (J.map k)
    exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout hsqTop hi

lemma finCell_trivialCofibration_cobaseChange {A B X P : FinCell.{u}}
    (i : A ⟶ B) (f : A ⟶ X) (k : B ⟶ P) (j : X ⟶ P)
    (hsq : IsPushout i f k j) (hi : cofibrations FinCell.{u} i)
    (hwi : weakEquivalences FinCell.{u} i) : weakEquivalences FinCell.{u} j := by
  let J : FinCell.{u} ⥤ TopCat.{u} := ObjectProperty.ι _
  letI : CreatesColimit (span i f) J := finCell_createsPushout i f hi
  have hsqTop : IsPushout (J.map i) (J.map f) (J.map k) (J.map j) :=
    Functor.map_isPushout J hsq
  have hiTop : Top.relativeFiniteCellComplexes (J.map i) := hi
  have hwiTop : Top.homotopyEquivalences (J.map i) := hwi
  have hidA : Top.homotopyEquivalences (𝟙 A.obj) := homotopyEquivalences_id _
  have hidX : Top.homotopyEquivalences (𝟙 X.obj) := homotopyEquivalences_id _
  have htriv : IsPushout (𝟙 A.obj) (J.map f) (J.map f) (𝟙 X.obj) := by
    letI : IsIso (𝟙 A.obj) := inferInstance
    letI : IsIso (𝟙 X.obj) := inferInstance
    exact IsPushout.of_horiz_isIso (show CommSq (𝟙 A.obj) (J.map f) (J.map f) (𝟙 X.obj) from
      ⟨(Category.comp_id (J.map f)).symm⟩)
  have hjTop : Top.homotopyEquivalences (J.map j) := by
    exact HomotopyHypothesis.Henry.Packages.homotopyEquivalence_of_isPushout
      (i := 𝟙 A.obj) (f := J.map f) (k := J.map f) (j := 𝟙 X.obj)
      (i' := J.map i) (f' := J.map f) (k' := J.map k) (j' := J.map j)
      (vA := 𝟙 A.obj) (vB := J.map i) (vC := 𝟙 X.obj) (φ := J.map j)
      htriv hsqTop
      (isomorphisms_le_relativeFiniteCellComplexes (𝟙 A.obj) (by infer_instance)) hiTop
      hidA hwiTop hidX rfl
      ((Category.comp_id (J.map f)).trans (Category.id_comp (J.map f)).symm)
      hsqTop.w.symm rfl
  exact hjTop

lemma finCell_trivialCofibration_retraction {A B : FinCell.{u}} (i : A ⟶ B)
    (hi : cofibrations FinCell.{u} i) (hwi : weakEquivalences FinCell.{u} i) :
    ∃ r : B ⟶ A, i ≫ r = 𝟙 A := by
  let J : FinCell.{u} ⥤ TopCat.{u} := ObjectProperty.ι _
  have hiTop : Top.relativeFiniteCellComplexes (J.map i) := hi
  have hwiTop : Top.homotopyEquivalences (J.map i) := hwi
  obtain ⟨r, hr, _⟩ :=
    (HomotopyHypothesis.Henry.Packages.relativeLift_of_homotopyEquivalence
      (J.map i) hiTop (J.map i) hwiTop).1 (𝟙 A.obj) (𝟙 B.obj)
      ((Category.id_comp (J.map i)).trans (Category.comp_id (J.map i)).symm)
  refine ⟨ObjectProperty.homMk r, ?_⟩
  apply ObjectProperty.hom_ext
  exact hr

noncomputable def finCell_topImage_initial {I : FinCell.{u}} (hI : IsInitial I) :
    IsInitial ((ObjectProperty.ι Top.IsFiniteCellComplex.{u}).obj I) := by
  let J : FinCell.{u} ⥤ TopCat.{u} := ObjectProperty.ι _
  have hEmpty : Top.IsFiniteCellComplex (⊥_ TopCat.{u}) := by
    change Top.relativeFiniteCellComplexes (initial.to (⊥_ TopCat.{u}))
    have heq : initial.to (⊥_ TopCat.{u}) = 𝟙 (⊥_ TopCat.{u}) :=
      initialIsInitial.hom_ext _ _
    rw [heq]
    exact isomorphisms_le_relativeFiniteCellComplexes _
      (MorphismProperty.isomorphisms.iff _ |>.2 (by infer_instance))
  let I₀ : FinCell.{u} := ⟨⊥_ TopCat.{u}, hEmpty⟩
  have hI₀ : IsInitial I₀ := by
    refine IsInitial.ofUniqueHom (fun X => ObjectProperty.homMk (initial.to X.obj)) ?_
    intro X f
    apply ObjectProperty.hom_ext
    exact initialIsInitial.hom_ext _ _
  let e : I ≅ I₀ := hI.uniqueUpToIso hI₀
  have eTop : J.obj I ≅ J.obj I₀ := J.mapIso e
  have hI₀Top : IsInitial (J.obj I₀) := by
    change IsInitial (⊥_ TopCat.{u})
    exact initialIsInitial
  exact hI₀Top.ofIso eTop.symm

noncomputable def topTensorProdIso (X Y : TopCat.{u}) : X ⊗ Y ≅ X ⨯ Y := by
  let η : X ⊗ Y ⟶ X ⨯ Y := Limits.prod.lift (fst X Y) (snd X Y)
  let ε : X ⨯ Y ⟶ X ⊗ Y := CartesianMonoidalCategory.lift Limits.prod.fst Limits.prod.snd
  have hηε : η ≫ ε = 𝟙 (X ⊗ Y) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [η, ε]
  have hεη : ε ≫ η = 𝟙 (X ⨯ Y) := by
    apply Limits.prod.hom_ext <;> simp [η, ε]
  exact ⟨η, ε, hηε, hεη⟩

noncomputable def topTensorIProductIso (X : TopCat.{u}) :
    X ⊗ TopCat.I.{u} ≅ TopCat.of (X × TopCat.I.{u}) :=
  topTensorProdIso X TopCat.I.{u} ≪≫ TopCat.prodIsoProd X TopCat.I.{u}

lemma topTensorIotaZero_toProduct {X : TopCat.{u}} :
    TopCat.ι₀ ≫ (topTensorIProductIso X).hom =
      TopCat.ofHom ⟨fun x => (x, (0 : TopCat.I.{u})),
        Continuous.prodMk continuous_id continuous_const⟩ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change (TopCat.prodIsoProd X TopCat.I.{u}).hom
      ((topTensorProdIso X TopCat.I.{u}).hom (TopCat.ι₀ x)) = (x, 0)
  rw [TopCat.prodIsoProd_hom_apply]
  apply Prod.ext
  · change ((topTensorProdIso X TopCat.I.{u}).hom ≫ Limits.prod.fst) (TopCat.ι₀ x) = x
    simp [topTensorProdIso, TopCat.ι₀_fst] <;> rfl
  · change ((topTensorProdIso X TopCat.I.{u}).hom ≫ Limits.prod.snd) (TopCat.ι₀ x) = 0
    simp [topTensorProdIso, TopCat.ι₀_snd] <;> rfl

lemma topTensorIotaOne_toProduct {X : TopCat.{u}} :
    TopCat.ι₁ ≫ (topTensorIProductIso X).hom =
      TopCat.ofHom ⟨fun x => (x, (1 : TopCat.I.{u})),
        Continuous.prodMk continuous_id continuous_const⟩ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change (TopCat.prodIsoProd X TopCat.I.{u}).hom
      ((topTensorProdIso X TopCat.I.{u}).hom (TopCat.ι₁ x)) = (x, 1)
  rw [TopCat.prodIsoProd_hom_apply]
  apply Prod.ext
  · change ((topTensorProdIso X TopCat.I.{u}).hom ≫ Limits.prod.fst) (TopCat.ι₁ x) = x
    simp [topTensorProdIso, TopCat.ι₁_fst] <;> rfl
  · change ((topTensorProdIso X TopCat.I.{u}).hom ≫ Limits.prod.snd) (TopCat.ι₁ x) = 1
    simp [topTensorProdIso, TopCat.ι₁_snd] <;> rfl

lemma topTensorIotaZero_fromProduct {X : TopCat.{u}} :
    TopCat.ofHom ⟨fun x => (x, (0 : TopCat.I.{u})),
      Continuous.prodMk continuous_id continuous_const⟩ ≫
      (topTensorIProductIso X).inv = TopCat.ι₀ := by
  rw [← topTensorIotaZero_toProduct]
  simp [Category.assoc]

lemma topTensorIotaOne_fromProduct {X : TopCat.{u}} :
    TopCat.ofHom ⟨fun x => (x, (1 : TopCat.I.{u})),
      Continuous.prodMk continuous_id continuous_const⟩ ≫
      (topTensorIProductIso X).inv = TopCat.ι₁ := by
  rw [← topTensorIotaOne_toProduct]
  simp [Category.assoc]

noncomputable def prismCoordinateEquiv (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin n) × ℝ :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).trans
    ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n))).prodCongr
      ((EuclideanSpace.equiv (Fin 1) ℝ).trans
        (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)))

noncomputable def prismProductSet (n : ℕ) :
    Set (EuclideanSpace ℝ (Fin n) × ℝ) :=
  Metric.closedBall 0 1 ×ˢ Set.Icc (-1 : ℝ) 1

noncomputable def prismBodySet (n : ℕ) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  (prismCoordinateEquiv n).symm.toLinearEquiv.toLinearMap '' prismProductSet n

lemma prismProductSet_frontier (n : ℕ) :
    frontier (prismProductSet n) =
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ×ˢ ({-1, 1} : Set ℝ)) ∪
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ×ˢ Set.Icc (-1 : ℝ) 1) := by
  rw [prismProductSet, frontier_prod_eq]
  simp [frontier_closedBall (0 : EuclideanSpace ℝ (Fin n)) (by norm_num : (1 : ℝ) ≠ 0),
    frontier_Icc (show (-1 : ℝ) ≤ 1 by norm_num)]

lemma prismBodySet_convex (n : ℕ) : Convex ℝ (prismBodySet n) := by
  unfold prismBodySet prismProductSet
  exact (convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).prod (convex_Icc (-1 : ℝ) 1)
    |>.linear_image (prismCoordinateEquiv n).symm.toLinearMap

lemma prismBodySet_interior_nonempty (n : ℕ) :
    (interior (prismBodySet n)).Nonempty := by
  let q : (EuclideanSpace ℝ (Fin n) × ℝ) ≃ₜ EuclideanSpace ℝ (Fin (n + 1)) :=
    (prismCoordinateEquiv n).symm.toHomeomorph
  have h0 : (0, 0) ∈ interior (prismProductSet n) := by
    rw [prismProductSet, interior_prod_eq]
    constructor
    · rw [interior_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)]
      exact Metric.mem_ball_self (by norm_num)
    · rw [interior_Icc]
      norm_num
  have himage : q '' interior (prismProductSet n) = interior (prismBodySet n) := by
    rw [prismBodySet]
    exact q.image_interior _
  rw [← himage]
  exact ⟨q (0, 0), ⟨(0, 0), h0, rfl⟩⟩

lemma prismBodySet_isBounded (n : ℕ) : Bornology.IsBounded (prismBodySet n) := by
  unfold prismBodySet prismProductSet
  exact (prismCoordinateEquiv n).symm.lipschitzWith.isBounded_image
    (Metric.isBounded_closedBall.prod (Metric.isBounded_Icc (-1 : ℝ) 1))

lemma prismBodySet_isClosed (n : ℕ) : IsClosed (prismBodySet n) := by
  let q : (EuclideanSpace ℝ (Fin n) × ℝ) ≃ₜ EuclideanSpace ℝ (Fin (n + 1)) :=
    (prismCoordinateEquiv n).symm.toHomeomorph
  have hc : IsCompact (prismProductSet n) := by
    unfold prismProductSet
    exact (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).prod isCompact_Icc
  rw [prismBodySet]
  exact hc.image q.continuous |>.isClosed

lemma exists_prismBodySet_homeomorph (n : ℕ) :
    ∃ h : EuclideanSpace ℝ (Fin (n + 1)) ≃ₜ EuclideanSpace ℝ (Fin (n + 1)),
      h '' prismBodySet n = Metric.closedBall 0 1 ∧
      h '' frontier (prismBodySet n) = Metric.sphere 0 1 := by
  obtain ⟨h, _, hc, hf⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (prismBodySet_convex n) (prismBodySet_interior_nonempty n) (prismBodySet_isBounded n)
  have hclosure : closure (prismBodySet n) = prismBodySet n :=
    (prismBodySet_isClosed n).closure_eq
  exact ⟨h, by simpa [hclosure] using hc, hf⟩

noncomputable def prismBodyHomeomorph (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 1)) ≃ₜ EuclideanSpace ℝ (Fin (n + 1)) :=
  Classical.choose (exists_prismBodySet_homeomorph n)

lemma prismBodyHomeomorph_image (n : ℕ) :
    prismBodyHomeomorph n '' prismBodySet n = Metric.closedBall 0 1 :=
  (Classical.choose_spec (exists_prismBodySet_homeomorph n)).1

lemma prismBodyHomeomorph_frontier (n : ℕ) :
    prismBodyHomeomorph n '' frontier (prismBodySet n) = Metric.sphere 0 1 :=
  (Classical.choose_spec (exists_prismBodySet_homeomorph n)).2

noncomputable def prismProductHomeomorphDisk (n : ℕ) :
    ↥(prismProductSet n) ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
  let q : (EuclideanSpace ℝ (Fin n) × ℝ) ≃ₜ EuclideanSpace ℝ (Fin (n + 1)) :=
    (prismCoordinateEquiv n).symm.toHomeomorph
  have hq : q '' prismProductSet n = prismBodySet n := by
    rfl
  have hh : prismBodyHomeomorph n '' prismBodySet n =
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
    prismBodyHomeomorph_image n
  exact (q.image (prismProductSet n)).trans <| (Homeomorph.setCongr hq).trans <|
    (prismBodyHomeomorph n).image (prismBodySet n) |>.trans (Homeomorph.setCongr hh)

lemma prismProductHomeomorphDisk_frontier (n : ℕ) :
    ((prismCoordinateEquiv n).symm.toHomeomorph) '' frontier (prismProductSet n) =
      frontier (prismBodySet n) := by
  rw [prismBodySet]
  exact Homeomorph.image_frontier (prismCoordinateEquiv n).symm.toHomeomorph _

noncomputable def prismFrontierHomeomorphSphere (n : ℕ) :
    ↥(frontier (prismProductSet n)) ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
  let q : (EuclideanSpace ℝ (Fin n) × ℝ) ≃ₜ EuclideanSpace ℝ (Fin (n + 1)) :=
    (prismCoordinateEquiv n).symm.toHomeomorph
  have hq : q '' frontier (prismProductSet n) = frontier (prismBodySet n) := by
    exact prismProductHomeomorphDisk_frontier n
  have hh : prismBodyHomeomorph n '' frontier (prismBodySet n) =
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
    prismBodyHomeomorph_frontier n
  exact (q.image (frontier (prismProductSet n))).trans <| (Homeomorph.setCongr hq).trans <|
    (prismBodyHomeomorph n).image (frontier (prismBodySet n)) |>.trans (Homeomorph.setCongr hh)

def prismCapSet (n : ℕ) : Set (EuclideanSpace ℝ (Fin n) × ℝ) :=
  Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ×ˢ ({-1, 1} : Set ℝ)

def prismTubeSet (n : ℕ) : Set (EuclideanSpace ℝ (Fin n) × ℝ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ×ˢ Set.Icc (-1 : ℝ) 1

def prismSideSet (n : ℕ) : Set (EuclideanSpace ℝ (Fin n) × ℝ) :=
  prismCapSet n ∪ prismTubeSet n

lemma prismSideSet_eq_frontier (n : ℕ) :
    prismSideSet n = frontier (prismProductSet n) := by
  rw [prismProductSet_frontier]
  rfl

lemma prismSideSet_subset_product (n : ℕ) : prismSideSet n ⊆ prismProductSet n := by
  intro z hz
  change ((z.1 ∈ Metric.closedBall 0 1 ∧ z.2 ∈ ({-1, 1} : Set ℝ)) ∨
    z.1 ∈ Metric.sphere 0 1 ∧ z.2 ∈ Set.Icc (-1 : ℝ) 1) at hz
  change z.1 ∈ Metric.closedBall 0 1 ∧ z.2 ∈ Set.Icc (-1 : ℝ) 1
  rcases hz with ⟨hx, ht⟩ | ⟨hx, ht⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    refine ⟨hx, ?_⟩
    rcases ht with ht | ht
    · rw [ht]
      norm_num
    · rw [ht]
      norm_num
  · exact ⟨Metric.sphere_subset_closedBall hx, ht⟩

noncomputable def centeredIntervalEndsEquiv :
    ↥({-1, 1} : Set ℝ) ≃ Fin 2 where
  toFun x := if (x : ℝ) = -1 then 0 else 1
  invFun j := if j = 0 then ⟨-1, by simp⟩ else ⟨1, by simp⟩
  left_inv x := by
    apply Subtype.ext
    by_cases h : (x : ℝ) = -1
    · simp [h]
    · have hx := Set.mem_insert_iff.mp x.property
      have hx' : (x : ℝ) = -1 ∨ (x : ℝ) = 1 := by
        rcases hx with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Set.mem_singleton_iff.mp h')
      rcases hx' with h' | h'
      · contradiction
      · simp [h, h'] <;> norm_num
  right_inv j := by
    fin_cases j <;> simp <;> norm_num

noncomputable def centeredIntervalEndsHomeomorph :
    ↥({-1, 1} : Set ℝ) ≃ₜ Fin 2 := by
  let e := centeredIntervalEndsEquiv
  letI : Finite ↥({-1, 1} : Set ℝ) := Finite.of_injective e e.injective
  letI : DiscreteTopology ↥({-1, 1} : Set ℝ) := Finite.instDiscreteTopology
  exact e.toHomeomorphOfDiscrete

def finTwoToSum : Fin 2 ≃ Fin 1 ⊕ Fin 1 where
  toFun i := if i = 0 then Sum.inl 0 else Sum.inr 0
  invFun
    | .inl _ => 0
    | .inr _ => 1
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    cases i with
    | inl i => have : i = 0 := Subsingleton.elim _ _; subst i; rfl
    | inr i => have : i = 0 := Subsingleton.elim _ _; subst i; rfl

noncomputable def finTwoToSumHomeomorph : Fin 2 ≃ₜ Fin 1 ⊕ Fin 1 :=
  finTwoToSum.toHomeomorphOfDiscrete

noncomputable def centeredIntervalEndsToSumHomeomorph :
    ↥({-1, 1} : Set ℝ) ≃ₜ Fin 1 ⊕ Fin 1 :=
  centeredIntervalEndsHomeomorph.trans finTwoToSumHomeomorph

noncomputable def diskSubtypeHomeomorph (n : ℕ) :
    ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) ≃ₜ TopCat.disk.{u} n :=
  Homeomorph.ulift.{u, 0}.symm

noncomputable def sphereSubtypeHomeomorph (n : ℕ) :
    ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) ≃ₜ TopCat.diskBoundary.{u} n :=
  Homeomorph.ulift.{u, 0}.symm

noncomputable def prismCapSetProductHomeomorph (n : ℕ) :
    ↥(prismCapSet n) ≃ₜ
      ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) × ↥({-1, 1} : Set ℝ) := by
  let D := Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1
  let E := ({-1, 1} : Set ℝ)
  exact (Homeomorph.setCongr (show prismCapSet n = D ×ˢ E by rfl)).trans
    (Homeomorph.Set.prod D E)

noncomputable def prismCapProductEndsHomeomorph (n : ℕ) :
    (↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) × ↥({-1, 1} : Set ℝ)) ≃ₜ
      (↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) × (Fin 1 ⊕ Fin 1)) :=
  (Homeomorph.refl _).prodCongr centeredIntervalEndsToSumHomeomorph

noncomputable def prismCapProductSumHomeomorph (n : ℕ) :
    (↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) × (Fin 1 ⊕ Fin 1)) ≃ₜ
      ((↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) × Fin 1) ⊕
        (↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) × Fin 1)) :=
  Homeomorph.prodSumDistrib

noncomputable def prismCapDoubleDiskHomeomorph (n : ℕ) :
    ((↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) × Fin 1) ⊕
      (↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) × Fin 1)) ≃ₜ
        (↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) ⊕
          ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) := by
  let D := ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
  exact Homeomorph.sumCongr (Homeomorph.prodUnique D (Fin 1))
    (Homeomorph.prodUnique D (Fin 1))

noncomputable def prismCapDiskCopiesHomeomorph (n : ℕ) :
    (↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) ⊕
      ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) ≃ₜ
        (TopCat.disk.{u} n ⊕ TopCat.disk.{u} n) := by
  let d := diskSubtypeHomeomorph n
  exact Homeomorph.sumCongr d d

noncomputable def prismCapHomeomorphDiskSum (n : ℕ) :
    ↥(prismCapSet n) ≃ₜ (TopCat.disk.{u} n ⊕ TopCat.disk.{u} n) :=
  (prismCapSetProductHomeomorph n).trans <|
    (prismCapProductEndsHomeomorph n).trans <|
      (prismCapProductSumHomeomorph n).trans <|
        (prismCapDoubleDiskHomeomorph n).trans (prismCapDiskCopiesHomeomorph n)

lemma prismCapSetProductHomeomorph_apply {n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    (t : ℝ) (hx : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
    (ht : t ∈ ({-1, 1} : Set ℝ)) :
    prismCapSetProductHomeomorph n ⟨(x, t), by simp [prismCapSet, hx, ht]⟩ =
      (⟨x, hx⟩, ⟨t, ht⟩) := by
  rfl

lemma prismCapProductEndsHomeomorph_apply {n : ℕ}
    (x : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) (t : ↥({-1, 1} : Set ℝ)) :
    prismCapProductEndsHomeomorph n (x, t) = (x, centeredIntervalEndsToSumHomeomorph t) := rfl

lemma prismCapProductSumHomeomorph_apply_left {n : ℕ}
    (x : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) (t : Fin 1) :
    prismCapProductSumHomeomorph n (x, Sum.inl t) = Sum.inl (x, t) := by
  change Equiv.sumCongr (Equiv.prodComm (Fin 1) ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1))
    (Equiv.prodComm (Fin 1) ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1))
    (Sum.inl (t, x)) = _
  simp

lemma prismCapProductSumHomeomorph_apply_right {n : ℕ}
    (x : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) (t : Fin 1) :
    prismCapProductSumHomeomorph n (x, Sum.inr t) = Sum.inr (x, t) := by
  change Equiv.sumCongr (Equiv.prodComm (Fin 1) ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1))
    (Equiv.prodComm (Fin 1) ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1))
    (Sum.inr (t, x)) = _
  simp

lemma prismCapDoubleDiskHomeomorph_apply_left {n : ℕ}
    (x : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) × Fin 1) :
    prismCapDoubleDiskHomeomorph n (Sum.inl x) = Sum.inl x.1 := by
  simp [prismCapDoubleDiskHomeomorph, Homeomorph.prodUnique, Homeomorph.sumCongr]

lemma prismCapDoubleDiskHomeomorph_apply_right {n : ℕ}
    (x : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) × Fin 1) :
    prismCapDoubleDiskHomeomorph n (Sum.inr x) = Sum.inr x.1 := by
  simp [prismCapDoubleDiskHomeomorph, Homeomorph.prodUnique, Homeomorph.sumCongr]

lemma prismCapDiskCopiesHomeomorph_apply_left {n : ℕ}
    (x : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) :
    prismCapDiskCopiesHomeomorph n (Sum.inl x) = Sum.inl (diskSubtypeHomeomorph n x) := by
  simp [prismCapDiskCopiesHomeomorph, Homeomorph.sumCongr]

lemma prismCapDiskCopiesHomeomorph_apply_right {n : ℕ}
    (x : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) :
    prismCapDiskCopiesHomeomorph n (Sum.inr x) = Sum.inr (diskSubtypeHomeomorph n x) := by
  simp [prismCapDiskCopiesHomeomorph, Homeomorph.sumCongr]

@[simp] lemma centeredIntervalEndsToSumHomeomorph_neg :
    centeredIntervalEndsToSumHomeomorph ⟨-1, by simp⟩ = Sum.inl (0 : Fin 1) := by
  change finTwoToSum (centeredIntervalEndsEquiv ⟨-1, by simp⟩) = _
  simp [centeredIntervalEndsEquiv, finTwoToSum]

@[simp] lemma centeredIntervalEndsToSumHomeomorph_one :
    centeredIntervalEndsToSumHomeomorph ⟨1, by simp⟩ = Sum.inr (0 : Fin 1) := by
  change finTwoToSum (centeredIntervalEndsEquiv ⟨1, by simp⟩) = _
  simp [centeredIntervalEndsEquiv, finTwoToSum] <;> norm_num

noncomputable def prismCapEquivDiskSum (n : ℕ) :
    ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ×ˢ ({-1, 1} : Set ℝ)) ≃
      (TopCat.disk.{u} n ⊕ TopCat.disk.{u} n) := by
  let D := Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1
  let E := ({-1, 1} : Set ℝ)
  let e₁ : ↥(D ×ˢ E) ≃ ↥D × ↥E := Equiv.Set.prod D E
  let e₂ : ↥D × ↥E ≃ ↥D × (Fin 1 ⊕ Fin 1) :=
    Equiv.prodCongr (Equiv.refl _) centeredIntervalEndsToSumHomeomorph.toEquiv
  let e₃ : ↥D × (Fin 1 ⊕ Fin 1) ≃ (↥D × Fin 1) ⊕ (↥D × Fin 1) :=
    Equiv.prodSumDistrib _ _ _
  let e₄ : (↥D × Fin 1) ⊕ (↥D × Fin 1) ≃ ↥D ⊕ ↥D :=
    Equiv.sumCongr (Equiv.prodUnique ↥D (Fin 1)) (Equiv.prodUnique ↥D (Fin 1))
  let eDisk : ↥D ≃ TopCat.disk.{u} n := (diskSubtypeHomeomorph n).toEquiv
  let e₅ : ↥D ⊕ ↥D ≃ (TopCat.disk.{u} n ⊕ TopCat.disk.{u} n) :=
    Equiv.sumCongr eDisk eDisk
  exact e₁.trans (e₂.trans (e₃.trans (e₄.trans e₅)))

lemma prismCapHomeomorphDiskSum_apply_neg {n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    prismCapHomeomorphDiskSum n ⟨(x, -1), by simp [prismCapSet, hx]⟩ =
      Sum.inl (diskSubtypeHomeomorph n ⟨x, hx⟩) := by
  change prismCapDiskCopiesHomeomorph n
    (prismCapDoubleDiskHomeomorph n
      (prismCapProductSumHomeomorph n
        (prismCapProductEndsHomeomorph n
          (prismCapSetProductHomeomorph n ⟨(x, -1), by simp [prismCapSet, hx]⟩)))) = _
  rw [prismCapSetProductHomeomorph_apply x (-1) hx (by simp)]
  rw [prismCapProductEndsHomeomorph_apply, centeredIntervalEndsToSumHomeomorph_neg]
  rw [prismCapProductSumHomeomorph_apply_left, prismCapDoubleDiskHomeomorph_apply_left,
    prismCapDiskCopiesHomeomorph_apply_left]

lemma prismCapHomeomorphDiskSum_apply_one {n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    prismCapHomeomorphDiskSum n ⟨(x, 1), by simp [prismCapSet, hx]⟩ =
      Sum.inr (diskSubtypeHomeomorph n ⟨x, hx⟩) := by
  change prismCapDiskCopiesHomeomorph n
    (prismCapDoubleDiskHomeomorph n
      (prismCapProductSumHomeomorph n
        (prismCapProductEndsHomeomorph n
          (prismCapSetProductHomeomorph n ⟨(x, 1), by simp [prismCapSet, hx]⟩)))) = _
  rw [prismCapSetProductHomeomorph_apply x 1 hx (by simp)]
  rw [prismCapProductEndsHomeomorph_apply, centeredIntervalEndsToSumHomeomorph_one]
  rw [prismCapProductSumHomeomorph_apply_right, prismCapDoubleDiskHomeomorph_apply_right,
    prismCapDiskCopiesHomeomorph_apply_right]

noncomputable def prismSideInclusion (n : ℕ) :
    TopCat.of (ULift.{u, 0} (prismSideSet n)) ⟶
      TopCat.of (ULift.{u, 0} (prismProductSet n)) :=
  TopCat.ofHom ⟨fun x => ULift.up ⟨x.down.1, prismSideSet_subset_product n x.down.2⟩,
    by fun_prop⟩

@[simp] lemma prismSideInclusion_apply {n : ℕ}
    (z : ULift.{u, 0} (prismSideSet n)) :
    prismSideInclusion n z = ULift.up ⟨z.down.1, prismSideSet_subset_product n z.down.2⟩ := rfl

noncomputable def prismCapSideInclusion (n : ℕ) :
    TopCat.of (ULift.{u, 0} (prismCapSet n)) ⟶ TopCat.of (ULift.{u, 0} (prismSideSet n)) :=
  TopCat.ofHom ⟨fun z => ULift.up ⟨z.down.1, Or.inl z.down.2⟩, by fun_prop⟩

@[simp] lemma prismCapSideInclusion_apply {n : ℕ}
    (z : ULift.{u, 0} (prismCapSet n)) :
    prismCapSideInclusion n z = ULift.up ⟨z.down.1, Or.inl z.down.2⟩ := rfl

noncomputable def prismTubeSideInclusion (n : ℕ) :
    TopCat.of (ULift.{u, 0} (prismTubeSet n)) ⟶ TopCat.of (ULift.{u, 0} (prismSideSet n)) :=
  TopCat.ofHom ⟨fun z => ULift.up ⟨z.down.1, Or.inr z.down.2⟩, by fun_prop⟩

@[simp] lemma prismTubeSideInclusion_apply {n : ℕ}
    (z : ULift.{u, 0} (prismTubeSet n)) :
    prismTubeSideInclusion n z = ULift.up ⟨z.down.1, Or.inr z.down.2⟩ := rfl

noncomputable def prismProductDiskIso (n : ℕ) :
    TopCat.of (ULift.{u, 0} (prismProductSet n)) ≅ TopCat.disk.{u} (n + 1) :=
  TopCat.isoOfHomeo <| Homeomorph.ulift.trans <|
    (prismProductHomeomorphDisk n).trans Homeomorph.ulift.symm

noncomputable def prismSideSphereIso (n : ℕ) :
    TopCat.of (ULift.{u, 0} (prismSideSet n)) ≅ TopCat.diskBoundary.{u} (n + 1) := by
  let e : ↥(prismSideSet n) ≃ₜ ↥(frontier (prismProductSet n)) :=
    (Homeomorph.setCongr (prismSideSet_eq_frontier n)).trans (Homeomorph.refl _)
  exact TopCat.isoOfHomeo <| Homeomorph.ulift.trans <| e.trans <|
    (prismFrontierHomeomorphSphere n).trans Homeomorph.ulift.symm

noncomputable def intervalCenteredHomeomorph :
    (TopCat.I : TopCat.{u}) ≃ₜ ↥(Set.Icc (-1 : ℝ) 1) :=
  TopCat.I.homeomorph.trans (_root_.iccHomeoI (-1 : ℝ) 1 (by norm_num)).symm

@[simp] lemma intervalCenteredHomeomorph_symm_neg :
    intervalCenteredHomeomorph.symm ⟨-1, by norm_num⟩ = (0 : TopCat.I) := by
  apply TopCat.I.ext
  apply Subtype.ext
  simp [intervalCenteredHomeomorph, TopCat.I.homeomorph, Homeomorph.ulift, Equiv.ulift,
    _root_.iccHomeoI_apply_coe] <;> rfl

@[simp] lemma intervalCenteredHomeomorph_symm_one :
    intervalCenteredHomeomorph.symm ⟨1, by norm_num⟩ = (1 : TopCat.I) := by
  apply TopCat.I.ext
  apply Subtype.ext
  simp [intervalCenteredHomeomorph, TopCat.I.homeomorph, Homeomorph.ulift, Equiv.ulift,
    _root_.iccHomeoI_apply_coe] <;> rfl

@[simp] lemma intervalCenteredHomeomorph_zero :
    intervalCenteredHomeomorph.{u} (0 : TopCat.I.{u}) = ⟨-1, by norm_num⟩ := by
  calc
    intervalCenteredHomeomorph.{u} 0 = intervalCenteredHomeomorph.{u}
        (intervalCenteredHomeomorph.{u}.symm ⟨-1, by norm_num⟩) := by
          rw [intervalCenteredHomeomorph_symm_neg]
    _ = ⟨-1, by norm_num⟩ := intervalCenteredHomeomorph.{u}.apply_symm_apply _

@[simp] lemma intervalCenteredHomeomorph_one :
    intervalCenteredHomeomorph.{u} (1 : TopCat.I.{u}) = ⟨1, by norm_num⟩ := by
  calc
    intervalCenteredHomeomorph.{u} 1 = intervalCenteredHomeomorph.{u}
        (intervalCenteredHomeomorph.{u}.symm ⟨1, by norm_num⟩) := by
          rw [intervalCenteredHomeomorph_symm_one]
    _ = ⟨1, by norm_num⟩ := intervalCenteredHomeomorph.{u}.apply_symm_apply _

noncomputable def diskIntervalHomeomorphPrismProduct (n : ℕ) :
    (TopCat.disk.{u} n × TopCat.I.{u}) ≃ₜ ↥(prismProductSet n) := by
  let D := Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1
  let J := Set.Icc (-1 : ℝ) 1
  change (ULift.{u, 0} (↥D) × ULift.{u, 0} unitInterval) ≃ₜ ↥(D ×ˢ J)
  exact ((Homeomorph.ulift).prodCongr intervalCenteredHomeomorph).trans
    (Homeomorph.Set.prod D J).symm

lemma diskIntervalHomeomorphPrismProduct_val {n : ℕ} (a : TopCat.disk.{u} n)
    (t : TopCat.I.{u}) :
    (diskIntervalHomeomorphPrismProduct n (a, t)).1 =
      (a.1.1, (intervalCenteredHomeomorph.{u} t).1) := by
  let D := Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1
  let J := Set.Icc (-1 : ℝ) 1
  change (Equiv.subtypeProdEquivProd.symm
    (Equiv.ulift.{u, 0} a, intervalCenteredHomeomorph.{u} t)).1 = _
  simp [Equiv.subtypeProdEquivProd]

lemma diskIntervalHomeomorphPrismProduct_zero {n : ℕ} (a : TopCat.disk.{u} n) :
    diskIntervalHomeomorphPrismProduct n (a, 0) =
      ⟨(a.1.1, -1), by exact ⟨a.1.2, by norm_num⟩⟩ := by
  let D := Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1
  let J := Set.Icc (-1 : ℝ) 1
  apply Subtype.ext
  change (Equiv.subtypeProdEquivProd.symm
    (Equiv.ulift.{u, 0} a, intervalCenteredHomeomorph.{u} 0)).1 = (a.1.1, -1)
  simp [Equiv.subtypeProdEquivProd, intervalCenteredHomeomorph_zero]

lemma diskIntervalHomeomorphPrismProduct_one {n : ℕ} (a : TopCat.disk.{u} n) :
    diskIntervalHomeomorphPrismProduct n (a, 1) =
      ⟨(a.1.1, 1), by exact ⟨a.1.2, by norm_num⟩⟩ := by
  let D := Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1
  let J := Set.Icc (-1 : ℝ) 1
  apply Subtype.ext
  change (Equiv.subtypeProdEquivProd.symm
    (Equiv.ulift.{u, 0} a, intervalCenteredHomeomorph.{u} 1)).1 = (a.1.1, 1)
  simp [Equiv.subtypeProdEquivProd, intervalCenteredHomeomorph_one]

noncomputable def diskCylinderPrismIso (n : ℕ) :
    TopCat.disk.{u} n ⊗ TopCat.I.{u} ≅ TopCat.of (ULift.{u, 0} (prismProductSet n)) := by
  let e : (TopCat.disk.{u} n ⊗ TopCat.I.{u}) ≅
      TopCat.of (TopCat.disk.{u} n × TopCat.I.{u}) :=
    topTensorProdIso _ _ ≪≫ TopCat.prodIsoProd _ _
  exact e ≪≫ (TopCat.isoOfHomeo
    ((diskIntervalHomeomorphPrismProduct n).trans Homeomorph.ulift.symm))

noncomputable def prismTubeHomeomorphBoundaryCylinder (n : ℕ) :
    ↥(prismTubeSet n) ≃ₜ (TopCat.diskBoundary.{u} n × TopCat.I.{u}) := by
  let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1
  let J := Set.Icc (-1 : ℝ) 1
  change ↥(S ×ˢ J) ≃ₜ (ULift.{u, 0} (↥S) × ULift.{u, 0} unitInterval)
  exact (Homeomorph.Set.prod S J).trans <|
    (sphereSubtypeHomeomorph n).prodCongr intervalCenteredHomeomorph.symm

lemma prismTubeHomeomorphBoundaryCylinder_apply {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.sphere 0 1)
    (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    prismTubeHomeomorphBoundaryCylinder n ⟨(x, t), ⟨hx, ht⟩⟩ =
      (sphereSubtypeHomeomorph n ⟨x, hx⟩, intervalCenteredHomeomorph.symm ⟨t, ht⟩) := by
  rfl

noncomputable def prismTubeBoundaryCylinderIso (n : ℕ) :
    TopCat.of.{u} (ULift.{u, 0} (prismTubeSet n)) ≅
      TopCat.diskBoundary.{u} n ⊗ TopCat.I.{u} := by
  let h : ULift.{u, 0} (↥(prismTubeSet n)) ≃ₜ
      (TopCat.diskBoundary.{u} n × TopCat.I.{u}) :=
    Homeomorph.ulift.{u, 0}.trans (prismTubeHomeomorphBoundaryCylinder n)
  exact TopCat.isoOfHomeo h ≪≫ (topTensorIProductIso _).symm

lemma prismTubeBoundaryCylinderIso_apply_neg {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.sphere 0 1) :
    (prismTubeBoundaryCylinderIso n).hom
      (ULift.up (⟨(x, -1), ⟨hx, by norm_num⟩⟩ : ↥(prismTubeSet n))) =
      TopCat.ι₀ (X := TopCat.diskBoundary.{u} n) (sphereSubtypeHomeomorph n ⟨x, hx⟩) := by
  let z : ULift.{u, 0} (↥(prismTubeSet n)) :=
    ULift.up (⟨(x, -1), ⟨hx, by norm_num⟩⟩ : ↥(prismTubeSet n))
  let a : TopCat.diskBoundary.{u} n := sphereSubtypeHomeomorph n ⟨x, hx⟩
  change (topTensorIProductIso (TopCat.diskBoundary.{u} n)).inv.hom
      (prismTubeHomeomorphBoundaryCylinder n ⟨(x, -1), ⟨hx, by norm_num⟩⟩) = TopCat.ι₀ a
  rw [prismTubeHomeomorphBoundaryCylinder_apply x hx (-1) (by norm_num :
    (-1 : ℝ) ∈ Set.Icc (-1) 1), intervalCenteredHomeomorph_symm_neg]
  exact ConcreteCategory.congr_hom
    (topTensorIotaZero_fromProduct (X := TopCat.diskBoundary.{u} n)) a

lemma prismTubeBoundaryCylinderIso_apply_one {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.sphere 0 1) :
    (prismTubeBoundaryCylinderIso n).hom
      (ULift.up (⟨(x, 1), ⟨hx, by norm_num⟩⟩ : ↥(prismTubeSet n))) =
      TopCat.ι₁ (X := TopCat.diskBoundary.{u} n) (sphereSubtypeHomeomorph n ⟨x, hx⟩) := by
  let z : ULift.{u, 0} (↥(prismTubeSet n)) :=
    ULift.up (⟨(x, 1), ⟨hx, by norm_num⟩⟩ : ↥(prismTubeSet n))
  let a : TopCat.diskBoundary.{u} n := sphereSubtypeHomeomorph n ⟨x, hx⟩
  change (topTensorIProductIso (TopCat.diskBoundary.{u} n)).inv.hom
      (prismTubeHomeomorphBoundaryCylinder n ⟨(x, 1), ⟨hx, by norm_num⟩⟩) = TopCat.ι₁ a
  rw [prismTubeHomeomorphBoundaryCylinder_apply x hx 1 (by norm_num :
    (1 : ℝ) ∈ Set.Icc (-1) 1), intervalCenteredHomeomorph_symm_one]
  exact ConcreteCategory.congr_hom
    (topTensorIotaOne_fromProduct (X := TopCat.diskBoundary.{u} n)) a

noncomputable def topCatBinaryCoprodSumIso (X Y : TopCat.{u}) :
    X ⨿ Y ≅ TopCat.of (X ⊕ Y) := by
  let η : X ⨿ Y ⟶ TopCat.of (X ⊕ Y) :=
    coprod.desc (TopCat.ofHom ⟨Sum.inl, by fun_prop⟩)
      (TopCat.ofHom ⟨Sum.inr, by fun_prop⟩)
  let ε : TopCat.of (X ⊕ Y) ⟶ X ⨿ Y :=
    TopCat.ofHom ⟨
      Sum.elim (TopCat.Hom.hom (coprod.inl : X ⟶ X ⨿ Y))
        (TopCat.Hom.hom (coprod.inr : Y ⟶ X ⨿ Y)),
      continuous_sumElim.mpr ⟨
        (TopCat.Hom.hom (coprod.inl : X ⟶ X ⨿ Y)).continuous,
        (TopCat.Hom.hom (coprod.inr : Y ⟶ X ⨿ Y)).continuous⟩⟩
  have hηε : η ≫ ε = 𝟙 (X ⨿ Y) := by
    apply coprod.hom_ext
    · change coprod.inl ≫ (η ≫ ε) = coprod.inl
      calc
        coprod.inl ≫ (η ≫ ε) = (coprod.inl ≫ η) ≫ ε := (Category.assoc _ _ _).symm
        _ = TopCat.ofHom ⟨Sum.inl, by fun_prop⟩ ≫ ε := by rw [coprod.inl_desc]
        _ = coprod.inl := by
          apply TopCat.hom_ext
          ext x
          rfl
    · change coprod.inr ≫ (η ≫ ε) = coprod.inr
      calc
        coprod.inr ≫ (η ≫ ε) = (coprod.inr ≫ η) ≫ ε := (Category.assoc _ _ _).symm
        _ = TopCat.ofHom ⟨Sum.inr, by fun_prop⟩ ≫ ε := by rw [coprod.inr_desc]
        _ = coprod.inr := by
          apply TopCat.hom_ext
          ext x
          rfl
  have hεη : ε ≫ η = 𝟙 (TopCat.of (X ⊕ Y)) := by
    apply TopCat.hom_ext
    ext x
    cases x <;> simp [η, ε]
  exact ⟨η, ε, hηε, hεη⟩

lemma topCatIsoOfHomeo_ulift_apply {S : Type} {T : Type u} [TopologicalSpace S]
    [TopologicalSpace T] (h : S ≃ₜ T) (x : S) :
    (TopCat.isoOfHomeo (X := TopCat.of (ULift.{u, 0} S)) (Y := TopCat.of T)
      (Homeomorph.ulift.{u, 0}.trans h)).hom (ULift.up x) = h x := by
  let e : TopCat.of (ULift.{u, 0} S) ≅ TopCat.of T :=
    TopCat.isoOfHomeo (Homeomorph.ulift.{u, 0}.trans h)
  change e.hom (ULift.up x) = h x
  rfl

noncomputable def prismCapCoproductIso (n : ℕ) :
    TopCat.of (ULift.{u, 0} (prismCapSet n)) ≅
      TopCat.disk.{u} n ⨿ TopCat.disk.{u} n :=
  TopCat.isoOfHomeo (Homeomorph.ulift.trans (prismCapHomeomorphDiskSum n)) ≪≫
    (topCatBinaryCoprodSumIso _ _).symm

lemma prismCapCoproductIso_apply_asSum {n : ℕ} (x : ↥(prismCapSet n)) :
    (prismCapCoproductIso n).hom (ULift.up x) =
      TopCat.Hom.hom ((topCatBinaryCoprodSumIso (TopCat.disk.{u} n)
        (TopCat.disk.{u} n)).symm.hom) (prismCapHomeomorphDiskSum n x) := by
  rfl

lemma prismCapCoproductIso_apply_neg {n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    (prismCapCoproductIso n).hom
      (ULift.up (⟨(x, -1), ⟨hx, by norm_num⟩⟩ : ↥(prismCapSet n))) =
      TopCat.Hom.hom (coprod.inl : TopCat.disk.{u} n ⟶
        TopCat.disk.{u} n ⨿ TopCat.disk.{u} n) (diskSubtypeHomeomorph n ⟨x, hx⟩) := by
  rw [prismCapCoproductIso_apply_asSum]
  rw [prismCapHomeomorphDiskSum_apply_neg x hx]
  simp [topCatBinaryCoprodSumIso]

lemma prismCapCoproductIso_apply_one {n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    (prismCapCoproductIso n).hom
      (ULift.up (⟨(x, 1), ⟨hx, by norm_num⟩⟩ : ↥(prismCapSet n))) =
      TopCat.Hom.hom (coprod.inr : TopCat.disk.{u} n ⟶
        TopCat.disk.{u} n ⨿ TopCat.disk.{u} n) (diskSubtypeHomeomorph n ⟨x, hx⟩) := by
  rw [prismCapCoproductIso_apply_asSum]
  rw [prismCapHomeomorphDiskSum_apply_one x hx]
  simp [topCatBinaryCoprodSumIso]

lemma diskBoundaryInclusion_apply_sphere {n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ Metric.sphere 0 1) :
    diskBoundaryInclusion n (sphereSubtypeHomeomorph n ⟨x, hx⟩) =
      diskSubtypeHomeomorph n ⟨x, Metric.sphere_subset_closedBall hx⟩ := by
  rfl

noncomputable def cylinderEndpointMap (X : TopCat.{u}) :
    X ⨿ X ⟶ X ⊗ TopCat.I.{u} :=
  coprod.desc TopCat.ι₀ TopCat.ι₁

lemma prismCellCapTube_agree_neg {n : ℕ} {X P : TopCat.{u}}
    (f : TopCat.diskBoundary.{u} n ⟶ X) (k : TopCat.disk.{u} n ⟶ P) (j : X ⟶ P)
    (hsq : IsPushout (diskBoundaryInclusion.{u} n) f k j)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.sphere 0 1) :
    (pushout.inr (cylinderEndpointMap X) (coprod.map j j))
      ((coprod.map k k) ((prismCapCoproductIso n).hom
        (ULift.up (⟨(x, -1), ⟨Metric.sphere_subset_closedBall hx, by norm_num⟩⟩ :
          ↥(prismCapSet n))))) =
    (pushout.inl (cylinderEndpointMap X) (coprod.map j j))
      ((f ▷ TopCat.I.{u}) ((prismTubeBoundaryCylinderIso n).hom
        (ULift.up (⟨(x, -1), ⟨hx, by norm_num⟩⟩ : ↥(prismTubeSet n))))) := by
  let a : TopCat.diskBoundary.{u} n := sphereSubtypeHomeomorph n ⟨x, hx⟩
  let b : TopCat.disk.{u} n :=
    diskSubtypeHomeomorph n ⟨x, Metric.sphere_subset_closedBall hx⟩
  let eX := cylinderEndpointMap X
  let jsum := coprod.map j j
  let rX := pushout.inl eX jsum
  let rP := pushout.inr eX jsum
  letI : HasPushout eX jsum := inferInstance
  have hR : IsPushout eX jsum rX rP := IsPushout.of_hasPushout eX jsum
  have hEndInl : coprod.inl ≫ eX = TopCat.ι₀ := by
    dsimp [eX, cylinderEndpointMap]
    exact coprod.inl_desc _ _
  have hMapInl : coprod.inl ≫ jsum = j ≫ coprod.inl := coprod.inl_map j j
  have hRcomp : (TopCat.ι₀ ≫ rX) = (j ≫ coprod.inl) ≫ rP := by
    calc
      TopCat.ι₀ ≫ rX = (coprod.inl ≫ eX) ≫ rX := by rw [hEndInl]
      _ = coprod.inl ≫ (eX ≫ rX) := Category.assoc _ _ _
      _ = coprod.inl ≫ (jsum ≫ rP) := by rw [hR.w]
      _ = (coprod.inl ≫ jsum) ≫ rP := (Category.assoc _ _ _).symm
      _ = (j ≫ coprod.inl) ≫ rP := by rw [hMapInl]
  have hAttach : k b = j (f a) := by
    calc
      k b = k ((diskBoundaryInclusion n) a) := by
        rw [diskBoundaryInclusion_apply_sphere (n := n) x hx]
      _ = j (f a) := by
        simpa using ConcreteCategory.congr_hom hsq.w a
  have hEndpoint : (f ▷ TopCat.I.{u}) (TopCat.ι₀ a) = TopCat.ι₀ (f a) :=
    ConcreteCategory.congr_hom (TopCat.ι₀_comp f) a
  have hPushAt : ConcreteCategory.hom (TopCat.ι₀ ≫ rX) (f a) =
      ConcreteCategory.hom ((j ≫ coprod.inl) ≫ rP) (f a) :=
    ConcreteCategory.congr_hom hRcomp (f a)
  have hMapAt : (coprod.map k k) (TopCat.Hom.hom
      (coprod.inl : TopCat.disk.{u} n ⟶ TopCat.disk.{u} n ⨿ TopCat.disk.{u} n) b) =
      TopCat.Hom.hom (coprod.inl : P ⟶ P ⨿ P) (k b) := by
    exact ConcreteCategory.congr_hom (coprod.inl_map k k) b
  rw [prismCapCoproductIso_apply_neg x (Metric.sphere_subset_closedBall hx),
    prismTubeBoundaryCylinderIso_apply_neg x hx]
  calc
    rP ((coprod.map k k) (TopCat.Hom.hom
      (coprod.inl : TopCat.disk.{u} n ⟶ TopCat.disk.{u} n ⨿ TopCat.disk.{u} n) b)) =
      rP (TopCat.Hom.hom (coprod.inl : P ⟶ P ⨿ P) (k b)) := by rw [hMapAt]
    _ = rP (TopCat.Hom.hom (coprod.inl : P ⟶ P ⨿ P) (j (f a))) := by rw [hAttach]
    _ = ConcreteCategory.hom ((j ≫ coprod.inl) ≫ rP) (f a) := by
      simp [ConcreteCategory.comp_apply]
    _ = ConcreteCategory.hom (TopCat.ι₀ ≫ rX) (f a) := hPushAt.symm
    _ = rX (TopCat.ι₀ (f a)) := rfl
    _ = rX ((f ▷ TopCat.I.{u}) (TopCat.ι₀ a)) := by rw [← hEndpoint]

lemma prismCellCapTube_agree_one {n : ℕ} {X P : TopCat.{u}}
    (f : TopCat.diskBoundary.{u} n ⟶ X) (k : TopCat.disk.{u} n ⟶ P) (j : X ⟶ P)
    (hsq : IsPushout (diskBoundaryInclusion.{u} n) f k j)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.sphere 0 1) :
    (pushout.inr (cylinderEndpointMap X) (coprod.map j j))
      ((coprod.map k k) ((prismCapCoproductIso n).hom
        (ULift.up (⟨(x, 1), ⟨Metric.sphere_subset_closedBall hx, by norm_num⟩⟩ :
          ↥(prismCapSet n))))) =
    (pushout.inl (cylinderEndpointMap X) (coprod.map j j))
      ((f ▷ TopCat.I.{u}) ((prismTubeBoundaryCylinderIso n).hom
        (ULift.up (⟨(x, 1), ⟨hx, by norm_num⟩⟩ : ↥(prismTubeSet n))))) := by
  let a : TopCat.diskBoundary.{u} n := sphereSubtypeHomeomorph n ⟨x, hx⟩
  let b : TopCat.disk.{u} n :=
    diskSubtypeHomeomorph n ⟨x, Metric.sphere_subset_closedBall hx⟩
  let eX := cylinderEndpointMap X
  let jsum := coprod.map j j
  let rX := pushout.inl eX jsum
  let rP := pushout.inr eX jsum
  letI : HasPushout eX jsum := inferInstance
  have hR : IsPushout eX jsum rX rP := IsPushout.of_hasPushout eX jsum
  have hEndInr : coprod.inr ≫ eX = TopCat.ι₁ := by
    dsimp [eX, cylinderEndpointMap]
    exact coprod.inr_desc _ _
  have hMapInr : coprod.inr ≫ jsum = j ≫ coprod.inr := coprod.inr_map j j
  have hRcomp : (TopCat.ι₁ ≫ rX) = (j ≫ coprod.inr) ≫ rP := by
    calc
      TopCat.ι₁ ≫ rX = (coprod.inr ≫ eX) ≫ rX := by rw [hEndInr]
      _ = coprod.inr ≫ (eX ≫ rX) := Category.assoc _ _ _
      _ = coprod.inr ≫ (jsum ≫ rP) := by rw [hR.w]
      _ = (coprod.inr ≫ jsum) ≫ rP := (Category.assoc _ _ _).symm
      _ = (j ≫ coprod.inr) ≫ rP := by rw [hMapInr]
  have hAttach : k b = j (f a) := by
    calc
      k b = k ((diskBoundaryInclusion n) a) := by
        rw [diskBoundaryInclusion_apply_sphere (n := n) x hx]
      _ = j (f a) := by
        simpa using ConcreteCategory.congr_hom hsq.w a
  have hEndpoint : (f ▷ TopCat.I.{u}) (TopCat.ι₁ a) = TopCat.ι₁ (f a) :=
    ConcreteCategory.congr_hom (TopCat.ι₁_comp f) a
  have hPushAt : ConcreteCategory.hom (TopCat.ι₁ ≫ rX) (f a) =
      ConcreteCategory.hom ((j ≫ coprod.inr) ≫ rP) (f a) :=
    ConcreteCategory.congr_hom hRcomp (f a)
  have hMapAt : (coprod.map k k) (TopCat.Hom.hom
      (coprod.inr : TopCat.disk.{u} n ⟶ TopCat.disk.{u} n ⨿ TopCat.disk.{u} n) b) =
      TopCat.Hom.hom (coprod.inr : P ⟶ P ⨿ P) (k b) := by
    exact ConcreteCategory.congr_hom (coprod.inr_map k k) b
  rw [prismCapCoproductIso_apply_one x (Metric.sphere_subset_closedBall hx),
    prismTubeBoundaryCylinderIso_apply_one x hx]
  calc
    rP ((coprod.map k k) (TopCat.Hom.hom
      (coprod.inr : TopCat.disk.{u} n ⟶ TopCat.disk.{u} n ⨿ TopCat.disk.{u} n) b)) =
      rP (TopCat.Hom.hom (coprod.inr : P ⟶ P ⨿ P) (k b)) := by rw [hMapAt]
    _ = rP (TopCat.Hom.hom (coprod.inr : P ⟶ P ⨿ P) (j (f a))) := by rw [hAttach]
    _ = ConcreteCategory.hom ((j ≫ coprod.inr) ≫ rP) (f a) := by
      simp [ConcreteCategory.comp_apply]
    _ = ConcreteCategory.hom (TopCat.ι₁ ≫ rX) (f a) := hPushAt.symm
    _ = rX (TopCat.ι₁ (f a)) := rfl
    _ = rX ((f ▷ TopCat.I.{u}) (TopCat.ι₁ a)) := by rw [← hEndpoint]

lemma prismCellCapTube_agree_at {n : ℕ} {X P : TopCat.{u}}
    (f : TopCat.diskBoundary.{u} n ⟶ X) (k : TopCat.disk.{u} n ⟶ P) (j : X ⟶ P)
    (hsq : IsPushout (diskBoundaryInclusion.{u} n) f k j)
    {z : EuclideanSpace ℝ (Fin n) × ℝ} (hc : z ∈ prismCapSet n) (ht : z ∈ prismTubeSet n) :
    (pushout.inr (cylinderEndpointMap X) (coprod.map j j))
      ((coprod.map k k) ((prismCapCoproductIso n).hom (ULift.up ⟨z, hc⟩))) =
    (pushout.inl (cylinderEndpointMap X) (coprod.map j j))
      ((f ▷ TopCat.I.{u}) ((prismTubeBoundaryCylinderIso n).hom (ULift.up ⟨z, ht⟩))) := by
  rcases z with ⟨x, t⟩
  change x ∈ Metric.closedBall 0 1 ∧ t ∈ ({-1, 1} : Set ℝ) at hc
  change x ∈ Metric.sphere 0 1 ∧ t ∈ Set.Icc (-1 : ℝ) 1 at ht
  rcases Set.mem_insert_iff.mp hc.2 with htNeg | htOne
  · subst t
    exact prismCellCapTube_agree_neg f k j hsq x ht.1
  · have htEq := Set.mem_singleton_iff.mp htOne
    subst t
    exact prismCellCapTube_agree_one f k j hsq x ht.1

noncomputable def prismCellBoundaryMap {n : ℕ} {X P : TopCat.{u}}
    (f : TopCat.diskBoundary.{u} n ⟶ X) (k : TopCat.disk.{u} n ⟶ P) (j : X ⟶ P)
    (hsq : IsPushout (diskBoundaryInclusion.{u} n) f k j) :
    TopCat.of (ULift.{u, 0} (prismSideSet n)) ⟶
      pushout (cylinderEndpointMap X) (coprod.map j j) := by
  classical
  let eX := cylinderEndpointMap X
  let jsum := coprod.map j j
  let R := pushout eX jsum
  let rX := pushout.inl eX jsum
  let rP := pushout.inr eX jsum
  let capMap : TopCat.of (ULift.{u, 0} (prismCapSet n)) ⟶ R :=
    (prismCapCoproductIso n).hom ≫ coprod.map k k ≫ rP
  let tubeMap : TopCat.of (ULift.{u, 0} (prismTubeSet n)) ⟶ R :=
    (prismTubeBoundaryCylinderIso n).hom ≫ (f ▷ TopCat.I.{u}) ≫ rX
  let b₀ : TopCat.disk.{u} n := diskSubtypeHomeomorph n ⟨0, by simp⟩
  let r₀ : R := TopCat.Hom.hom rP
    (TopCat.Hom.hom (coprod.inl : P ⟶ P ⨿ P) (TopCat.Hom.hom k b₀))
  let capExt : (EuclideanSpace ℝ (Fin n) × ℝ) → R := fun z =>
    if hz : z ∈ prismCapSet n then
      TopCat.Hom.hom capMap (ULift.up ⟨z, hz⟩)
    else r₀
  let tubeExt : (EuclideanSpace ℝ (Fin n) × ℝ) → R := fun z =>
    if hz : z ∈ prismTubeSet n then
      TopCat.Hom.hom tubeMap (ULift.up ⟨z, hz⟩)
    else r₀
  let sideFun : (EuclideanSpace ℝ (Fin n) × ℝ) → R := fun z =>
    if hz : z ∈ prismCapSet n then capExt z else tubeExt z
  have hAgree {z : EuclideanSpace ℝ (Fin n) × ℝ}
      (hc : z ∈ prismCapSet n) (ht : z ∈ prismTubeSet n) : capExt z = tubeExt z := by
    rcases z with ⟨x, t⟩
    change x ∈ Metric.closedBall 0 1 ∧ t ∈ ({-1, 1} : Set ℝ) at hc
    change x ∈ Metric.sphere 0 1 ∧ t ∈ Set.Icc (-1 : ℝ) 1 at ht
    have hc' : (x, t) ∈ prismCapSet n := ⟨hc.1, hc.2⟩
    have ht' : (x, t) ∈ prismTubeSet n := ⟨ht.1, ht.2⟩
    have hend : t = -1 ∨ t = 1 := by
      rcases Set.mem_insert_iff.mp hc.2 with h | h
      · exact Or.inl h
      · exact Or.inr (Set.mem_singleton_iff.mp h)
    rcases hend with rfl | rfl
    · have hcNeg : (x, -1) ∈ prismCapSet n := ⟨hc.1, by simp⟩
      have htNeg : (x, -1) ∈ prismTubeSet n := ⟨ht.1, by norm_num⟩
      change capExt (x, -1) = tubeExt (x, -1)
      dsimp [capExt, tubeExt]
      rw [dif_pos hcNeg, dif_pos htNeg]
      change (pushout.inr (cylinderEndpointMap X) (coprod.map j j))
          ((coprod.map k k) ((prismCapCoproductIso n).hom
            (ULift.up ⟨(x, -1), hcNeg⟩))) =
        (pushout.inl (cylinderEndpointMap X) (coprod.map j j))
          ((f ▷ TopCat.I.{u}) ((prismTubeBoundaryCylinderIso n).hom
            (ULift.up ⟨(x, -1), htNeg⟩)))
      exact prismCellCapTube_agree_neg f k j hsq x ht.1
    · have hcOne : (x, 1) ∈ prismCapSet n := ⟨hc.1, by simp⟩
      have htOne : (x, 1) ∈ prismTubeSet n := ⟨ht.1, by norm_num⟩
      change capExt (x, 1) = tubeExt (x, 1)
      dsimp [capExt, tubeExt]
      rw [dif_pos hcOne, dif_pos htOne]
      change (pushout.inr (cylinderEndpointMap X) (coprod.map j j))
          ((coprod.map k k) ((prismCapCoproductIso n).hom
            (ULift.up ⟨(x, 1), hcOne⟩))) =
        (pushout.inl (cylinderEndpointMap X) (coprod.map j j))
          ((f ▷ TopCat.I.{u}) ((prismTubeBoundaryCylinderIso n).hom
            (ULift.up ⟨(x, 1), htOne⟩)))
      exact prismCellCapTube_agree_one f k j hsq x ht.1
  have hCapExt : ContinuousOn capExt (prismCapSet n) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hEq : (prismCapSet n).domRestrict capExt =
        fun z => TopCat.Hom.hom capMap (Homeomorph.ulift.{u, 0}.symm z) := by
      funext z
      simp [Set.domRestrict, capExt, z.2] <;> rfl
    rw [hEq]
    exact capMap.hom.continuous.comp (Homeomorph.ulift.{u, 0}.symm.continuous)
  have hTubeExt : ContinuousOn tubeExt (prismTubeSet n) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hEq : (prismTubeSet n).domRestrict tubeExt =
        fun z => TopCat.Hom.hom tubeMap (Homeomorph.ulift.{u, 0}.symm z) := by
      funext z
      simp [Set.domRestrict, tubeExt, z.2] <;> rfl
    rw [hEq]
    exact tubeMap.hom.continuous.comp (Homeomorph.ulift.{u, 0}.symm.continuous)
  have hSideCap : ContinuousOn sideFun (prismCapSet n) := by
    refine hCapExt.congr ?_
    intro z hz
    simp [sideFun, hz]
  have hSideTube : ContinuousOn sideFun (prismTubeSet n) := by
    refine hTubeExt.congr ?_
    intro z hz
    by_cases hc : z ∈ prismCapSet n
    · simpa [sideFun, hc] using hAgree (z := z) hc hz
    · simp [sideFun, hc]
  have hCapClosed : IsClosed (prismCapSet n) := by
    change IsClosed (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ×ˢ
      ({-1, 1} : Set ℝ))
    have hEnds : IsClosed ({-1, 1} : Set ℝ) := by
      have hFinite : ({-1, 1} : Set ℝ).Finite := by simp
      exact hFinite.isClosed
    exact IsClosed.prod Metric.isClosed_closedBall hEnds
  have hTubeClosed : IsClosed (prismTubeSet n) := by
    change IsClosed (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ×ˢ
      Set.Icc (-1 : ℝ) 1)
    exact IsClosed.prod Metric.isClosed_sphere isClosed_Icc
  have hSide : ContinuousOn sideFun (prismSideSet n) := by
    have h := hSideCap.union_of_isClosed hSideTube hCapClosed hTubeClosed
    simpa [prismSideSet] using h
  have hRestr : Continuous (fun z : ↥(prismSideSet n) => sideFun z) :=
    continuousOn_iff_continuous_restrict.mp hSide
  exact TopCat.ofHom ⟨fun z => sideFun z.down,
    by
      change Continuous
        ((fun z : ↥(prismSideSet n) => sideFun z) ∘ Homeomorph.ulift.{u, 0})
      exact hRestr.comp Homeomorph.ulift.{u, 0}.continuous⟩

lemma prismCellBoundaryMap_comp_cap {n : ℕ} {X P : TopCat.{u}}
    (f : TopCat.diskBoundary.{u} n ⟶ X) (k : TopCat.disk.{u} n ⟶ P) (j : X ⟶ P)
    (hsq : IsPushout (diskBoundaryInclusion.{u} n) f k j) :
    prismCapSideInclusion n ≫ prismCellBoundaryMap f k j hsq =
      (prismCapCoproductIso n).hom ≫ coprod.map k k ≫
        pushout.inr (cylinderEndpointMap X) (coprod.map j j) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  change (prismCellBoundaryMap f k j hsq) (prismCapSideInclusion n z) =
    ((prismCapCoproductIso n).hom ≫ coprod.map k k ≫
      pushout.inr (cylinderEndpointMap X) (coprod.map j j)) z
  rw [prismCapSideInclusion_apply]
  cases z with
  | up z =>
    delta prismCellBoundaryMap
    simp only [TopCat.hom_ofHom, DFunLike.coe, ContinuousMap.coe_mk]
    have hmem : (z : EuclideanSpace ℝ (Fin n) × ℝ) ∈ prismCapSet n := z.2
    simp only [dif_pos hmem]

lemma prismCellBoundaryMap_comp_tube {n : ℕ} {X P : TopCat.{u}}
    (f : TopCat.diskBoundary.{u} n ⟶ X) (k : TopCat.disk.{u} n ⟶ P) (j : X ⟶ P)
    (hsq : IsPushout (diskBoundaryInclusion.{u} n) f k j) :
    prismTubeSideInclusion n ≫ prismCellBoundaryMap f k j hsq =
      (prismTubeBoundaryCylinderIso n).hom ≫ (f ▷ TopCat.I.{u}) ≫
        pushout.inl (cylinderEndpointMap X) (coprod.map j j) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  change (prismCellBoundaryMap f k j hsq) (prismTubeSideInclusion n z) =
    ((prismTubeBoundaryCylinderIso n).hom ≫ (f ▷ TopCat.I.{u}) ≫
      pushout.inl (cylinderEndpointMap X) (coprod.map j j)) z
  rw [prismTubeSideInclusion_apply]
  cases z with
  | up z =>
    delta prismCellBoundaryMap
    simp only [TopCat.hom_ofHom, DFunLike.coe, ContinuousMap.coe_mk]
    by_cases hc : (z : EuclideanSpace ℝ (Fin n) × ℝ) ∈ prismCapSet n
    · simp only [dif_pos hc]
      exact prismCellCapTube_agree_at f k j hsq hc z.2
    · simp only [dif_neg hc, dif_pos z.2]

lemma prismSideInclusion_relativeFiniteCellComplexes (n : ℕ) :
    Top.relativeFiniteCellComplexes.{u} (prismSideInclusion n) := by
  let eP := prismProductDiskIso n
  let eS := prismSideSphereIso n
  have hcomm : prismSideInclusion n ≫ eP.hom =
      eS.hom ≫ diskBoundaryInclusion (n + 1) := by
    apply TopCat.hom_ext
    ext x
    rfl
  have hfactor : prismSideInclusion n =
      eS.hom ≫ diskBoundaryInclusion (n + 1) ≫ eP.inv := by
    calc
      prismSideInclusion n = prismSideInclusion n ≫ (eP.hom ≫ eP.inv) := by simp
      _ = (prismSideInclusion n ≫ eP.hom) ≫ eP.inv := by simp [Category.assoc]
      _ = (eS.hom ≫ diskBoundaryInclusion (n + 1)) ≫ eP.inv := by rw [hcomm]
  have hcell : Top.cellBoundaries.{u} (diskBoundaryInclusion.{u} (n + 1)) := by
    change MorphismProperty.ofHoms (fun m : ℕ => diskBoundaryInclusion.{u} m) _
    exact .mk (n + 1)
  have hbase : Top.relativeFiniteCellComplexes.{u} (diskBoundaryInclusion.{u} (n + 1)) :=
    cellBoundaryPushouts_le_relativeFiniteCellComplexes _ <|
      MorphismProperty.le_pushouts _ _ hcell
  have hm : Top.relativeFiniteCellComplexes.{u}.IsMultiplicative := by
    change ((Top.cellBoundaries.{u}.pushouts ⊔
      MorphismProperty.isomorphisms TopCat.{u}).multiplicativeClosure).IsMultiplicative
    infer_instance
  have hIsoS : Top.relativeFiniteCellComplexes.{u} eS.hom :=
    isomorphisms_le_relativeFiniteCellComplexes _ (by infer_instance)
  have hIsoP : Top.relativeFiniteCellComplexes.{u} eP.inv :=
    isomorphisms_le_relativeFiniteCellComplexes _ (by infer_instance)
  rw [hfactor]
  exact hm.comp_mem (eS.hom ≫ diskBoundaryInclusion (n + 1)) eP.inv
    (hm.comp_mem eS.hom (diskBoundaryInclusion (n + 1)) hIsoS hbase) hIsoP

lemma topTensorProdHomeo_apply (X Y : TopCat.{u}) (z : X ⊗ Y) :
    TopCat.homeoOfIso (topTensorProdIso X Y ≪≫ TopCat.prodIsoProd X Y) z =
      (fst X Y z, snd X Y z) := by
  change (TopCat.prodIsoProd X Y).hom ((topTensorProdIso X Y).hom z) = _
  rw [TopCat.prodIsoProd_hom_apply]
  apply Prod.ext
  · change ((topTensorProdIso X Y).hom ≫ Limits.prod.fst) z = _
    simp [topTensorProdIso]
  · change ((topTensorProdIso X Y).hom ≫ Limits.prod.snd) z = _
    simp [topTensorProdIso]

lemma topTensorIProductIso_whiskerRight_apply {X Y : TopCat.{u}} (f : X ⟶ Y)
    (z : X ⊗ TopCat.I.{u}) :
    (topTensorIProductIso Y).hom ((f ▷ TopCat.I.{u}) z) =
      (f (fst X TopCat.I z), snd X TopCat.I z) := by
  change (TopCat.prodIsoProd Y TopCat.I).hom
      ((topTensorProdIso Y TopCat.I).hom ((f ▷ TopCat.I) z)) = _
  rw [TopCat.prodIsoProd_hom_apply]
  apply Prod.ext
  · change ((Limits.prod.lift (fst Y TopCat.I) (snd Y TopCat.I) ≫
      Limits.prod.fst) ((f ▷ TopCat.I) z)) = _
    rw [Limits.prod.lift_fst]
    change ((f ▷ TopCat.I) ≫ fst Y TopCat.I) z = (fst X TopCat.I ≫ f) z
    rw [CartesianMonoidalCategory.whiskerRight_fst]
  · change ((Limits.prod.lift (fst Y TopCat.I) (snd Y TopCat.I) ≫
      Limits.prod.snd) ((f ▷ TopCat.I) z)) = _
    rw [Limits.prod.lift_snd]
    change ((f ▷ TopCat.I) ≫ snd Y TopCat.I) z = (snd X TopCat.I) z
    rw [CartesianMonoidalCategory.whiskerRight_snd]

lemma topTensorIotaZero_natural {X Y : TopCat.{u}} (f : X ⟶ Y) :
    TopCat.ι₀ ≫ (f ▷ TopCat.I.{u}) = f ≫ TopCat.ι₀ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply (TopCat.homeoOfIso (topTensorIProductIso Y)).injective
  have hright := ConcreteCategory.congr_hom
    (topTensorIotaZero_toProduct (X := Y)) (f x)
  have hfst : fst X TopCat.I (TopCat.ι₀ x) = x := by
    change ((TopCat.ι₀ ≫ fst X TopCat.I) x) = x
    simp [TopCat.ι₀_fst]
  have hsnd : snd X TopCat.I (TopCat.ι₀ x) = 0 := by
    change ((TopCat.ι₀ ≫ snd X TopCat.I) x) = 0
    simp [TopCat.ι₀_snd]
  change (topTensorIProductIso Y).hom ((f ▷ TopCat.I) (TopCat.ι₀ x)) =
    (topTensorIProductIso Y).hom (TopCat.ι₀ (f x))
  calc
    (topTensorIProductIso Y).hom ((f ▷ TopCat.I) (TopCat.ι₀ x)) =
        (f (fst X TopCat.I (TopCat.ι₀ x)), snd X TopCat.I (TopCat.ι₀ x)) :=
      topTensorIProductIso_whiskerRight_apply f (TopCat.ι₀ x)
    _ = (f x, 0) := by rw [hfst, hsnd]
    _ = (topTensorIProductIso Y).hom (TopCat.ι₀ (f x)) := by
      simpa [ConcreteCategory.comp_apply] using hright.symm

lemma topTensorIotaOne_natural {X Y : TopCat.{u}} (f : X ⟶ Y) :
    TopCat.ι₁ ≫ (f ▷ TopCat.I.{u}) = f ≫ TopCat.ι₁ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply (TopCat.homeoOfIso (topTensorIProductIso Y)).injective
  have hright := ConcreteCategory.congr_hom
    (topTensorIotaOne_toProduct (X := Y)) (f x)
  have hfst : fst X TopCat.I (TopCat.ι₁ x) = x := by
    change ((TopCat.ι₁ ≫ fst X TopCat.I) x) = x
    simp [TopCat.ι₁_fst]
  have hsnd : snd X TopCat.I (TopCat.ι₁ x) = 1 := by
    change ((TopCat.ι₁ ≫ snd X TopCat.I) x) = 1
    simp [TopCat.ι₁_snd]
  change (topTensorIProductIso Y).hom ((f ▷ TopCat.I) (TopCat.ι₁ x)) =
    (topTensorIProductIso Y).hom (TopCat.ι₁ (f x))
  calc
    (topTensorIProductIso Y).hom ((f ▷ TopCat.I) (TopCat.ι₁ x)) =
        (f (fst X TopCat.I (TopCat.ι₁ x)), snd X TopCat.I (TopCat.ι₁ x)) :=
      topTensorIProductIso_whiskerRight_apply f (TopCat.ι₁ x)
    _ = (f x, 1) := by rw [hfst, hsnd]
    _ = (topTensorIProductIso Y).hom (TopCat.ι₁ (f x)) := by
      simpa [ConcreteCategory.comp_apply] using hright.symm

lemma cylinderEndpointMap_natural {X Y : TopCat.{u}} (f : X ⟶ Y) :
    cylinderEndpointMap X ≫ (f ▷ TopCat.I.{u}) =
      (coprod.map f f) ≫ cylinderEndpointMap Y := by
  apply coprod.hom_ext
  · simp [cylinderEndpointMap, Category.assoc, topTensorIotaZero_natural]
  · simp [cylinderEndpointMap, Category.assoc, topTensorIotaOne_natural]

noncomputable def prismCellEndpointIntermediateMap {X P : TopCat.{u}} (j : X ⟶ P) :
    pushout (cylinderEndpointMap X) (coprod.map j j) ⟶ P ⊗ TopCat.I.{u} :=
  pushout.desc (j ▷ TopCat.I.{u}) (cylinderEndpointMap P) (cylinderEndpointMap_natural j)

@[reassoc (attr := simp)] lemma prismCellEndpointIntermediateMap_inl
    {X P : TopCat.{u}} (j : X ⟶ P) :
    pushout.inl (cylinderEndpointMap X) (coprod.map j j) ≫
      prismCellEndpointIntermediateMap j = j ▷ TopCat.I.{u} := by
  exact pushout.inl_desc (f := cylinderEndpointMap X) (g := coprod.map j j)
    (j ▷ TopCat.I.{u}) (cylinderEndpointMap P) (cylinderEndpointMap_natural j)

@[reassoc (attr := simp)] lemma prismCellEndpointIntermediateMap_inr
    {X P : TopCat.{u}} (j : X ⟶ P) :
    pushout.inr (cylinderEndpointMap X) (coprod.map j j) ≫
      prismCellEndpointIntermediateMap j = cylinderEndpointMap P := by
  exact pushout.inr_desc (f := cylinderEndpointMap X) (g := coprod.map j j)
    (j ▷ TopCat.I.{u}) (cylinderEndpointMap P) (cylinderEndpointMap_natural j)

lemma prismTubeBoundaryCylinderIso_apply {n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ Metric.sphere 0 1) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    (prismTubeBoundaryCylinderIso n).hom
      (ULift.up (⟨(x, t), ⟨hx, ht⟩⟩ : prismTubeSet n)) =
    (topTensorIProductIso (TopCat.diskBoundary.{u} n)).inv
      (sphereSubtypeHomeomorph n ⟨x, hx⟩, intervalCenteredHomeomorph.symm ⟨t, ht⟩) := by
  change (topTensorIProductIso (TopCat.diskBoundary.{u} n)).inv
      ((Homeomorph.ulift.{u, 0}.trans (prismTubeHomeomorphBoundaryCylinder n))
        (ULift.up (⟨(x, t), ⟨hx, ht⟩⟩ : prismTubeSet n))) = _
  rw [Homeomorph.trans_apply]
  change (topTensorIProductIso (TopCat.diskBoundary.{u} n)).inv
      (prismTubeHomeomorphBoundaryCylinder n ⟨(x, t), ⟨hx, ht⟩⟩) = _
  rw [prismTubeHomeomorphBoundaryCylinder_apply]

lemma diskCylinderPrismIso_inv_apply {n : ℕ} (a : TopCat.disk.{u} n) (t : TopCat.I.{u}) :
    (diskCylinderPrismIso n).inv
      (ULift.up (diskIntervalHomeomorphPrismProduct n (a, t))) =
    (topTensorIProductIso (TopCat.disk.{u} n)).inv (a, t) := by
  let e := topTensorIProductIso (TopCat.disk.{u} n)
  let H : (TopCat.disk.{u} n × TopCat.I.{u}) ≃ₜ
      ULift.{u, 0} (prismProductSet n) :=
    (diskIntervalHomeomorphPrismProduct n).trans Homeomorph.ulift.{u, 0}.symm
  have hcomp : (diskCylinderPrismIso n).inv ≫ e.hom = (TopCat.isoOfHomeo H).inv := by
    simp [diskCylinderPrismIso, e, topTensorIProductIso, Category.assoc]
  apply (TopCat.homeoOfIso e).injective
  change e.hom ((diskCylinderPrismIso n).inv
      (ULift.up (diskIntervalHomeomorphPrismProduct n (a, t)))) =
    e.hom (e.inv (a, t))
  calc
    e.hom ((diskCylinderPrismIso n).inv
        (ULift.up (diskIntervalHomeomorphPrismProduct n (a, t)))) =
      ((diskCylinderPrismIso n).inv ≫ e.hom)
        (ULift.up (diskIntervalHomeomorphPrismProduct n (a, t))) := by
          rw [← ConcreteCategory.comp_apply]
    _ = (TopCat.isoOfHomeo H).inv
        (ULift.up (diskIntervalHomeomorphPrismProduct n (a, t))) := by rw [hcomp]
    _ = (a, t) := by
      change (diskIntervalHomeomorphPrismProduct n).symm
        (diskIntervalHomeomorphPrismProduct n (a, t)) = (a, t)
      exact Homeomorph.symm_apply_apply _ _
    _ = e.hom (e.inv (a, t)) := by
      rw [← ConcreteCategory.comp_apply]
      simp [e]

noncomputable def intervalExponential : TopCat.{u} ⥤ TopCat.{u} where
  obj Y := TopCat.of C(TopCat.I, Y)
  map f := TopCat.ofHom ⟨ContinuousMap.comp f.hom, ContinuousMap.continuous_postcomp f.hom⟩
  map_id := by
    intro X
    apply TopCat.hom_ext
    ext f x
    rfl
  map_comp := by
    intro X Y Z f g
    apply TopCat.hom_ext
    ext h x
    rfl

noncomputable def intervalHomEquiv (X Y : TopCat.{u}) :
    (X ⊗ TopCat.I ⟶ Y) ≃ (X ⟶ intervalExponential.obj Y) := by
  let e : X ⊗ TopCat.I ≅ TopCat.of (X × TopCat.I) :=
    topTensorProdIso X TopCat.I ≪≫ TopCat.prodIsoProd X TopCat.I
  have h₁ (z : X ⊗ TopCat.I) : e.inv.hom (e.hom.hom z) = z := by
    exact ConcreteCategory.congr_hom e.hom_inv_id z
  have h₂ (z : TopCat.of (X × TopCat.I)) : e.hom.hom (e.inv.hom z) = z := by
    exact ConcreteCategory.congr_hom e.inv_hom_id z
  have h₂fun : e.hom.hom.comp e.inv.hom = ContinuousMap.id _ := by
    apply ContinuousMap.ext
    intro z
    exact h₂ z
  refine {
    toFun := fun f => (TopCat.Hom.equivContinuousMap X (intervalExponential.obj Y)).symm ?_
    invFun := fun g => (TopCat.Hom.equivContinuousMap (X ⊗ TopCat.I) Y).symm ?_
    left_inv := ?_
    right_inv := ?_ }
  · change C(X, C(TopCat.I, Y))
    exact ContinuousMap.curry (f.hom.comp e.inv.hom)
  · exact (ContinuousMap.uncurry g.hom).comp e.hom.hom
  · intro f
    apply TopCat.hom_ext
    ext z
    change f.hom (e.inv.hom (e.hom.hom z)) = f.hom z
    rw [h₁ z]
  · intro g
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    apply ContinuousMap.ext
    intro t
    simp [TopCat.Hom.equivContinuousMap, ContinuousMap.curry_apply,
      ContinuousMap.uncurry, ContinuousMap.comp_apply, h₂fun]
    rfl

lemma intervalHomEquiv_apply {X Y : TopCat.{u}} (f : X ⊗ TopCat.I ⟶ Y)
    (x : X) (t : TopCat.I) :
    (let ϕ : C(X, C(TopCat.I, Y)) :=
      TopCat.Hom.equivContinuousMap X (intervalExponential.obj Y)
        (intervalHomEquiv X Y f)
     ϕ x t) =
      f ((topTensorProdIso X TopCat.I ≪≫ TopCat.prodIsoProd X TopCat.I).inv.hom (x, t)) := by
  let e := topTensorProdIso X TopCat.I ≪≫ TopCat.prodIsoProd X TopCat.I
  change (ContinuousMap.curry (f.hom.comp e.inv.hom) x) t = f (e.inv.hom (x, t))
  rw [ContinuousMap.curry_apply, ContinuousMap.comp_apply]

lemma intervalHomEquiv_symm_eq_uncurry {X Y : TopCat.{u}}
    (g : X ⟶ intervalExponential.obj Y) :
    (intervalHomEquiv X Y).symm g =
      (TopCat.Hom.equivContinuousMap (X ⊗ TopCat.I) Y).symm
        ((ContinuousMap.uncurry g.hom).comp
          ((topTensorProdIso X TopCat.I ≪≫ TopCat.prodIsoProd X TopCat.I).hom.hom)) := by
  rfl

lemma intervalHomEquiv_symm_natural_left {X' X Y : TopCat.{u}} (f : X' ⟶ X)
    (g : X ⟶ intervalExponential.obj Y) :
    (intervalHomEquiv X' Y).symm (f ≫ g) =
      (MonoidalCategory.tensorRight TopCat.I).map f ≫ (intervalHomEquiv X Y).symm g := by
  rw [intervalHomEquiv_symm_eq_uncurry, intervalHomEquiv_symm_eq_uncurry]
  let e' := topTensorProdIso X' TopCat.I ≪≫ TopCat.prodIsoProd X' TopCat.I
  let e := topTensorProdIso X TopCat.I ≪≫ TopCat.prodIsoProd X TopCat.I
  have he' (z : X' ⊗ TopCat.I) : e'.hom.hom z = (fst X' TopCat.I z, snd X' TopCat.I z) := by
    change (TopCat.prodIsoProd X' TopCat.I).hom
      ((topTensorProdIso X' TopCat.I).hom z) = _
    rw [TopCat.prodIsoProd_hom_apply]
    apply Prod.ext
    · change (Limits.prod.lift (fst X' TopCat.I) (snd X' TopCat.I) ≫
        Limits.prod.fst) z = _
      rw [Limits.prod.lift_fst]
    · change (Limits.prod.lift (fst X' TopCat.I) (snd X' TopCat.I) ≫
        Limits.prod.snd) z = _
      rw [Limits.prod.lift_snd]
  have he (z : X ⊗ TopCat.I) : e.hom.hom z = (fst X TopCat.I z, snd X TopCat.I z) := by
    change (TopCat.prodIsoProd X TopCat.I).hom
      ((topTensorProdIso X TopCat.I).hom z) = _
    rw [TopCat.prodIsoProd_hom_apply]
    apply Prod.ext
    · change (Limits.prod.lift (fst X TopCat.I) (snd X TopCat.I) ≫
        Limits.prod.fst) z = _
      rw [Limits.prod.lift_fst]
    · change (Limits.prod.lift (fst X TopCat.I) (snd X TopCat.I) ≫
        Limits.prod.snd) z = _
      rw [Limits.prod.lift_snd]
  have heF (z : X' ⊗ TopCat.I) :
      e.hom.hom ((f ▷ TopCat.I) z) =
        (f (fst X' TopCat.I z), snd X' TopCat.I z) := by
    change (TopCat.prodIsoProd X TopCat.I).hom
      ((topTensorProdIso X TopCat.I).hom ((f ▷ TopCat.I) z)) = _
    rw [TopCat.prodIsoProd_hom_apply]
    apply Prod.ext
    · change ((Limits.prod.lift (fst X TopCat.I) (snd X TopCat.I) ≫
        Limits.prod.fst) ((f ▷ TopCat.I) z)) = _
      rw [Limits.prod.lift_fst]
      change ((f ▷ TopCat.I) ≫ fst X TopCat.I) z =
        (fst X' TopCat.I ≫ f) z
      rw [CartesianMonoidalCategory.whiskerRight_fst]
    · change ((Limits.prod.lift (fst X TopCat.I) (snd X TopCat.I) ≫
        Limits.prod.snd) ((f ▷ TopCat.I) z)) = _
      rw [Limits.prod.lift_snd]
      change ((f ▷ TopCat.I) ≫ snd X TopCat.I) z = (snd X' TopCat.I) z
      rw [CartesianMonoidalCategory.whiskerRight_snd]
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  change (ContinuousMap.uncurry (g.hom.comp f.hom)).comp e'.hom.hom z =
    (ContinuousMap.uncurry g.hom).comp e.hom.hom ((f ▷ TopCat.I) z)
  rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply, he' z, heF z]
  rfl

lemma intervalHomEquiv_natural_right {X Y Y' : TopCat.{u}} (f : X ⊗ TopCat.I ⟶ Y)
    (g : Y ⟶ Y') :
    intervalHomEquiv X Y' (f ≫ g) =
      intervalHomEquiv X Y f ≫ intervalExponential.map g := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro t
  let e := topTensorProdIso X TopCat.I ≪≫ TopCat.prodIsoProd X TopCat.I
  change (ContinuousMap.curry ((g.hom.comp f.hom).comp e.inv.hom) x) t =
    (ContinuousMap.comp g.hom ((ContinuousMap.curry (f.hom.comp e.inv.hom)) x)) t
  simp [ContinuousMap.curry_apply, ContinuousMap.comp_apply]

noncomputable def intervalTensorAdjunction :
    MonoidalCategory.tensorRight TopCat.I ⊣ intervalExponential :=
  Adjunction.mkOfHomEquiv {
    homEquiv := intervalHomEquiv
    homEquiv_naturality_left_symm := intervalHomEquiv_symm_natural_left
    homEquiv_naturality_right := intervalHomEquiv_natural_right }

lemma tensorRightI_map_isPushout {A B C P : TopCat.{u}} {f : A ⟶ B} {g : A ⟶ C}
    {k : B ⟶ P} {j : C ⟶ P} (h : IsPushout f g k j) :
    IsPushout (f ▷ TopCat.I) (g ▷ TopCat.I) (k ▷ TopCat.I) (j ▷ TopCat.I) := by
  let F : TopCat.{u} ⥤ TopCat.{u} := MonoidalCategory.tensorRight TopCat.I
  letI : PreservesColimitsOfShape WalkingSpan F :=
    intervalTensorAdjunction.leftAdjoint_preservesColimits.preservesColimitsOfShape
  exact Functor.map_isPushout F h

lemma prismCapSideInclusion_toDiskCylinder {n : ℕ} :
    prismCapSideInclusion n ≫ prismSideInclusion n ≫ (diskCylinderPrismIso n).inv =
      (prismCapCoproductIso n).hom ≫ cylinderEndpointMap (TopCat.disk.{u} n) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  change (diskCylinderPrismIso n).inv
      (prismSideInclusion n (prismCapSideInclusion n z)) =
    (cylinderEndpointMap (TopCat.disk.{u} n)) ((prismCapCoproductIso n).hom z)
  cases z with
  | up z =>
    rcases z with ⟨⟨x, t⟩, hz⟩
    change x ∈ Metric.closedBall 0 1 ∧ t ∈ ({-1, 1} : Set ℝ) at hz
    rcases Set.mem_insert_iff.mp hz.2 with htNeg | htOne
    · subst t
      let a : TopCat.disk.{u} n := diskSubtypeHomeomorph n ⟨x, hz.1⟩
      have ha : a.1.1 = x := by rfl
      have hbody : (⟨(x, -1), ⟨hz.1, by norm_num⟩⟩ : prismProductSet n) =
          diskIntervalHomeomorphPrismProduct n (a, 0) := by
        apply Subtype.ext
        rw [diskIntervalHomeomorphPrismProduct_zero]
        apply Prod.ext
        · exact ha.symm
        · rfl
      rw [prismCapSideInclusion_apply, prismSideInclusion_apply]
      rw [show (ULift.up ⟨(x, -1), prismSideSet_subset_product n (Or.inl hz)⟩ :
          ULift.{u, 0} (prismProductSet n)) = ULift.up ⟨(x, -1),
            ⟨hz.1, by norm_num⟩⟩ by congr 2]
      rw [show (⟨(x, -1), ⟨hz.1, by norm_num⟩⟩ : prismProductSet n) =
          diskIntervalHomeomorphPrismProduct n (a, 0) by exact hbody]
      rw [diskCylinderPrismIso_inv_apply]
      rw [prismCapCoproductIso_apply_neg x hz.1]
      have hι₀ : (topTensorIProductIso (TopCat.disk.{u} n)).inv (a, 0) = TopCat.ι₀ a := by
        have h := ConcreteCategory.congr_hom
          (topTensorIotaZero_fromProduct (X := TopCat.disk.{u} n)) a
        simpa [ConcreteCategory.comp_apply] using h
      simpa [ConcreteCategory.comp_apply, cylinderEndpointMap] using hι₀
    · have htEq := Set.mem_singleton_iff.mp htOne
      subst t
      let a : TopCat.disk.{u} n := diskSubtypeHomeomorph n ⟨x, hz.1⟩
      have ha : a.1.1 = x := by rfl
      have hbody : (⟨(x, 1), ⟨hz.1, by norm_num⟩⟩ : prismProductSet n) =
          diskIntervalHomeomorphPrismProduct n (a, 1) := by
        apply Subtype.ext
        rw [diskIntervalHomeomorphPrismProduct_one]
        apply Prod.ext
        · exact ha.symm
        · rfl
      rw [prismCapSideInclusion_apply, prismSideInclusion_apply]
      rw [show (ULift.up ⟨(x, 1), prismSideSet_subset_product n (Or.inl hz)⟩ :
          ULift.{u, 0} (prismProductSet n)) = ULift.up ⟨(x, 1),
            ⟨hz.1, by norm_num⟩⟩ by congr 2]
      rw [show (⟨(x, 1), ⟨hz.1, by norm_num⟩⟩ : prismProductSet n) =
          diskIntervalHomeomorphPrismProduct n (a, 1) by exact hbody]
      rw [diskCylinderPrismIso_inv_apply]
      rw [prismCapCoproductIso_apply_one x hz.1]
      have hι₁ : (topTensorIProductIso (TopCat.disk.{u} n)).inv (a, 1) = TopCat.ι₁ a := by
        have h := ConcreteCategory.congr_hom
          (topTensorIotaOne_fromProduct (X := TopCat.disk.{u} n)) a
        simpa [ConcreteCategory.comp_apply] using h
      simpa [ConcreteCategory.comp_apply, cylinderEndpointMap] using hι₁

lemma prismCapSideIntoDiskCylinder {n : ℕ} :
    prismCapSideInclusion n ≫ prismSideInclusion n =
      (prismCapCoproductIso n).hom ≫ cylinderEndpointMap (TopCat.disk.{u} n) ≫
        (diskCylinderPrismIso n).hom := by
  calc
    prismCapSideInclusion n ≫ prismSideInclusion n =
      (prismCapSideInclusion n ≫ prismSideInclusion n ≫ (diskCylinderPrismIso n).inv) ≫
        (diskCylinderPrismIso n).hom := by simp [Category.assoc]
    _ = ((prismCapCoproductIso n).hom ≫ cylinderEndpointMap (TopCat.disk.{u} n)) ≫
        (diskCylinderPrismIso n).hom := by rw [prismCapSideInclusion_toDiskCylinder]
    _ = (prismCapCoproductIso n).hom ≫ cylinderEndpointMap (TopCat.disk.{u} n) ≫
        (diskCylinderPrismIso n).hom := by rw [Category.assoc]

lemma prismTubeSideInclusion_toDiskCylinder {n : ℕ} :
    prismTubeSideInclusion n ≫ prismSideInclusion n ≫ (diskCylinderPrismIso n).inv =
      (prismTubeBoundaryCylinderIso n).hom ≫
        (diskBoundaryInclusion.{u} n ▷ TopCat.I.{u}) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  change (diskCylinderPrismIso n).inv
      (prismSideInclusion n (prismTubeSideInclusion n z)) =
    ((prismTubeBoundaryCylinderIso n).hom ≫
      (diskBoundaryInclusion n ▷ TopCat.I.{u})) z
  rw [prismTubeSideInclusion_apply, prismSideInclusion_apply]
  cases z with
  | up z =>
    rcases z with ⟨⟨x, t⟩, hz⟩
    change x ∈ Metric.sphere 0 1 ∧ t ∈ Set.Icc (-1 : ℝ) 1 at hz
    let b : TopCat.diskBoundary.{u} n := sphereSubtypeHomeomorph.{u} n ⟨x, hz.1⟩
    let a : TopCat.disk.{u} n := diskBoundaryInclusion.{u} n b
    let tI : TopCat.I.{u} := intervalCenteredHomeomorph.symm ⟨t, hz.2⟩
    have hxD : x ∈ Metric.closedBall 0 1 := Metric.sphere_subset_closedBall hz.1
    have ha : a.1.1 = x := by
      change (diskBoundaryInclusion.{u} n (sphereSubtypeHomeomorph.{u} n ⟨x, hz.1⟩)).1.1 = x
      rw [diskBoundaryInclusion_apply_sphere]
      rfl
    have hbody : (⟨(x, t), ⟨hxD, hz.2⟩⟩ : prismProductSet n) =
        diskIntervalHomeomorphPrismProduct n (a, tI) := by
      apply Subtype.ext
      rw [diskIntervalHomeomorphPrismProduct_val]
      change (x, t) = (a.1.1, (intervalCenteredHomeomorph tI).1)
      rw [ha]
      simp [tI]
    have hbodyULift : (ULift.up ⟨(x, t), prismSideSet_subset_product n (Or.inr hz)⟩ :
        ULift.{u, 0} (prismProductSet n)) =
        ULift.up (⟨(x, t), ⟨hxD, hz.2⟩⟩ : prismProductSet n) := by
      congr 2
    rw [hbodyULift, hbody, diskCylinderPrismIso_inv_apply,
      TopCat.comp_app, prismTubeBoundaryCylinderIso_apply x hz.1 t hz.2]
    let eD := topTensorIProductIso (TopCat.disk.{u} n)
    let eB := topTensorIProductIso (TopCat.diskBoundary.{u} n)
    have hcoords :
        (fst (TopCat.diskBoundary.{u} n) TopCat.I.{u} (eB.inv (b, tI)),
          snd (TopCat.diskBoundary.{u} n) TopCat.I.{u} (eB.inv (b, tI))) = (b, tI) := by
      rw [← topTensorProdHomeo_apply (TopCat.diskBoundary.{u} n) TopCat.I.{u} (eB.inv (b, tI))]
      exact (TopCat.homeoOfIso eB).apply_symm_apply (b, tI)
    have hLeft : (TopCat.homeoOfIso eD) (eD.inv (a, tI)) = (a, tI) :=
      (TopCat.homeoOfIso eD).apply_symm_apply (a, tI)
    have hRight : (TopCat.homeoOfIso eD)
        ((diskBoundaryInclusion n ▷ TopCat.I) (eB.inv (b, tI))) = (a, tI) := by
      change (topTensorIProductIso (TopCat.disk.{u} n)).hom
        ((diskBoundaryInclusion.{u} n ▷ TopCat.I.{u}) (eB.inv (b, tI))) = (a, tI)
      calc
        (topTensorIProductIso (TopCat.disk.{u} n)).hom
            ((diskBoundaryInclusion n ▷ TopCat.I) (eB.inv (b, tI))) =
          (diskBoundaryInclusion n
            (fst (TopCat.diskBoundary.{u} n) TopCat.I.{u} (eB.inv (b, tI))),
            snd (TopCat.diskBoundary.{u} n) TopCat.I.{u} (eB.inv (b, tI))) :=
          topTensorIProductIso_whiskerRight_apply (f := diskBoundaryInclusion.{u} n)
            (z := eB.inv (b, tI))
        _ = (a, tI) := by
          have hfst : fst (TopCat.diskBoundary.{u} n) TopCat.I.{u} (eB.inv (b, tI)) = b := by
            simpa using congrArg Prod.fst hcoords
          have hsnd : snd (TopCat.diskBoundary.{u} n) TopCat.I.{u} (eB.inv (b, tI)) = tI := by
            simpa using congrArg Prod.snd hcoords
          rw [hfst, hsnd]
    apply (TopCat.homeoOfIso eD).injective
    exact hLeft.trans hRight.symm

lemma prismTubeBoundary_intoDiskCylinder {n : ℕ} :
    (prismTubeBoundaryCylinderIso n).inv ≫ prismTubeSideInclusion n ≫
      prismSideInclusion n =
      (diskBoundaryInclusion.{u} n ▷ TopCat.I.{u}) ≫ (diskCylinderPrismIso n).hom := by
  have hTube := prismTubeSideInclusion_toDiskCylinder (n := n)
  calc
    (prismTubeBoundaryCylinderIso n).inv ≫ prismTubeSideInclusion n ≫
        prismSideInclusion n =
      ((prismTubeBoundaryCylinderIso n).inv ≫ prismTubeSideInclusion n ≫
        prismSideInclusion n ≫ (diskCylinderPrismIso n).inv) ≫
          (diskCylinderPrismIso n).hom := by simp [Category.assoc]
    _ = ((prismTubeBoundaryCylinderIso n).inv ≫
          ((prismTubeBoundaryCylinderIso n).hom ≫ (diskBoundaryInclusion.{u} n ▷ TopCat.I.{u}))) ≫
            (diskCylinderPrismIso n).hom := by
          exact congrArg
            (fun g => ((prismTubeBoundaryCylinderIso n).inv ≫ g) ≫ (diskCylinderPrismIso n).hom)
            hTube
    _ = (diskBoundaryInclusion.{u} n ▷ TopCat.I.{u}) ≫ (diskCylinderPrismIso n).hom := by
          simp [Category.assoc]

lemma prismCellBoundaryMap_square_commutes {n : ℕ} {X P : TopCat.{u}}
    (f : TopCat.diskBoundary.{u} n ⟶ X) (k : TopCat.disk.{u} n ⟶ P) (j : X ⟶ P)
    (hsq : IsPushout (diskBoundaryInclusion n) f k j) :
    prismSideInclusion n ≫ (diskCylinderPrismIso n).inv ≫ (k ▷ TopCat.I.{u}) =
      prismCellBoundaryMap f k j hsq ≫ prismCellEndpointIntermediateMap j := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  cases z with
  | up z =>
    rcases z with ⟨p, hp⟩
    rcases hp with hc | ht
    · let zc : ULift.{u, 0} (prismCapSet n) := ULift.up ⟨p, hc⟩
      have hz : prismCapSideInclusion n zc = ULift.up ⟨p, Or.inl hc⟩ :=
        prismCapSideInclusion_apply zc
      have hCapEq :
          prismCapSideInclusion n ≫ prismSideInclusion n ≫ (diskCylinderPrismIso n).inv ≫
              (k ▷ TopCat.I.{u}) =
            prismCapSideInclusion n ≫ prismCellBoundaryMap f k j hsq ≫
              prismCellEndpointIntermediateMap j := by
        calc
          prismCapSideInclusion n ≫ prismSideInclusion n ≫ (diskCylinderPrismIso n).inv ≫
              (k ▷ TopCat.I.{u}) =
            (prismCapSideInclusion n ≫ prismSideInclusion n ≫ (diskCylinderPrismIso n).inv) ≫
              (k ▷ TopCat.I.{u}) := by simp [Category.assoc]
          _ = ((prismCapCoproductIso n).hom ≫ cylinderEndpointMap (TopCat.disk.{u} n)) ≫
              (k ▷ TopCat.I.{u}) := by rw [prismCapSideInclusion_toDiskCylinder]
          _ = (prismCapCoproductIso n).hom ≫
              (cylinderEndpointMap (TopCat.disk.{u} n) ≫ (k ▷ TopCat.I.{u})) := by
                simp [Category.assoc]
          _ = (prismCapCoproductIso n).hom ≫
              (coprod.map k k ≫ cylinderEndpointMap P) := by
                rw [cylinderEndpointMap_natural]
          _ = (prismCapCoproductIso n).hom ≫
              (coprod.map k k ≫
                (pushout.inr (cylinderEndpointMap X) (coprod.map j j) ≫
                  prismCellEndpointIntermediateMap j)) := by
                rw [prismCellEndpointIntermediateMap_inr]
          _ = (prismCapCoproductIso n).hom ≫ coprod.map k k ≫
              pushout.inr (cylinderEndpointMap X) (coprod.map j j) ≫
                prismCellEndpointIntermediateMap j := by
                  rw [← Category.assoc, ← Category.assoc]
          _ = (prismCapSideInclusion n ≫ prismCellBoundaryMap f k j hsq) ≫
              prismCellEndpointIntermediateMap j := by
                have h := congrArg (fun g => g ≫ prismCellEndpointIntermediateMap j)
                  (prismCellBoundaryMap_comp_cap f k j hsq).symm
                simpa [Category.assoc] using h
          _ = prismCapSideInclusion n ≫ prismCellBoundaryMap f k j hsq ≫
              prismCellEndpointIntermediateMap j := rfl
      have hPoint := ConcreteCategory.congr_hom hCapEq zc
      simpa [ConcreteCategory.comp_apply, hz] using hPoint
    · let zt : ULift.{u, 0} (prismTubeSet n) := ULift.up ⟨p, ht⟩
      have hz : prismTubeSideInclusion n zt = ULift.up ⟨p, Or.inr ht⟩ :=
        prismTubeSideInclusion_apply zt
      have hTubeEq :
          prismTubeSideInclusion n ≫ prismSideInclusion n ≫ (diskCylinderPrismIso n).inv ≫
              (k ▷ TopCat.I.{u}) =
            prismTubeSideInclusion n ≫ prismCellBoundaryMap f k j hsq ≫
              prismCellEndpointIntermediateMap j := by
        calc
          prismTubeSideInclusion n ≫ prismSideInclusion n ≫ (diskCylinderPrismIso n).inv ≫
              (k ▷ TopCat.I.{u}) =
            (prismTubeSideInclusion n ≫ prismSideInclusion n ≫ (diskCylinderPrismIso n).inv) ≫
              (k ▷ TopCat.I.{u}) := by simp [Category.assoc]
          _ = ((prismTubeBoundaryCylinderIso n).hom ≫
              (diskBoundaryInclusion n ▷ TopCat.I.{u})) ≫ (k ▷ TopCat.I.{u}) := by
                rw [prismTubeSideInclusion_toDiskCylinder]
          _ = (prismTubeBoundaryCylinderIso n).hom ≫
              ((diskBoundaryInclusion n ▷ TopCat.I.{u}) ≫ (k ▷ TopCat.I.{u})) := by
                simp [Category.assoc]
          _ = (prismTubeBoundaryCylinderIso n).hom ≫
              ((f ▷ TopCat.I.{u}) ≫ (j ▷ TopCat.I.{u})) := by
                rw [(tensorRightI_map_isPushout hsq).w]
          _ = (prismTubeBoundaryCylinderIso n).hom ≫ (f ▷ TopCat.I.{u}) ≫
              (pushout.inl (cylinderEndpointMap X) (coprod.map j j) ≫
                prismCellEndpointIntermediateMap j) := by
                rw [prismCellEndpointIntermediateMap_inl]
          _ = ((prismTubeBoundaryCylinderIso n).hom ≫ (f ▷ TopCat.I.{u}) ≫
              pushout.inl (cylinderEndpointMap X) (coprod.map j j)) ≫
                prismCellEndpointIntermediateMap j := by
                exact congrArg (fun g => g ≫ prismCellEndpointIntermediateMap j)
                  (Category.assoc (prismTubeBoundaryCylinderIso n).hom
                    (f ▷ TopCat.I.{u})
                    (pushout.inl (cylinderEndpointMap X) (coprod.map j j)))
          _ = (prismTubeSideInclusion n ≫ prismCellBoundaryMap f k j hsq) ≫
              prismCellEndpointIntermediateMap j := by
                have h := congrArg (fun g => g ≫ prismCellEndpointIntermediateMap j)
                  (prismCellBoundaryMap_comp_tube f k j hsq).symm
                simpa [Category.assoc] using h
          _ = prismTubeSideInclusion n ≫ prismCellBoundaryMap f k j hsq ≫
              prismCellEndpointIntermediateMap j := by
                exact Category.assoc (prismTubeSideInclusion n)
                  (prismCellBoundaryMap f k j hsq) (prismCellEndpointIntermediateMap j)
      have hPoint := ConcreteCategory.congr_hom hTubeEq zt
      simpa [ConcreteCategory.comp_apply, hz] using hPoint

lemma prismCellAttachedCylinder_existsDesc {n : ℕ} {X P : TopCat.{u}}
    (f : TopCat.diskBoundary.{u} n ⟶ X) (k : TopCat.disk.{u} n ⟶ P) (j : X ⟶ P)
    (hsq : IsPushout (diskBoundaryInclusion.{u} n) f k j)
    (s : PushoutCocone (prismSideInclusion n) (prismCellBoundaryMap f k j hsq)) :
    ∃ l : P ⊗ TopCat.I.{u} ⟶ s.pt,
      ((diskCylinderPrismIso n).inv ≫ (k ▷ TopCat.I.{u})) ≫ l = s.inl ∧
        prismCellEndpointIntermediateMap j ≫ l = s.inr := by
  let eX := cylinderEndpointMap X
  let jsum := coprod.map j j
  let rX := pushout.inl eX jsum
  let rP := pushout.inr eX jsum
  let hR : IsPushout eX jsum rX rP := IsPushout.of_hasPushout eX jsum
  let hTensor := tensorRightI_map_isPushout hsq
  let dDisk : TopCat.disk.{u} n ⊗ TopCat.I.{u} ⟶ s.pt :=
    (diskCylinderPrismIso n).hom ≫ s.inl
  let dX : X ⊗ TopCat.I.{u} ⟶ s.pt := rX ≫ s.inr
  have hTubeBody :
      ((prismTubeBoundaryCylinderIso n).inv ≫ prismTubeSideInclusion n ≫
        prismSideInclusion n) ≫ s.inl =
      (diskBoundaryInclusion n ▷ TopCat.I.{u}) ≫ dDisk := by
    calc
      ((prismTubeBoundaryCylinderIso n).inv ≫ prismTubeSideInclusion n ≫
          prismSideInclusion n) ≫ s.inl =
        ((diskBoundaryInclusion n ▷ TopCat.I.{u}) ≫ (diskCylinderPrismIso n).hom) ≫ s.inl := by
          rw [prismTubeBoundary_intoDiskCylinder]
      _ = (diskBoundaryInclusion n ▷ TopCat.I.{u}) ≫ dDisk := by
          simp [dDisk, Category.assoc]
  have hTubeCompat : (diskBoundaryInclusion.{u} n ▷ TopCat.I.{u}) ≫ dDisk =
      (f ▷ TopCat.I.{u}) ≫ dX := by
    calc
      (diskBoundaryInclusion.{u} n ▷ TopCat.I.{u}) ≫ dDisk =
          ((prismTubeBoundaryCylinderIso n).inv ≫ prismTubeSideInclusion n ≫
            prismSideInclusion n) ≫ s.inl := by
              exact hTubeBody.symm
      _ = (prismTubeBoundaryCylinderIso n).inv ≫ prismTubeSideInclusion n ≫
            (prismSideInclusion n ≫ s.inl) := by simp [Category.assoc]
      _ = (prismTubeBoundaryCylinderIso n).inv ≫ prismTubeSideInclusion n ≫
            (prismCellBoundaryMap f k j hsq ≫ s.inr) := by rw [s.condition]
      _ = (prismTubeBoundaryCylinderIso n).inv ≫
            (prismTubeSideInclusion n ≫ prismCellBoundaryMap f k j hsq) ≫ s.inr := by
              simp [Category.assoc]
      _ = (prismTubeBoundaryCylinderIso n).inv ≫
            ((prismTubeBoundaryCylinderIso n).hom ≫ (f ▷ TopCat.I.{u}) ≫ rX) ≫ s.inr := by
              rw [prismCellBoundaryMap_comp_tube]
      _ = (f ▷ TopCat.I.{u}) ≫ dX := by simp [dX, Category.assoc]
  let d : P ⊗ TopCat.I.{u} ⟶ s.pt := hTensor.desc dDisk dX hTubeCompat
  have hCapData : cylinderEndpointMap (TopCat.disk.{u} n) ≫ dDisk =
      (coprod.map k k) ≫ rP ≫ s.inr := by
    have hCapPost : (prismCapCoproductIso n).hom ≫
        (cylinderEndpointMap (TopCat.disk.{u} n) ≫ dDisk) =
        (prismCapCoproductIso n).hom ≫ ((coprod.map k k) ≫ rP ≫ s.inr) := by
      calc
        (prismCapCoproductIso n).hom ≫ cylinderEndpointMap (TopCat.disk.{u} n) ≫ dDisk =
            (prismCapSideInclusion n ≫ prismSideInclusion n) ≫ s.inl := by
              simp [dDisk, Category.assoc]
              simpa [Category.assoc] using
                congrArg (fun g => g ≫ s.inl)
                  (prismCapSideIntoDiskCylinder (n := n)).symm
        _ = prismCapSideInclusion n ≫ prismCellBoundaryMap f k j hsq ≫ s.inr := by
              rw [Category.assoc, s.condition, ← Category.assoc]
        _ = (prismCapCoproductIso n).hom ≫ coprod.map k k ≫ rP ≫ s.inr := by
              exact congrArg (fun g => g ≫ s.inr) (prismCellBoundaryMap_comp_cap f k j hsq)
    exact (cancel_epi (prismCapCoproductIso n).hom).1 hCapPost
  have hBodyFac : ((diskCylinderPrismIso n).inv ≫ (k ▷ TopCat.I.{u})) ≫ d = s.inl := by
    calc
      ((diskCylinderPrismIso n).inv ≫ (k ▷ TopCat.I.{u})) ≫ d =
          (diskCylinderPrismIso n).inv ≫ ((k ▷ TopCat.I.{u}) ≫ d) := by simp [Category.assoc]
      _ = (diskCylinderPrismIso n).inv ≫ dDisk := by rw [hTensor.inl_desc]
      _ = (diskCylinderPrismIso n).inv ≫ (diskCylinderPrismIso n).hom ≫ s.inl := rfl
      _ = s.inl := by simp [Category.assoc]
  have hRZero : TopCat.ι₀ ≫ rX = j ≫ coprod.inl ≫ rP := by
    have h := congrArg (fun g : X ⨿ X ⟶ pushout eX jsum =>
      (coprod.inl : X ⟶ X ⨿ X) ≫ g) hR.w
    change (coprod.inl ≫ cylinderEndpointMap X) ≫ rX =
      (coprod.inl ≫ coprod.map j j) ≫ rP at h
    rw [cylinderEndpointMap, coprod.inl_desc, coprod.inl_map] at h
    exact h
  have hROne : TopCat.ι₁ ≫ rX = j ≫ coprod.inr ≫ rP := by
    have h := congrArg (fun g : X ⨿ X ⟶ pushout eX jsum =>
      (coprod.inr : X ⟶ X ⨿ X) ≫ g) hR.w
    change (coprod.inr ≫ cylinderEndpointMap X) ≫ rX =
      (coprod.inr ≫ coprod.map j j) ≫ rP at h
    rw [cylinderEndpointMap, coprod.inr_desc, coprod.inr_map] at h
    exact h
  have hCapZero : TopCat.ι₀ ≫ dDisk = k ≫ coprod.inl ≫ rP ≫ s.inr := by
    have h := congrArg (fun g : TopCat.disk.{u} n ⨿ TopCat.disk.{u} n ⟶ s.pt =>
      (coprod.inl : TopCat.disk.{u} n ⟶ TopCat.disk.{u} n ⨿ TopCat.disk.{u} n) ≫ g)
      hCapData
    simpa [cylinderEndpointMap, Category.assoc] using h
  have hCapOne : TopCat.ι₁ ≫ dDisk = k ≫ coprod.inr ≫ rP ≫ s.inr := by
    have h := congrArg (fun g : TopCat.disk.{u} n ⨿ TopCat.disk.{u} n ⟶ s.pt =>
      (coprod.inr : TopCat.disk.{u} n ⟶ TopCat.disk.{u} n ⨿ TopCat.disk.{u} n) ≫ g)
      hCapData
    simpa [cylinderEndpointMap, Category.assoc] using h
  have hPZero :
      (coprod.inl : P ⟶ P ⨿ P) ≫ cylinderEndpointMap P ≫ d =
        (coprod.inl : P ⟶ P ⨿ P) ≫ rP ≫ s.inr := by
    apply hsq.hom_ext
    · calc
        k ≫ coprod.inl ≫ cylinderEndpointMap P ≫ d =
            (k ≫ TopCat.ι₀) ≫ d := by simp [Category.assoc, cylinderEndpointMap]
        _ = (TopCat.ι₀ ≫ (k ▷ TopCat.I.{u})) ≫ d := by
              rw [← topTensorIotaZero_natural (f := k)]
        _ = TopCat.ι₀ ≫ dDisk := by
              change TopCat.ι₀ ≫ (k ▷ TopCat.I.{u}) ≫
                hTensor.desc dDisk dX hTubeCompat = _
              rw [hTensor.inl_desc dDisk dX hTubeCompat]
        _ = k ≫ coprod.inl ≫ rP ≫ s.inr := hCapZero
    · calc
        j ≫ coprod.inl ≫ cylinderEndpointMap P ≫ d =
            (j ≫ TopCat.ι₀) ≫ d := by simp [Category.assoc, cylinderEndpointMap]
        _ = (TopCat.ι₀ ≫ (j ▷ TopCat.I.{u})) ≫ d := by
              rw [← topTensorIotaZero_natural (f := j)]
        _ = TopCat.ι₀ ≫ dX := by
              change TopCat.ι₀ ≫ (j ▷ TopCat.I.{u}) ≫
                hTensor.desc dDisk dX hTubeCompat = _
              rw [hTensor.inr_desc dDisk dX hTubeCompat]
        _ = j ≫ coprod.inl ≫ rP ≫ s.inr := by
              simpa [Category.assoc] using congrArg (fun g => g ≫ s.inr) hRZero
  have hPOne :
      (coprod.inr : P ⟶ P ⨿ P) ≫ cylinderEndpointMap P ≫ d =
        (coprod.inr : P ⟶ P ⨿ P) ≫ rP ≫ s.inr := by
    apply hsq.hom_ext
    · calc
        k ≫ coprod.inr ≫ cylinderEndpointMap P ≫ d =
            (k ≫ TopCat.ι₁) ≫ d := by simp [Category.assoc, cylinderEndpointMap]
        _ = (TopCat.ι₁ ≫ (k ▷ TopCat.I.{u})) ≫ d := by
              rw [← topTensorIotaOne_natural (f := k)]
        _ = TopCat.ι₁ ≫ dDisk := by
              change TopCat.ι₁ ≫ (k ▷ TopCat.I.{u}) ≫
                hTensor.desc dDisk dX hTubeCompat = _
              rw [hTensor.inl_desc dDisk dX hTubeCompat]
        _ = k ≫ coprod.inr ≫ rP ≫ s.inr := hCapOne
    · calc
        j ≫ coprod.inr ≫ cylinderEndpointMap P ≫ d =
            (j ≫ TopCat.ι₁) ≫ d := by simp [Category.assoc, cylinderEndpointMap]
        _ = (TopCat.ι₁ ≫ (j ▷ TopCat.I.{u})) ≫ d := by
              rw [← topTensorIotaOne_natural (f := j)]
        _ = TopCat.ι₁ ≫ dX := by
              change TopCat.ι₁ ≫ (j ▷ TopCat.I.{u}) ≫
                hTensor.desc dDisk dX hTubeCompat = _
              rw [hTensor.inr_desc dDisk dX hTubeCompat]
        _ = j ≫ coprod.inr ≫ rP ≫ s.inr := by
              simpa [Category.assoc] using congrArg (fun g => g ≫ s.inr) hROne
  have hRP : cylinderEndpointMap P ≫ d = rP ≫ s.inr := by
    apply coprod.hom_ext
    · exact hPZero
    · exact hPOne
  have hRFac : prismCellEndpointIntermediateMap j ≫ d = s.inr := by
    apply hR.hom_ext
    · calc
        rX ≫ prismCellEndpointIntermediateMap j ≫ d =
            (rX ≫ prismCellEndpointIntermediateMap j) ≫ d := by simp [Category.assoc]
        _ = (j ▷ TopCat.I.{u}) ≫ d := by rw [prismCellEndpointIntermediateMap_inl]
        _ = rX ≫ s.inr := by
              rw [hTensor.inr_desc dDisk dX hTubeCompat]
    · calc
        rP ≫ prismCellEndpointIntermediateMap j ≫ d =
            (rP ≫ prismCellEndpointIntermediateMap j) ≫ d := by simp [Category.assoc]
        _ = cylinderEndpointMap P ≫ d := by rw [prismCellEndpointIntermediateMap_inr]
        _ = rP ≫ s.inr := hRP
  exact ⟨d, hBodyFac, hRFac⟩

lemma prismCellAttachedCylinder_isPushout {n : ℕ} {X P : TopCat.{u}}
    (f : TopCat.diskBoundary.{u} n ⟶ X) (k : TopCat.disk.{u} n ⟶ P) (j : X ⟶ P)
    (hsq : IsPushout (diskBoundaryInclusion.{u} n) f k j) :
    IsPushout (prismSideInclusion n) (prismCellBoundaryMap f k j hsq)
      ((diskCylinderPrismIso n).inv ≫ (k ▷ TopCat.I.{u}))
      (prismCellEndpointIntermediateMap j) := by
  refine IsPushout.mk' (prismCellBoundaryMap_square_commutes f k j hsq) ?_ ?_
  · intro T φ ψ hBody hR
    apply (tensorRightI_map_isPushout hsq).hom_ext
    · have hDisk : (k ▷ TopCat.I.{u}) ≫ φ = (k ▷ TopCat.I.{u}) ≫ ψ := by
        have h := congrArg (fun m => (diskCylinderPrismIso n).hom ≫ m) hBody
        simpa [Category.assoc] using h
      exact hDisk
    · calc
        (j ▷ TopCat.I.{u}) ≫ φ =
            (pushout.inl (cylinderEndpointMap X) (coprod.map j j) ≫
              prismCellEndpointIntermediateMap j) ≫ φ := by
                rw [prismCellEndpointIntermediateMap_inl]
        _ = pushout.inl (cylinderEndpointMap X) (coprod.map j j) ≫
              prismCellEndpointIntermediateMap j ≫ φ := by simp [Category.assoc]
        _ = pushout.inl (cylinderEndpointMap X) (coprod.map j j) ≫
              prismCellEndpointIntermediateMap j ≫ ψ := by rw [hR]
        _ = (j ▷ TopCat.I.{u}) ≫ ψ := by
              rw [← Category.assoc, prismCellEndpointIntermediateMap_inl]
  · intro T a b h
    exact prismCellAttachedCylinder_existsDesc f k j hsq (PushoutCocone.mk a b h)

lemma prismCellAttachedCylinder_endpointMap {n : ℕ} {X P : TopCat.{u}}
    (f : TopCat.diskBoundary.{u} n ⟶ X) (k : TopCat.disk.{u} n ⟶ P) (j : X ⟶ P)
    (hsq : IsPushout (diskBoundaryInclusion.{u} n) f k j)
    (hX : Top.relativeFiniteCellComplexes (cylinderEndpointMap X)) :
    Top.relativeFiniteCellComplexes (cylinderEndpointMap P) := by
  letI : Top.relativeFiniteCellComplexes.{u}.IsStableUnderCobaseChange :=
    relativeFiniteCellComplexes_isStableUnderCobaseChange
  let eX := cylinderEndpointMap X
  let jsum := coprod.map j j
  let rP := pushout.inr eX jsum
  have hR : IsPushout eX jsum (pushout.inl eX jsum) rP := IsPushout.of_hasPushout eX jsum
  have hrP : Top.relativeFiniteCellComplexes rP :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout hR.flip hX
  have hPush := prismCellAttachedCylinder_isPushout f k j hsq
  have hr : Top.relativeFiniteCellComplexes (prismCellEndpointIntermediateMap j) :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout hPush.flip
      (prismSideInclusion_relativeFiniteCellComplexes n)
  have hm : Top.relativeFiniteCellComplexes.{u}.IsMultiplicative := by
    change ((Top.cellBoundaries.{u}.pushouts ⊔
      MorphismProperty.isomorphisms TopCat.{u}).multiplicativeClosure).IsMultiplicative
    infer_instance
  have hfactor : cylinderEndpointMap P = rP ≫ prismCellEndpointIntermediateMap j := by
    symm
    exact prismCellEndpointIntermediateMap_inr j
  rw [hfactor]
  exact hm.comp_mem rP (prismCellEndpointIntermediateMap j) hrP hr

lemma cylinderEndpointMap_of_isInitial {X : TopCat.{u}} (hX : IsInitial X) :
    Top.relativeFiniteCellComplexes (cylinderEndpointMap X) := by
  have hCoprod : IsInitial (X ⨿ X) := by
    refine IsInitial.ofUniqueHom (fun Y => coprod.desc (hX.to Y) (hX.to Y)) ?_
    intro Y f
    apply coprod.hom_ext
    · exact hX.hom_ext _ _
    · exact hX.hom_ext _ _
  have hTensor : IsInitial (X ⊗ TopCat.I.{u}) := by
    refine IsInitial.ofUniqueHom
      (fun Y => (intervalHomEquiv X Y).symm (hX.to (intervalExponential.obj Y))) ?_
    intro Y f
    apply (intervalHomEquiv X Y).injective
    exact hX.hom_ext _ _
  let e := hCoprod.uniqueUpToIso hTensor
  have heq : cylinderEndpointMap X = e.hom := hCoprod.hom_ext _ _
  have hIso : IsIso (cylinderEndpointMap X) := by
    rw [heq]
    infer_instance
  exact isomorphisms_le_relativeFiniteCellComplexes _
    (MorphismProperty.isomorphisms.iff _ |>.2 hIso)

lemma cylinderEndpointMap_stable_under_basic {A B : TopCat.{u}} (g : A ⟶ B)
    (hg : (Top.cellBoundaries.{u}.pushouts ⊔
      MorphismProperty.isomorphisms TopCat.{u}) g)
    (hA : Top.relativeFiniteCellComplexes (cylinderEndpointMap A)) :
    Top.relativeFiniteCellComplexes (cylinderEndpointMap B) := by
  rcases hg with hgCell | hgIso
  · change Top.cellBoundaries.{u}.pushouts g at hgCell
    rcases hgCell with ⟨A₀, B₀, p, f, k, hp, hsq⟩
    change MorphismProperty.ofHoms (fun n : ℕ => diskBoundaryInclusion.{u} n) p at hp
    rw [MorphismProperty.ofHoms_iff] at hp
    rcases hp with ⟨n, hArrow⟩
    rcases (Arrow.mk_eq_mk_iff p (diskBoundaryInclusion.{u} n)).mp hArrow with
      ⟨hA₀, hB₀, hpEq⟩
    cases hA₀
    cases hB₀
    have hpEq' : p = diskBoundaryInclusion.{u} n := by simpa using hpEq
    subst p
    exact prismCellAttachedCylinder_endpointMap f k g hsq.flip hA
  · rw [MorphismProperty.isomorphisms.iff] at hgIso
    let e := asIso g
    let gSum := coprod.map g g
    have hIsoSum : IsIso gSum := by infer_instance
    have hIsoTensor : IsIso (g ▷ TopCat.I.{u}) := by infer_instance
    have hNatural := cylinderEndpointMap_natural g
    have hfactor : cylinderEndpointMap B = inv gSum ≫ cylinderEndpointMap A ≫ (g ▷ TopCat.I) := by
      calc
        cylinderEndpointMap B = 𝟙 (B ⨿ B) ≫ cylinderEndpointMap B := by simp
        _ = (inv gSum ≫ gSum) ≫ cylinderEndpointMap B := by simp [gSum]
        _ = inv gSum ≫ (gSum ≫ cylinderEndpointMap B) := by simp [Category.assoc]
        _ = inv gSum ≫ (cylinderEndpointMap A ≫ (g ▷ TopCat.I)) := by rw [← hNatural]
        _ = inv gSum ≫ cylinderEndpointMap A ≫ (g ▷ TopCat.I) := by simp [Category.assoc]
    have hMult : Top.relativeFiniteCellComplexes.{u}.IsMultiplicative := by
      change ((Top.cellBoundaries.{u}.pushouts ⊔
        MorphismProperty.isomorphisms TopCat.{u}).multiplicativeClosure).IsMultiplicative
      infer_instance
    have hInv : Top.relativeFiniteCellComplexes (inv gSum) :=
      isomorphisms_le_relativeFiniteCellComplexes _ (by infer_instance)
    have hTensor : Top.relativeFiniteCellComplexes (g ▷ TopCat.I.{u}) :=
      isomorphisms_le_relativeFiniteCellComplexes _ (by infer_instance)
    have hPost := hMult.comp_mem (cylinderEndpointMap A) (g ▷ TopCat.I.{u}) hA hTensor
    have hAll := hMult.comp_mem (inv gSum) (cylinderEndpointMap A ≫ (g ▷ TopCat.I.{u})) hInv hPost
    rw [hfactor]
    exact hAll

lemma finiteEndpoint_of_relative {A B : TopCat.{u}} (f : A ⟶ B)
    (hf : Top.relativeFiniteCellComplexes f) (hA : IsInitial A) :
    Top.relativeFiniteCellComplexes (cylinderEndpointMap B) := by
  change ((Top.cellBoundaries.{u}.pushouts ⊔
    MorphismProperty.isomorphisms TopCat.{u}).multiplicativeClosure) f at hf
  revert hA
  induction hf with
  | of f hf =>
      intro hA
      exact cylinderEndpointMap_stable_under_basic f hf
        (cylinderEndpointMap_of_isInitial hA)
  | id A =>
      intro hA
      exact cylinderEndpointMap_of_isInitial hA
  | comp_of f g hf hg ih =>
      intro hA
      exact cylinderEndpointMap_stable_under_basic g hg (ih hA)

theorem finiteCell_cylinderEndpoints_cofibration {X : TopCat.{u}}
    (hX : Top.IsFiniteCellComplex X) :
    Top.relativeFiniteCellComplexes
      (coprod.desc (TopCat.ι₀ : X ⟶ X ⊗ TopCat.I) TopCat.ι₁) := by
  change Top.relativeFiniteCellComplexes (initial.to X) at hX
  exact finiteEndpoint_of_relative (initial.to X) hX initialIsInitial

lemma homotopyEquivalences_prodFst (X : TopCat.{u}) :
    Top.homotopyEquivalences (fst X TopCat.I) := by
  refine ⟨TopCat.ι₀, ?_, ?_⟩
  · change ((fst X TopCat.I ≫ TopCat.ι₀).hom).Homotopic
      ((𝟙 (X ⊗ TopCat.I) : X ⊗ TopCat.I ⟶ X ⊗ TopCat.I).hom)
    let η : X ⊗ TopCat.I ⟶ X ⨯ TopCat.I :=
      Limits.prod.lift (fst X TopCat.I) (snd X TopCat.I)
    let ε : X ⨯ TopCat.I ⟶ X ⊗ TopCat.I :=
      CartesianMonoidalCategory.lift Limits.prod.fst Limits.prod.snd
    have hηε : η ≫ ε = 𝟙 (X ⊗ TopCat.I) := by
      apply CartesianMonoidalCategory.hom_ext
      · simp [η, ε]
      · simp [η, ε]
    have hεη : ε ≫ η = 𝟙 (X ⨯ TopCat.I) := by
      apply Limits.prod.hom_ext
      · simp [η, ε]
      · simp [η, ε]
    let eIso : X ⊗ TopCat.I ≅ X ⨯ TopCat.I := ⟨η, ε, hηε, hεη⟩
    let e := TopCat.homeoOfIso (eIso ≪≫ TopCat.prodIsoProd X TopCat.I)
    have e_apply (z : X ⊗ TopCat.I) :
        e z = (fst X TopCat.I z, snd X TopCat.I z) := by
      change (TopCat.prodIsoProd X TopCat.I).hom (η z) = _
      rw [TopCat.prodIsoProd_hom_apply]
      apply Prod.ext
      · change (η ≫ Limits.prod.fst) z = (fst X TopCat.I) z
        rw [Limits.prod.lift_fst]
      · change (η ≫ Limits.prod.snd) z = (snd X TopCat.I) z
        rw [Limits.prod.lift_snd]
    have hproj : (fst X TopCat.I ≫ TopCat.ι₀) ≫ snd X TopCat.I = TopCat.const 0 := by
      rw [Category.assoc, TopCat.ι₀_snd]
      ext z
      simp
    refine ⟨{
      toFun := fun z => e.symm
        ((e z.2).1, TopCat.I.homeomorph.symm (z.1 * TopCat.I.homeomorph (e z.2).2))
      continuous_toFun := by fun_prop
      map_zero_left := ?_
      map_one_left := ?_ }⟩
    · intro z
      apply e.injective
      rw [Homeomorph.apply_symm_apply, e_apply z,
        e_apply ((fst X TopCat.I ≫ TopCat.ι₀) z)]
      apply Prod.ext
      · simp only [ConcreteCategory.comp_apply, TopCat.ι₀_apply]
        rfl
      · rw [zero_mul]
        have hsnd : (snd X TopCat.I) ((fst X TopCat.I ≫ TopCat.ι₀) z) = 0 := by
          change ((fst X TopCat.I ≫ TopCat.ι₀) ≫ snd X TopCat.I) z =
            (TopCat.const 0) z
          rw [hproj]
        rw [hsnd]
        apply TopCat.I.ext
        simp
    · intro z
      apply e.injective
      simp [e, TopCat.homeoOfIso, TopCat.I.homeomorph_one]
  · simpa using ContinuousMap.Homotopic.refl ((𝟙 X : X ⟶ X).hom)

lemma finCell_exists_cylinder {I : FinCell.{u}} (hI : IsInitial I) (X : FinCell.{u}) :
    Nonempty (RelativeCylinder (hI.to X)) := by
  let J : FinCell.{u} ⥤ TopCat.{u} := ObjectProperty.ι _
  let i := hI.to X
  have hi : cofibrations FinCell.{u} i := finCell_isCofibrationCategory.initial_cofibration hI X
  letI : HasPushout i i := finCell_hasPushout i i hi
  let P : FinCell.{u} := pushout i i
  let j₀ : X ⟶ P := pushout.inl i i
  let j₁ : X ⟶ P := pushout.inr i i
  have hsq : IsPushout i i j₀ j₁ := IsPushout.of_hasPushout i i
  letI : CreatesColimit (span i i) J := finCell_createsPushout i i hi
  have hsqTop : IsPushout (J.map i) (J.map i) (J.map j₀) (J.map j₁) :=
    Functor.map_isPushout J hsq
  have hITop : IsInitial (J.obj I) := finCell_topImage_initial hI
  have hiTopEq : J.map i = hITop.to X.obj := hITop.hom_ext _ _
  have hcoprod : IsPushout (J.map i) (J.map i)
      (coprod.inl : X.obj ⟶ X.obj ⨿ X.obj) coprod.inr := by
    rw [hiTopEq]
    exact IsPushout.of_is_coproduct (coprodIsCoprod X.obj X.obj) hITop
  let e := hsqTop.isoIsPushout X.obj X.obj hcoprod
  let endpointMap := coprod.desc (TopCat.ι₀ : X.obj ⟶ X.obj ⊗ TopCat.I) TopCat.ι₁
  have hEndpoint : Top.relativeFiniteCellComplexes endpointMap :=
    finiteCell_cylinderEndpoints_cofibration X.property
  have hm : Top.relativeFiniteCellComplexes.{u}.IsMultiplicative := by
    change ((Top.cellBoundaries.{u}.pushouts ⊔
      MorphismProperty.isomorphisms TopCat.{u}).multiplicativeClosure).IsMultiplicative
    infer_instance
  have hIso : Top.relativeFiniteCellComplexes e.hom := by
    apply isomorphisms_le_relativeFiniteCellComplexes
    exact MorphismProperty.isomorphisms.iff _ |>.2 inferInstance
  let cTop : J.obj P ⟶ X.obj ⊗ TopCat.I := e.hom ≫ endpointMap
  have hcTop : Top.relativeFiniteCellComplexes cTop :=
    hm.comp_mem e.hom endpointMap hIso hEndpoint
  have he₀ : J.map j₀ ≫ e.hom = coprod.inl :=
    hsqTop.inl_isoIsPushout_hom X.obj X.obj hcoprod
  have he₁ : J.map j₁ ≫ e.hom = coprod.inr :=
    hsqTop.inr_isoIsPushout_hom X.obj X.obj hcoprod
  have hj₀c : J.map j₀ ≫ cTop = TopCat.ι₀ := by
    change (J.map j₀ ≫ e.hom) ≫ endpointMap = TopCat.ι₀
    rw [he₀]
    exact coprod.inl_desc _ _
  have hj₁c : J.map j₁ ≫ cTop = TopCat.ι₁ := by
    change (J.map j₁ ≫ e.hom) ≫ endpointMap = TopCat.ι₁
    rw [he₁]
    exact coprod.inr_desc _ _
  have hProd : Top.IsFiniteCellComplex (X.obj ⊗ TopCat.I) := by
    change Top.relativeFiniteCellComplexes (initial.to (X.obj ⊗ TopCat.I))
    have heq : initial.to (X.obj ⊗ TopCat.I) = initial.to (J.obj P) ≫ cTop :=
      initialIsInitial.hom_ext _ _
    rw [heq]
    exact hm.comp_mem (initial.to (J.obj P)) cTop P.property hcTop
  let cylObj : FinCell.{u} := ⟨X.obj ⊗ TopCat.I, hProd⟩
  let c : P ⟶ cylObj := ObjectProperty.homMk cTop
  let pTop : X.obj ⊗ TopCat.I ⟶ X.obj := fst X.obj TopCat.I
  let p : cylObj ⟶ X := ObjectProperty.homMk pTop
  refine ⟨{
    P := P
    j₀ := j₀
    j₁ := j₁
    isPushout := hsq
    I := cylObj
    c := c
    p := p
    c_mem := ?_
    p_mem := ?_
    j₀_c_p := ?_
    j₁_c_p := ?_ }⟩
  · change Top.relativeFiniteCellComplexes cTop
    exact hcTop
  · change Top.homotopyEquivalences pTop
    exact homotopyEquivalences_prodFst X.obj
  · apply ObjectProperty.hom_ext
    calc
      J.map j₀ ≫ cTop ≫ pTop = (J.map j₀ ≫ cTop) ≫ pTop := by rw [← Category.assoc]
      _ = TopCat.ι₀ ≫ pTop := by rw [hj₀c]
      _ = 𝟙 X.obj := TopCat.ι₀_fst _
  · apply ObjectProperty.hom_ext
    calc
      J.map j₁ ≫ cTop ≫ pTop = (J.map j₁ ≫ cTop) ≫ pTop := by rw [← Category.assoc]
      _ = TopCat.ι₁ ≫ pTop := by rw [hj₁c]
      _ = 𝟙 X.obj := TopCat.ι₁_fst _

theorem finCell_isCylinderCategory_proof : IsCylinderCategory FinCell.{u} := by
  let J : FinCell.{u} ⥤ TopCat.{u} := ObjectProperty.ι _
  letI : IsCofibrationCategory FinCell.{u} := finCell_isCofibrationCategory
  refine {
    toIsCofibrationCategory := finCell_isCofibrationCategory
    isomorphisms_le_weakEquivalences := ?_
    weakEquivalences_isMultiplicative := ?_
    twoOutOfSix := ?_
    trivialCofibration_cobaseChange := ?_
    exists_cylinder := ?_
    exists_retraction := ?_ }
  · intro A B f hf
    haveI : IsIso f := MorphismProperty.isomorphisms.iff f |>.1 hf
    change Top.homotopyEquivalences (J.map f)
    exact homotopyEquivalences_of_isIso (J.map f)
  · change (Top.homotopyEquivalences.inverseImage J).IsMultiplicative
    infer_instance
  · intro A B C D f g h hfg hgh
    change Top.homotopyEquivalences (J.map (f ≫ g)) at hfg
    change Top.homotopyEquivalences (J.map (g ≫ h)) at hgh
    change Top.homotopyEquivalences (J.map f) ∧
      Top.homotopyEquivalences (J.map g) ∧ Top.homotopyEquivalences (J.map h) ∧
        Top.homotopyEquivalences (J.map (f ≫ g ≫ h))
    simpa only [Functor.map_comp] using
      homotopyEquivalences_twoOutOfSix (J.map f) (J.map g) (J.map h) hfg hgh
  · intro A B X P i f k j hsq hi hwi
    exact finCell_trivialCofibration_cobaseChange i f k j hsq hi hwi
  · exact finCell_exists_cylinder
  · exact finCell_trivialCofibration_retraction

end HomotopyHypothesis.FiniteCategory.Cylinder

#print axioms HomotopyHypothesis.FiniteCategory.Cylinder.finCell_isCylinderCategory_proof
