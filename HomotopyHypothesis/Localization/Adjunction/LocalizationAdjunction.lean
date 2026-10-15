import Mathlib.AlgebraicTopology.ModelCategory.LeftHomotopy
import Mathlib.CategoryTheory.Localization.OfQuotient
import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.SemiModel
/-!
# Localizations from adjunctions

The homotopy category of cofibrant objects provides the intermediate category for the
localization induced by a homotopical right adjoint.
-/

universe w v₁ u₁ v₂ u₂

open CategoryTheory Limits HomotopicalAlgebra
open HomotopyHypothesis.Henry

namespace HomotopyHypothesis.Localization.Adjunction

section SemiModel

variable {C : Type u₁} [instC : Category.{v₁} C]
  (cof fib W : MorphismProperty C)

private theorem cof_trivFib_weakFactorizationSystem
    (hC : IsSemiModelCategory C cof fib W) :
    MorphismProperty.IsWeakFactorizationSystem cof (fib ⊓ W) := by
  letI : HasFiniteLimits C := IsSemiModelCategory.hasFiniteLimits hC
  letI : HasFiniteColimits C := IsSemiModelCategory.hasFiniteColimits hC
  letI : CategoryWithCofibrations C := ⟨cof⟩
  letI : CategoryWithFibrations C := ⟨fib⟩
  letI : CategoryWithWeakEquivalences C := ⟨W⟩
  letI : W.HasTwoOutOfThreeProperty := IsSemiModelCategory.twoOutOfThree hC
  letI : cof.IsStableUnderRetracts := IsSemiModelCategory.cof_retracts hC
  letI : fib.IsStableUnderRetracts := IsSemiModelCategory.fib_retracts hC
  letI : W.IsStableUnderRetracts := IsSemiModelCategory.W_retracts hC
  letI : (fib ⊓ W).IsStableUnderRetracts := inferInstance
  letI : MorphismProperty.HasFactorization cof (fib ⊓ W) := ⟨fun f => by
    obtain ⟨Z, i, p, hi, hp, hw, hfac⟩ := IsSemiModelCategory.factor_cof_trivFib hC f
    exact ⟨⟨Z, i, p, hfac, hi, ⟨hp, hw⟩⟩⟩⟩
  exact MorphismProperty.IsWeakFactorizationSystem.mk' cof (fib ⊓ W)
    (fun i p hi hp => IsSemiModelCategory.lift_cof_trivFib hC p hp i hi)

private theorem cof_stableUnderComposition
    (hC : IsSemiModelCategory C cof fib W) : cof.IsStableUnderComposition := by
  letI : HasFiniteLimits C := IsSemiModelCategory.hasFiniteLimits hC
  letI : HasFiniteColimits C := IsSemiModelCategory.hasFiniteColimits hC
  letI : CategoryWithCofibrations C := ⟨cof⟩
  letI : CategoryWithFibrations C := ⟨fib⟩
  letI : CategoryWithWeakEquivalences C := ⟨W⟩
  letI : W.HasTwoOutOfThreeProperty := IsSemiModelCategory.twoOutOfThree hC
  letI : MorphismProperty.IsWeakFactorizationSystem cof (fib ⊓ W) :=
    cof_trivFib_weakFactorizationSystem cof fib W hC
  rw [← MorphismProperty.llp_eq_of_wfs cof (fib ⊓ W)]
  infer_instance

private theorem cof_stableUnderCobaseChange
    (hC : IsSemiModelCategory C cof fib W) : cof.IsStableUnderCobaseChange := by
  letI : HasFiniteLimits C := IsSemiModelCategory.hasFiniteLimits hC
  letI : HasFiniteColimits C := IsSemiModelCategory.hasFiniteColimits hC
  letI : CategoryWithCofibrations C := ⟨cof⟩
  letI : CategoryWithFibrations C := ⟨fib⟩
  letI : CategoryWithWeakEquivalences C := ⟨W⟩
  letI : W.HasTwoOutOfThreeProperty := IsSemiModelCategory.twoOutOfThree hC
  letI : MorphismProperty.IsWeakFactorizationSystem cof (fib ⊓ W) :=
    cof_trivFib_weakFactorizationSystem cof fib W hC
  rw [← MorphismProperty.llp_eq_of_wfs cof (fib ⊓ W)]
  infer_instance

def cofObjects : ObjectProperty C := fun X => IsCofibrantFor cof X

abbrev Cof := (cofObjects cof).FullSubcategory

def cofInclusion : Cof cof ⥤ C := (cofObjects cof).ι

lemma cofibrant_coproduct (hC : IsSemiModelCategory C cof fib W)
    {X Y : C} [HasBinaryCoproduct X Y] (hX : IsCofibrantFor cof X)
    (hY : IsCofibrantFor cof Y) : IsCofibrantFor cof (X ⨿ Y) := by
  letI : HasFiniteColimits C := IsSemiModelCategory.hasFiniteColimits hC
  letI : CategoryWithCofibrations C := ⟨cof⟩
  letI : cof.IsStableUnderComposition := cof_stableUnderComposition cof fib W hC
  letI : cof.IsStableUnderCobaseChange := cof_stableUnderCobaseChange cof fib W hC
  intro I hI
  have hinl : cof (coprod.inl : X ⟶ X ⨿ Y) :=
    MorphismProperty.of_isPushout
      ((IsPushout.of_isColimit_binaryCofan_of_isInitial
        (colimit.isColimit (pair X Y)) hI).flip) (hY hI)
  rw [hI.hom_ext (hI.to (X ⨿ Y)) (hI.to X ≫ coprod.inl)]
  exact cof.comp_mem _ _ (hX hI) hinl

structure CofibrantResolution (X : C) where
  Q : Cof cof
  q : @Quiver.Hom C instC.toQuiver ((cofInclusion cof).obj Q) X
  q_fib : fib q
  q_we : W q

noncomputable def cofibrantResolution (hC : IsSemiModelCategory C cof fib W)
    (X : C) : CofibrantResolution cof fib W X := by
  classical
  letI : HasFiniteColimits C := IsSemiModelCategory.hasFiniteColimits hC
  letI : CategoryWithCofibrations C := ⟨cof⟩
  letI : cof.IsStableUnderRetracts := IsSemiModelCategory.cof_retracts hC
  letI : MorphismProperty.IsWeakFactorizationSystem cof (fib ⊓ W) :=
    cof_trivFib_weakFactorizationSystem cof fib W hC
  let d := MorphismProperty.factorizationData cof (fib ⊓ W) (initial.to X)
  refine ⟨⟨d.Z, ?_⟩, d.p, d.hp.1, d.hp.2⟩
  intro I hI
  have hz : cof (initial.to d.Z) := by
    rw [Subsingleton.elim (initial.to d.Z) d.i]
    exact d.hi
  have e : Arrow.mk (hI.to d.Z) ≅ Arrow.mk (initial.to d.Z) :=
    Arrow.isoMk (IsInitial.uniqueUpToIso hI initialIsInitial) (Iso.refl _)
  exact (cof.arrow_mk_iso_iff e).2 hz

structure CofibrantCylinder (X : C) [HasBinaryCoproduct X X] where
  I : C
  hI : IsCofibrantFor cof I
  i : @Quiver.Hom C instC.toQuiver (X ⨿ X) I
  π : @Quiver.Hom C instC.toQuiver I X
  fac : i ≫ π = coprod.desc (𝟙 X) (𝟙 X)
  hi : cof i
  hπ : W π

noncomputable def cofibrantCylinder (hC : IsSemiModelCategory C cof fib W)
    {X : C} [HasBinaryCoproduct X X] (hX : IsCofibrantFor cof X) :
    CofibrantCylinder cof W X := by
  classical
  letI : HasFiniteColimits C := IsSemiModelCategory.hasFiniteColimits hC
  letI : cof.IsStableUnderComposition := cof_stableUnderComposition cof fib W hC
  letI : cof.IsStableUnderCobaseChange := cof_stableUnderCobaseChange cof fib W hC
  letI : MorphismProperty.IsWeakFactorizationSystem cof (fib ⊓ W) :=
    cof_trivFib_weakFactorizationSystem cof fib W hC
  have hXX : IsCofibrantFor cof (X ⨿ X) := cofibrant_coproduct cof fib W hC hX hX
  let fold : X ⨿ X ⟶ X := coprod.desc (𝟙 X) (𝟙 X)
  let d := MorphismProperty.factorizationData cof (fib ⊓ W) fold
  have hI : IsCofibrantFor cof d.Z := by
    intro J hJ
    rw [hJ.hom_ext (hJ.to d.Z) (hJ.to (X ⨿ X) ≫ d.i)]
    exact cof.comp_mem _ _ (hXX hJ) d.hi
  exact ⟨d.Z, hI, d.i, d.p, d.fac, d.hi, d.hp.2⟩

def cofWeakEquivalences : MorphismProperty (Cof cof) :=
  W.inverseImage (cofInclusion cof)

lemma exists_resolutionMap (hC : IsSemiModelCategory C cof fib W)
    {X Y : C} (f : X ⟶ Y) :
    ∃ g : (cofibrantResolution cof fib W hC X).Q ⟶
        (cofibrantResolution cof fib W hC Y).Q,
      g.hom ≫ (cofibrantResolution cof fib W hC Y).q =
        (cofibrantResolution cof fib W hC X).q ≫ f := by
  classical
  letI : HasFiniteColimits C := IsSemiModelCategory.hasFiniteColimits hC
  let qX := cofibrantResolution cof fib W hC X
  let qY := cofibrantResolution cof fib W hC Y
  have hrlp : cof.rlp qY.q :=
    IsSemiModelCategory.lift_cof_trivFib hC qY.q ⟨qY.q_fib, qY.q_we⟩
  have hlift : HasLiftingProperty (initial.to ((cofInclusion cof).obj qX.Q)) qY.q :=
    hrlp (initial.to ((cofInclusion cof).obj qX.Q)) (qX.Q.2 initialIsInitial)
  let sq : CommSq (initial.to ((cofInclusion cof).obj qY.Q))
      (initial.to ((cofInclusion cof).obj qX.Q)) qY.q (qX.q ≫ f) := by
    constructor
    exact (initialIsInitial.hom_ext _ _)
  have hsq : sq.HasLift := hlift.sq_hasLift sq
  let liftData : sq.LiftStruct := Classical.choice hsq.exists_lift
  exact ⟨ObjectProperty.homMk liftData.l, liftData.fac_right⟩

noncomputable def resolutionMap (hC : IsSemiModelCategory C cof fib W)
    {X Y : C} (f : X ⟶ Y) :
    (cofibrantResolution cof fib W hC X).Q ⟶
      (cofibrantResolution cof fib W hC Y).Q :=
  Classical.choose (exists_resolutionMap cof fib W hC f)

@[reassoc]
lemma resolutionMap_fac (hC : IsSemiModelCategory C cof fib W)
    {X Y : C} (f : X ⟶ Y) :
    (cofInclusion cof).map (resolutionMap cof fib W hC f) ≫
        (cofibrantResolution cof fib W hC Y).q =
      (cofibrantResolution cof fib W hC X).q ≫ f :=
  Classical.choose_spec (exists_resolutionMap cof fib W hC f)

lemma resolution_maps_equal_in_localization (hC : IsSemiModelCategory C cof fib W)
    {A : Cof cof} {Y : C}
    (f g : A ⟶ (cofibrantResolution cof fib W hC Y).Q)
    (hfg : (cofInclusion cof).map f ≫ (cofibrantResolution cof fib W hC Y).q =
      (cofInclusion cof).map g ≫ (cofibrantResolution cof fib W hC Y).q) :
    (cofWeakEquivalences cof W).Q.map f =
      (cofWeakEquivalences cof W).Q.map g := by
  classical
  letI : HasFiniteColimits C := IsSemiModelCategory.hasFiniteColimits hC
  let qY := cofibrantResolution cof fib W hC Y
  let Xq := (cofInclusion cof).obj A
  let Yq := (cofInclusion cof).obj qY.Q
  have hXq : IsCofibrantFor cof Xq := A.property
  let P := cofibrantCylinder cof fib W hC hXq
  let Xc : Cof cof := A
  let Yc : Cof cof := qY.Q
  let Ic : Cof cof := ⟨P.I, P.hI⟩
  let fC := (cofInclusion cof).map f
  let gC := (cofInclusion cof).map g
  let top := coprod.desc fC gC
  let bottom := P.π ≫ fC ≫ qY.q
  have hsec₀ : (coprod.inl ≫ P.i) ≫ P.π = 𝟙 Xq := by
    calc
      (coprod.inl ≫ P.i) ≫ P.π =
          coprod.inl ≫ coprod.desc (𝟙 Xq) (𝟙 Xq) := by rw [Category.assoc, P.fac]
      _ = 𝟙 Xq := by simp
  have hsec₁ : (coprod.inr ≫ P.i) ≫ P.π = 𝟙 Xq := by
    calc
      (coprod.inr ≫ P.i) ≫ P.π =
          coprod.inr ≫ coprod.desc (𝟙 Xq) (𝟙 Xq) := by rw [Category.assoc, P.fac]
      _ = 𝟙 Xq := by simp
  have hbottom₀ : (coprod.inl ≫ P.i) ≫ (P.π ≫ fC ≫ qY.q) = fC ≫ qY.q := by
    calc
      (coprod.inl ≫ P.i) ≫ (P.π ≫ fC ≫ qY.q) =
          ((coprod.inl ≫ P.i) ≫ P.π) ≫ (fC ≫ qY.q) := by
            rw [← Category.assoc, ← Category.assoc]
      _ = (𝟙 Xq) ≫ (fC ≫ qY.q) :=
        congrArg (fun k => k ≫ (fC ≫ qY.q)) hsec₀
      _ = fC ≫ qY.q := by simp
  have hbottom₁ : (coprod.inr ≫ P.i) ≫ (P.π ≫ fC ≫ qY.q) = fC ≫ qY.q := by
    calc
      (coprod.inr ≫ P.i) ≫ (P.π ≫ fC ≫ qY.q) =
          ((coprod.inr ≫ P.i) ≫ P.π) ≫ (fC ≫ qY.q) := by
            rw [← Category.assoc, ← Category.assoc]
      _ = (𝟙 Xq) ≫ (fC ≫ qY.q) :=
        congrArg (fun k => k ≫ (fC ≫ qY.q)) hsec₁
      _ = fC ≫ qY.q := by simp
  have hbottom₀' : (coprod.inl ≫ P.i) ≫ bottom = fC ≫ qY.q := by
    change (coprod.inl ≫ P.i) ≫ (P.π ≫ fC ≫ qY.q) = fC ≫ qY.q
    exact hbottom₀
  have hbottom₁' : (coprod.inr ≫ P.i) ≫ bottom = fC ≫ qY.q := by
    change (coprod.inr ≫ P.i) ≫ (P.π ≫ fC ≫ qY.q) = fC ≫ qY.q
    exact hbottom₁
  have hsquare : CommSq top P.i qY.q bottom := by
    constructor
    apply coprod.hom_ext
    · calc
        coprod.inl ≫ top ≫ qY.q = fC ≫ qY.q := by simp [top]
        _ = (coprod.inl ≫ P.i) ≫ bottom := hbottom₀'.symm
        _ = coprod.inl ≫ P.i ≫ bottom :=
          Category.assoc coprod.inl P.i bottom
    · calc
        coprod.inr ≫ top ≫ qY.q = gC ≫ qY.q := by simp [top]
        _ = fC ≫ qY.q := hfg.symm
        _ = (coprod.inr ≫ P.i) ≫ bottom := hbottom₁'.symm
        _ = coprod.inr ≫ P.i ≫ bottom :=
          Category.assoc coprod.inr P.i bottom
  have hrlp : cof.rlp qY.q :=
    IsSemiModelCategory.lift_cof_trivFib hC qY.q ⟨qY.q_fib, qY.q_we⟩
  have hlift : HasLiftingProperty P.i qY.q := hrlp P.i P.hi
  have hsq : hsquare.HasLift := hlift.sq_hasLift hsquare
  let liftData : hsquare.LiftStruct := Classical.choice hsq.exists_lift
  let H : P.I ⟶ Yq := liftData.l
  have hH₀ : (coprod.inl ≫ P.i) ≫ H = fC := by
    calc
      (coprod.inl ≫ P.i) ≫ H = coprod.inl ≫ (P.i ≫ H) := by simp [Category.assoc]
      _ = coprod.inl ≫ top := by rw [liftData.fac_left]
      _ = fC := by simp [top]
  have hH₁ : (coprod.inr ≫ P.i) ≫ H = gC := by
    calc
      (coprod.inr ≫ P.i) ≫ H = coprod.inr ≫ (P.i ≫ H) := by simp [Category.assoc]
      _ = coprod.inr ≫ top := by rw [liftData.fac_left]
      _ = gC := by simp [top]
  let i₀ : Xc ⟶ Ic := ObjectProperty.homMk (coprod.inl ≫ P.i)
  let i₁ : Xc ⟶ Ic := ObjectProperty.homMk (coprod.inr ≫ P.i)
  let h : Ic ⟶ Yc := ObjectProperty.homMk H
  let p : Ic ⟶ Xc := ObjectProperty.homMk P.π
  have h0 : i₀ ≫ h = f := by ext; exact hH₀
  have h1 : i₁ ≫ h = g := by ext; exact hH₁
  have hp₀ : i₀ ≫ p = 𝟙 Xc := by
    ext
    exact hsec₀
  have hp₁ : i₁ ≫ p = 𝟙 Xc := by
    ext
    exact hsec₁
  let Wc := cofWeakEquivalences cof W
  have hpW : Wc p := P.hπ
  have hpis : IsIso (Wc.Q.map p) := Localization.inverts Wc.Q Wc p hpW
  letI := hpis
  have hi₀ : Wc.Q.map i₀ = Wc.Q.map i₁ := by
    apply (cancel_mono (Wc.Q.map p)).1
    calc
      Wc.Q.map i₀ ≫ Wc.Q.map p = Wc.Q.map (i₀ ≫ p) := (Wc.Q.map_comp i₀ p).symm
      _ = Wc.Q.map (𝟙 Xc) := by rw [hp₀]
      _ = Wc.Q.map (i₁ ≫ p) := by rw [hp₁]
      _ = Wc.Q.map i₁ ≫ Wc.Q.map p := Wc.Q.map_comp i₁ p
  calc
    Wc.Q.map f = Wc.Q.map (i₀ ≫ h) := by rw [← h0]
    _ = Wc.Q.map (i₁ ≫ h) := by rw [Functor.map_comp, Functor.map_comp, hi₀]
    _ = Wc.Q.map g := by rw [← h1]

noncomputable def cofibrantResolutionFunctor (hC : IsSemiModelCategory C cof fib W) :
    C ⥤ (cofWeakEquivalences cof W).Localization where
  obj X := (cofWeakEquivalences cof W).Q.obj
    (cofibrantResolution cof fib W hC X).Q
  map f := (cofWeakEquivalences cof W).Q.map (resolutionMap cof fib W hC f)
  map_id X := by
    rw [← (cofWeakEquivalences cof W).Q.map_id]
    exact resolution_maps_equal_in_localization cof fib W hC
      (resolutionMap cof fib W hC (𝟙 X)) (𝟙 _)
      (by simp [resolutionMap_fac])
  map_comp {X Y Z} f g := by
    rw [← (cofWeakEquivalences cof W).Q.map_comp]
    apply resolution_maps_equal_in_localization cof fib W hC
    calc
      (cofInclusion cof).map (resolutionMap cof fib W hC (f ≫ g)) ≫
          (cofibrantResolution cof fib W hC _).q =
        (cofibrantResolution cof fib W hC _).q ≫ f ≫ g := by
          rw [resolutionMap_fac]
      _ = ((cofInclusion cof).map (resolutionMap cof fib W hC f) ≫
            (cofInclusion cof).map (resolutionMap cof fib W hC g)) ≫
          (cofibrantResolution cof fib W hC _).q := by
            let qX := cofibrantResolution cof fib W hC X
            let qY := cofibrantResolution cof fib W hC Y
            let qZ := cofibrantResolution cof fib W hC Z
            let rf := resolutionMap cof fib W hC f
            let rg := resolutionMap cof fib W hC g
            change qX.q ≫ f ≫ g = (rf.hom ≫ rg.hom) ≫ qZ.q
            have hrf : (cofInclusion cof).map rf ≫ qY.q = qX.q ≫ f := by
              simpa [rf, qX, qY] using resolutionMap_fac cof fib W hC f
            have hrg : (cofInclusion cof).map rg ≫ qZ.q = qY.q ≫ g := by
              simpa [rg, qY, qZ] using resolutionMap_fac cof fib W hC g
            calc
              qX.q ≫ f ≫ g = (qX.q ≫ f) ≫ g := (Category.assoc _ _ _).symm
              _ = ((cofInclusion cof).map rf ≫ qY.q) ≫ g := by rw [← hrf]
              _ = (cofInclusion cof).map rf ≫ (qY.q ≫ g) := Category.assoc _ _ _
              _ = (cofInclusion cof).map rf ≫ ((cofInclusion cof).map rg ≫ qZ.q) :=
                by rw [← hrg]
              _ = ((cofInclusion cof).map rf ≫ (cofInclusion cof).map rg) ≫ qZ.q :=
                (Category.assoc _ _ _).symm

lemma resolutionFunctor_inverts (hC : IsSemiModelCategory C cof fib W) :
    W.IsInvertedBy (cofibrantResolutionFunctor cof fib W hC) := by
  letI : W.HasTwoOutOfThreeProperty := IsSemiModelCategory.twoOutOfThree hC
  intro X Y f hf
  let qX := cofibrantResolution cof fib W hC X
  let qY := cofibrantResolution cof fib W hC Y
  let g := resolutionMap cof fib W hC f
  have hcomp : W ((cofInclusion cof).map g ≫ qY.q) := by
    rw [resolutionMap_fac]
    exact W.comp_mem qX.q f qX.q_we hf
  have hg : W ((cofInclusion cof).map g) :=
    W.of_postcomp ((cofInclusion cof).map g) qY.q qY.q_we hcomp
  let Wc := cofWeakEquivalences cof W
  have hg' : Wc g := hg
  exact Localization.inverts Wc.Q Wc g hg'

lemma cofInclusion_inverts :
    (cofWeakEquivalences cof W).IsInvertedBy (cofInclusion cof ⋙ W.Q) := by
  intro X Y f hf
  apply Localization.inverts W.Q W ((cofInclusion cof).map f)
  change W ((cofInclusion cof).map f)
  exact hf

noncomputable def inclusionLocalizedFunctor :
    (cofWeakEquivalences cof W).Localization ⥤ W.Localization :=
  Localization.lift (cofInclusion cof ⋙ W.Q) (cofInclusion_inverts cof W)
    (cofWeakEquivalences cof W).Q

noncomputable def inclusionLocalizedFac :
    (cofWeakEquivalences cof W).Q ⋙ inclusionLocalizedFunctor cof W ≅
      cofInclusion cof ⋙ W.Q :=
  Localization.fac (cofInclusion cof ⋙ W.Q) (cofInclusion_inverts cof W)
    (cofWeakEquivalences cof W).Q

noncomputable def resolutionLocalizedFunctor
    (hC : IsSemiModelCategory C cof fib W) :
    W.Localization ⥤ (cofWeakEquivalences cof W).Localization :=
  Localization.lift (cofibrantResolutionFunctor cof fib W hC)
    (resolutionFunctor_inverts cof fib W hC) W.Q

noncomputable def resolutionLocalizedFac
    (hC : IsSemiModelCategory C cof fib W) :
    W.Q ⋙ resolutionLocalizedFunctor cof fib W hC ≅
      cofibrantResolutionFunctor cof fib W hC :=
  Localization.fac _ _ _

noncomputable def resolutionInclusionNatTrans
    (hC : IsSemiModelCategory C cof fib W) :
    cofibrantResolutionFunctor cof fib W hC ⋙ inclusionLocalizedFunctor cof W ⟶ W.Q where
  app X :=
    (inclusionLocalizedFac cof W).hom.app
      (@cofibrantResolution C instC cof fib W hC X).Q ≫
      W.Q.map (@cofibrantResolution C instC cof fib W hC X).q
  naturality X Y f := by
    let qX : CofibrantResolution cof fib W X := @cofibrantResolution C instC cof fib W hC X
    let qY : CofibrantResolution cof fib W Y := @cofibrantResolution C instC cof fib W hC Y
    let m : qX.Q ⟶ qY.Q := @resolutionMap C instC cof fib W hC X Y f
    symm
    change ((inclusionLocalizedFac cof W).hom.app qX.Q ≫ W.Q.map qX.q) ≫ W.Q.map f =
      (inclusionLocalizedFunctor cof W).map ((cofWeakEquivalences cof W).Q.map m) ≫
        (inclusionLocalizedFac cof W).hom.app qY.Q ≫ W.Q.map qY.q
    calc
      ((inclusionLocalizedFac cof W).hom.app qX.Q ≫ W.Q.map qX.q) ≫ W.Q.map f =
          (inclusionLocalizedFac cof W).hom.app qX.Q ≫
            (W.Q.map qX.q ≫ W.Q.map f) := Category.assoc _ _ _
      _ = (inclusionLocalizedFac cof W).hom.app qX.Q ≫ W.Q.map (qX.q ≫ f) := by
            rw [← W.Q.map_comp]
      _ = (inclusionLocalizedFac cof W).hom.app qX.Q ≫
          W.Q.map ((cofInclusion cof).map m ≫ qY.q) := by rw [resolutionMap_fac]
      _ = (inclusionLocalizedFunctor cof W).map ((cofWeakEquivalences cof W).Q.map m) ≫
          (inclusionLocalizedFac cof W).hom.app qY.Q ≫ W.Q.map qY.q := by
            have hnat := (inclusionLocalizedFac cof W).hom.naturality m
            simp only [Functor.comp_map] at hnat
            calc
              (inclusionLocalizedFac cof W).hom.app qX.Q ≫
                  W.Q.map ((cofInclusion cof).map m ≫ qY.q) =
                (inclusionLocalizedFac cof W).hom.app qX.Q ≫
                  (W.Q.map ((cofInclusion cof).map m) ≫ W.Q.map qY.q) := by
                    rw [W.Q.map_comp]
              _ = ((inclusionLocalizedFac cof W).hom.app qX.Q ≫
                    W.Q.map ((cofInclusion cof).map m)) ≫ W.Q.map qY.q :=
                    (Category.assoc _ _ _).symm
              _ = ((inclusionLocalizedFunctor cof W).map
                    ((cofWeakEquivalences cof W).Q.map m) ≫
                    (inclusionLocalizedFac cof W).hom.app qY.Q) ≫ W.Q.map qY.q := by
                    rw [← hnat]
              _ = (inclusionLocalizedFunctor cof W).map
                    ((cofWeakEquivalences cof W).Q.map m) ≫
                    (inclusionLocalizedFac cof W).hom.app qY.Q ≫ W.Q.map qY.q :=
                    Category.assoc _ _ _

noncomputable def resolutionInclusionNatIso
    (hC : IsSemiModelCategory C cof fib W) :
    cofibrantResolutionFunctor cof fib W hC ⋙ inclusionLocalizedFunctor cof W ≅ W.Q :=
  NatIso.ofComponents (fun X => by
    let qX : CofibrantResolution cof fib W X := @cofibrantResolution C instC cof fib W hC X
    have hq : IsIso (W.Q.map qX.q) := Localization.inverts W.Q W qX.q qX.q_we
    letI := hq
    exact (asIso ((inclusionLocalizedFac cof W).hom.app qX.Q)).trans
      (asIso (W.Q.map qX.q)))
    (fun {X Y} f => (resolutionInclusionNatTrans cof fib W hC).naturality f)

noncomputable def inclusionResolutionNatTrans
    (hC : IsSemiModelCategory C cof fib W) :
    cofInclusion cof ⋙ cofibrantResolutionFunctor cof fib W hC ⟶
      (cofWeakEquivalences cof W).Q where
  app X := by
    let qX : CofibrantResolution cof fib W X.obj :=
      @cofibrantResolution C instC cof fib W hC X.obj
    exact (cofWeakEquivalences cof W).Q.map (ObjectProperty.homMk qX.q)
  naturality X Y f := by
    let qX : CofibrantResolution cof fib W X.obj :=
      @cofibrantResolution C instC cof fib W hC X.obj
    let qY : CofibrantResolution cof fib W Y.obj :=
      @cofibrantResolution C instC cof fib W hC Y.obj
    let m := resolutionMap cof fib W hC ((cofInclusion cof).map f)
    have hm : m ≫ ObjectProperty.homMk qY.q = ObjectProperty.homMk qX.q ≫ f := by
      ext
      exact resolutionMap_fac cof fib W hC ((cofInclusion cof).map f)
    change (cofWeakEquivalences cof W).Q.map m ≫
        (cofWeakEquivalences cof W).Q.map (ObjectProperty.homMk qY.q) =
      (cofWeakEquivalences cof W).Q.map (ObjectProperty.homMk qX.q) ≫
        (cofWeakEquivalences cof W).Q.map f
    simp only [← Functor.map_comp, hm]
    rfl

noncomputable def inclusionResolutionNatIso
    (hC : IsSemiModelCategory C cof fib W) :
    cofInclusion cof ⋙ cofibrantResolutionFunctor cof fib W hC ≅
      (cofWeakEquivalences cof W).Q :=
  NatIso.ofComponents (fun X => by
    let qX : CofibrantResolution cof fib W X.obj :=
      @cofibrantResolution C instC cof fib W hC X.obj
    let Wc := cofWeakEquivalences cof W
    have hw : Wc (ObjectProperty.homMk qX.q) := qX.q_we
    exact Localization.isoOfHom Wc.Q Wc (ObjectProperty.homMk qX.q) hw)
    (fun {X Y} f => (inclusionResolutionNatTrans cof fib W hC).naturality f)

noncomputable def cofibrantLocalizationEquivalence
    (hC : IsSemiModelCategory C cof fib W) :
    W.Localization ≌ (cofWeakEquivalences cof W).Localization := by
  let ρ := resolutionLocalizedFunctor cof fib W hC
  let ι := inclusionLocalizedFunctor cof W
  let e₁ : W.Q ⋙ (ρ ⋙ ι) ≅ W.Q :=
    (Functor.associator W.Q ρ ι).symm ≪≫
      Functor.isoWhiskerRight (resolutionLocalizedFac cof fib W hC) ι ≪≫
      resolutionInclusionNatIso cof fib W hC
  let e₂ : (cofWeakEquivalences cof W).Q ⋙ (ι ⋙ ρ) ≅
      (cofWeakEquivalences cof W).Q :=
    (Functor.associator (cofWeakEquivalences cof W).Q ι ρ).symm ≪≫
      Functor.isoWhiskerRight (inclusionLocalizedFac cof W) ρ ≪≫
      Functor.associator (cofInclusion cof) W.Q ρ ≪≫
      Functor.isoWhiskerLeft (cofInclusion cof) (resolutionLocalizedFac cof fib W hC) ≪≫
      inclusionResolutionNatIso cof fib W hC
  let unit := Localization.liftNatIso W.Q W
    (W.Q ⋙ 𝟭 W.Localization) (W.Q ⋙ (ρ ⋙ ι)) (𝟭 W.Localization) (ρ ⋙ ι)
    (Functor.rightUnitor W.Q ≪≫ e₁.symm)
  let counit := Localization.liftNatIso (cofWeakEquivalences cof W).Q
    (cofWeakEquivalences cof W)
    ((cofWeakEquivalences cof W).Q ⋙ (ι ⋙ ρ)) (cofWeakEquivalences cof W).Q
    (ι ⋙ ρ) (𝟭 (cofWeakEquivalences cof W).Localization) e₂
  exact CategoryTheory.Equivalence.mk ρ ι unit counit

lemma exists_adjUnitLift {D : Type u₂} [Category.{v₂} D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (hC : IsSemiModelCategory C cof fib W)
    (hunit : ∀ X : C, IsCofibrantFor cof X → W (adj.unit.app X))
    (X : Cof cof) :
    ∃ u : @Quiver.Hom C instC.toQuiver ((cofInclusion cof).obj X)
        ((cofInclusion cof).obj
          (cofibrantResolution cof fib W hC
            (R.obj (L.obj ((cofInclusion cof).obj X)))).Q),
      u ≫ (cofibrantResolution cof fib W hC
          (R.obj (L.obj ((cofInclusion cof).obj X)))).q =
        adj.unit.app ((cofInclusion cof).obj X) ∧ W u := by
  classical
  letI : HasFiniteColimits C := IsSemiModelCategory.hasFiniteColimits hC
  letI : W.HasTwoOutOfThreeProperty := IsSemiModelCategory.twoOutOfThree hC
  let Z := (cofibrantResolution cof fib W hC
    (R.obj (L.obj ((cofInclusion cof).obj X))))
  have hrlp : cof.rlp Z.q :=
    IsSemiModelCategory.lift_cof_trivFib hC Z.q ⟨Z.q_fib, Z.q_we⟩
  have hlift : HasLiftingProperty (initial.to ((cofInclusion cof).obj X)) Z.q :=
    hrlp (initial.to ((cofInclusion cof).obj X))
      (X.property initialIsInitial)
  let sq : CommSq (initial.to ((cofInclusion cof).obj Z.Q))
      (initial.to ((cofInclusion cof).obj X)) Z.q
      (adj.unit.app ((cofInclusion cof).obj X)) := by
    constructor
    exact initialIsInitial.hom_ext _ _
  have hsq : sq.HasLift := hlift.sq_hasLift sq
  let d : sq.LiftStruct := Classical.choice hsq.exists_lift
  have hu : W d.l := W.of_postcomp d.l Z.q Z.q_we (by
    rw [d.fac_right]
    exact hunit ((cofInclusion cof).obj X) X.property)
  exact ⟨d.l, d.fac_right, hu⟩

noncomputable def adjUnitLift {D : Type u₂} [Category.{v₂} D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (hC : IsSemiModelCategory C cof fib W)
    (hunit : ∀ X : C, IsCofibrantFor cof X → W (adj.unit.app X))
    (X : Cof cof) :
    X ⟶ (cofibrantResolution cof fib W hC
      (R.obj (L.obj ((cofInclusion cof).obj X)))).Q :=
  ObjectProperty.homMk (Classical.choose (exists_adjUnitLift cof fib W adj hC hunit X))

lemma adjUnitLift_fac {D : Type u₂} [Category.{v₂} D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (hC : IsSemiModelCategory C cof fib W)
    (hunit : ∀ X : C, IsCofibrantFor cof X → W (adj.unit.app X))
    (X : Cof cof) :
    (cofInclusion cof).map (adjUnitLift cof fib W adj hC hunit X) ≫
        (cofibrantResolution cof fib W hC
          (R.obj (L.obj ((cofInclusion cof).obj X)))).q =
      adj.unit.app ((cofInclusion cof).obj X) := by
  change (Classical.choose (exists_adjUnitLift cof fib W adj hC hunit X)) ≫ _ = _
  exact (Classical.choose_spec (exists_adjUnitLift cof fib W adj hC hunit X)).1

lemma adjUnitLift_we {D : Type u₂} [Category.{v₂} D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (hC : IsSemiModelCategory C cof fib W)
    (hunit : ∀ X : C, IsCofibrantFor cof X → W (adj.unit.app X))
    (X : Cof cof) :
    W ((cofInclusion cof).map (adjUnitLift cof fib W adj hC hunit X)) := by
  change W (Classical.choose (exists_adjUnitLift cof fib W adj hC hunit X))
  exact (Classical.choose_spec (exists_adjUnitLift cof fib W adj hC hunit X)).2

noncomputable def adjDerivedUnitNatTrans {D : Type u₂} [Category.{v₂} D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (hC : IsSemiModelCategory C cof fib W)
    (hunit : ∀ X : C, IsCofibrantFor cof X → W (adj.unit.app X)) :
    (cofWeakEquivalences cof W).Q ⟶
      cofInclusion cof ⋙ L ⋙ R ⋙ cofibrantResolutionFunctor cof fib W hC where
  app X := (cofWeakEquivalences cof W).Q.map
    (adjUnitLift cof fib W adj hC hunit X)
  naturality X Y f := by
    let uX := adjUnitLift cof fib W adj hC hunit X
    let uY := adjUnitLift cof fib W adj hC hunit Y
    let qX := cofibrantResolution cof fib W hC
      (R.obj (L.obj ((cofInclusion cof).obj X)))
    let qY := cofibrantResolution cof fib W hC
      (R.obj (L.obj ((cofInclusion cof).obj Y)))
    let m := resolutionMap cof fib W hC
      (R.map (L.map ((cofInclusion cof).map f)))
    have hunitNat :
        (cofInclusion cof).map f ≫ adj.unit.app ((cofInclusion cof).obj Y) =
          adj.unit.app ((cofInclusion cof).obj X) ≫
            R.map (L.map ((cofInclusion cof).map f)) := by
      simpa only [Functor.id_map, Functor.comp_map] using
        adj.unit.naturality ((cofInclusion cof).map f)
    have h₁ :
        ((cofInclusion cof).map f ≫ (cofInclusion cof).map uY) ≫ qY.q =
          (cofInclusion cof).map f ≫ adj.unit.app ((cofInclusion cof).obj Y) := by
      rw [Category.assoc, adjUnitLift_fac]
    have h₂ :
        ((cofInclusion cof).map uX ≫ (cofInclusion cof).map m) ≫ qY.q =
          adj.unit.app ((cofInclusion cof).obj X) ≫
            R.map (L.map ((cofInclusion cof).map f)) := by
      calc
        ((cofInclusion cof).map uX ≫ (cofInclusion cof).map m) ≫ qY.q =
            (cofInclusion cof).map uX ≫
              ((cofInclusion cof).map m ≫ qY.q) := Category.assoc _ _ _
        _ = (cofInclusion cof).map uX ≫
              (qX.q ≫ R.map (L.map ((cofInclusion cof).map f))) := by
                rw [resolutionMap_fac]
        _ = ((cofInclusion cof).map uX ≫ qX.q) ≫
              R.map (L.map ((cofInclusion cof).map f)) :=
                (Category.assoc _ _ _).symm
        _ = adj.unit.app ((cofInclusion cof).obj X) ≫
              R.map (L.map ((cofInclusion cof).map f)) := by
                rw [adjUnitLift_fac]
    have hfg :
        ((cofInclusion cof).map f ≫ (cofInclusion cof).map uY) ≫ qY.q =
          ((cofInclusion cof).map uX ≫ (cofInclusion cof).map m) ≫ qY.q :=
      h₁.trans (hunitNat.trans h₂.symm)
    change (cofWeakEquivalences cof W).Q.map f ≫
        (cofWeakEquivalences cof W).Q.map uY =
      (cofWeakEquivalences cof W).Q.map uX ≫
        (cofWeakEquivalences cof W).Q.map m
    simpa only [Functor.map_comp] using
      resolution_maps_equal_in_localization cof fib W hC (f ≫ uY) (uX ≫ m) hfg

noncomputable def adjDerivedUnitNatIso {D : Type u₂} [Category.{v₂} D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (hC : IsSemiModelCategory C cof fib W)
    (hunit : ∀ X : C, IsCofibrantFor cof X → W (adj.unit.app X)) :
    (cofWeakEquivalences cof W).Q ≅
      cofInclusion cof ⋙ L ⋙ R ⋙ cofibrantResolutionFunctor cof fib W hC :=
  NatIso.ofComponents (fun X => by
    exact Localization.isoOfHom (cofWeakEquivalences cof W).Q
      (cofWeakEquivalences cof W)
      (adjUnitLift cof fib W adj hC hunit X)
      (by change W ((cofInclusion cof).map (adjUnitLift cof fib W adj hC hunit X));
          exact adjUnitLift_we cof fib W adj hC hunit X))
    (fun {X Y} f => (adjDerivedUnitNatTrans cof fib W adj hC hunit).naturality f)

noncomputable def adjResolutionCounit {D : Type u₂} [Category.{v₂} D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (hC : IsSemiModelCategory C cof fib W) (Y : D) :
    L.obj ((cofInclusion cof).obj
      (cofibrantResolution cof fib W hC (R.obj Y)).Q) ⟶ Y :=
  (adj.homEquiv _ _).symm (cofibrantResolution cof fib W hC (R.obj Y)).q

lemma adjResolutionCounit_fac {D : Type u₂} [Category.{v₂} D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (hC : IsSemiModelCategory C cof fib W) (Y : D) :
    adj.unit.app ((cofInclusion cof).obj
        (cofibrantResolution cof fib W hC (R.obj Y)).Q) ≫
      R.map (adjResolutionCounit cof fib W adj hC Y) =
        (cofibrantResolution cof fib W hC (R.obj Y)).q := by
  simpa only [Adjunction.homEquiv_apply, adjResolutionCounit] using
    (adj.homEquiv _ _).apply_symm_apply
      (cofibrantResolution cof fib W hC (R.obj Y)).q

lemma adjResolutionCounit_we {D : Type u₂} [Category.{v₂} D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (hC : IsSemiModelCategory C cof fib W) {WD : MorphismProperty D}
    (hR : WD = W.inverseImage R)
    (hunit : ∀ X : C, IsCofibrantFor cof X → W (adj.unit.app X)) (Y : D) :
    WD (adjResolutionCounit cof fib W adj hC Y) := by
  letI : W.HasTwoOutOfThreeProperty := IsSemiModelCategory.twoOutOfThree hC
  let q := cofibrantResolution cof fib W hC (R.obj Y)
  have hη := hunit ((cofInclusion cof).obj q.Q) q.Q.property
  have hcomp : W (adj.unit.app ((cofInclusion cof).obj q.Q) ≫
      R.map (adjResolutionCounit cof fib W adj hC Y)) := by
    rw [adjResolutionCounit_fac]
    exact q.q_we
  have hRp : W (R.map (adjResolutionCounit cof fib W adj hC Y)) :=
    W.of_precomp _ _ hη hcomp
  rw [hR]
  exact hRp

lemma adjResolutionCounit_naturality {D : Type u₂} [Category.{v₂} D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (hC : IsSemiModelCategory C cof fib W) {Y Z : D} (f : Y ⟶ Z) :
    L.map ((cofInclusion cof).map
        (resolutionMap cof fib W hC (R.map f))) ≫
      adjResolutionCounit cof fib W adj hC Z =
        adjResolutionCounit cof fib W adj hC Y ≫ f := by
  let qY := cofibrantResolution cof fib W hC (R.obj Y)
  let qZ := cofibrantResolution cof fib W hC (R.obj Z)
  let m := resolutionMap cof fib W hC (R.map f)
  change L.map ((cofInclusion cof).map m) ≫
        (adj.homEquiv ((cofInclusion cof).obj qZ.Q) Z).symm qZ.q =
      (adj.homEquiv ((cofInclusion cof).obj qY.Q) Y).symm qY.q ≫ f
  calc
    _ = (adj.homEquiv ((cofInclusion cof).obj qY.Q) Z).symm
          ((cofInclusion cof).map m ≫ qZ.q) := by
            rw [← adj.homEquiv_naturality_left_symm]
    _ = (adj.homEquiv ((cofInclusion cof).obj qY.Q) Z).symm
          (qY.q ≫ R.map f) := by
            rw [resolutionMap_fac]
    _ = (adj.homEquiv ((cofInclusion cof).obj qY.Q) Y).symm qY.q ≫ f :=
          adj.homEquiv_naturality_right_symm qY.q f

noncomputable def leftDerivedLocalizer {D : Type u₂} [Category.{v₂} D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (hC : IsSemiModelCategory C cof fib W)
    {WD : MorphismProperty D} (hR : WD = W.inverseImage R)
    (hunit : ∀ X : C, IsCofibrantFor cof X → W (adj.unit.app X)) :
    LocalizerMorphism (cofWeakEquivalences cof W) WD where
  functor := cofInclusion cof ⋙ L
  map X Y f hf := by
    letI : W.HasTwoOutOfThreeProperty := IsSemiModelCategory.twoOutOfThree hC
    have hηX := hunit ((cofInclusion cof).obj X) X.property
    have hηY := hunit ((cofInclusion cof).obj Y) Y.property
    have hnat := adj.unit.naturality ((cofInclusion cof).map f)
    have hnat' :
        (cofInclusion cof).map f ≫ adj.unit.app ((cofInclusion cof).obj Y) =
          adj.unit.app ((cofInclusion cof).obj X) ≫
            R.map (L.map ((cofInclusion cof).map f)) := by
      simpa only [Functor.id_map, Functor.comp_map] using hnat
    have hcomp : W ((cofInclusion cof).map f ≫ adj.unit.app ((cofInclusion cof).obj Y)) :=
      W.comp_mem _ _ hf hηY
    have hcomp' : W (adj.unit.app ((cofInclusion cof).obj X) ≫
        R.map (L.map ((cofInclusion cof).map f))) := by
      rw [hnat'] at hcomp
      exact hcomp
    have hRmap : W (R.map (L.map ((cofInclusion cof).map f))) :=
      W.of_precomp _ _ hηX hcomp'
    change WD (L.map ((cofInclusion cof).map f))
    rw [hR]
    exact hRmap

theorem resolvedRightLocalizer {D : Type u₂} [Category.{v₂} D]
    {R : D ⥤ C} (hC : IsSemiModelCategory C cof fib W) {WD : MorphismProperty D}
    (hR : WD = W.inverseImage R) :
    WD.IsInvertedBy (R ⋙ cofibrantResolutionFunctor cof fib W hC) := by
  intro Y Z f hf
  have hRf : W (R.map f) := by
    rw [hR] at hf
    change W (R.map f) at hf
    exact hf
  exact resolutionFunctor_inverts cof fib W hC (R.map f) hRf

noncomputable def leftDerivedLocalizedFunctor {D : Type u₂} [Category.{v₂} D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (hC : IsSemiModelCategory C cof fib W)
    {WD : MorphismProperty D} (hR : WD = W.inverseImage R)
    (hunit : ∀ X : C, IsCofibrantFor cof X → W (adj.unit.app X)) :
    (cofWeakEquivalences cof W).Localization ⥤ WD.Localization :=
  (leftDerivedLocalizer cof fib W adj hC hR hunit).localizedFunctor
    (cofWeakEquivalences cof W).Q WD.Q

noncomputable def resolvedRightLocalizedFunctor {D : Type u₂} [Category.{v₂} D]
    {R : D ⥤ C} (hC : IsSemiModelCategory C cof fib W) {WD : MorphismProperty D}
    (hR : WD = W.inverseImage R) :
    WD.Localization ⥤ (cofWeakEquivalences cof W).Localization :=
  Localization.lift (R ⋙ cofibrantResolutionFunctor cof fib W hC)
    (resolvedRightLocalizer cof fib W hC hR) WD.Q

noncomputable def leftDerivedLocalizedFac {D : Type u₂} [Category.{v₂} D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (hC : IsSemiModelCategory C cof fib W)
    {WD : MorphismProperty D} (hR : WD = W.inverseImage R)
    (hunit : ∀ X : C, IsCofibrantFor cof X → W (adj.unit.app X)) :
    (cofWeakEquivalences cof W).Q ⋙
        leftDerivedLocalizedFunctor cof fib W adj hC hR hunit ≅
      cofInclusion cof ⋙ L ⋙ WD.Q :=
  Localization.fac _ _ _

noncomputable def resolvedRightLocalizedFac {D : Type u₂} [Category.{v₂} D]
    {R : D ⥤ C} (hC : IsSemiModelCategory C cof fib W) {WD : MorphismProperty D}
    (hR : WD = W.inverseImage R) :
    WD.Q ⋙ resolvedRightLocalizedFunctor cof fib W hC hR ≅
      R ⋙ cofibrantResolutionFunctor cof fib W hC :=
  Localization.fac _ _ _

noncomputable def adjDerivedCounitNatIso {D : Type u₂} [Category.{v₂} D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (hC : IsSemiModelCategory C cof fib W) {WD : MorphismProperty D}
    (hR : WD = W.inverseImage R)
    (hunit : ∀ X : C, IsCofibrantFor cof X → W (adj.unit.app X)) :
    R ⋙ cofibrantResolutionFunctor cof fib W hC ⋙
        leftDerivedLocalizedFunctor cof fib W adj hC hR hunit ≅ WD.Q := by
  let F := leftDerivedLocalizedFunctor cof fib W adj hC hR hunit
  let facF := leftDerivedLocalizedFac cof fib W adj hC hR hunit
  refine NatIso.ofComponents (fun Y => ?_) (fun {Y Z} f => ?_)
  · let q := cofibrantResolution cof fib W hC (R.obj Y)
    let p := adjResolutionCounit cof fib W adj hC Y
    have hp : WD p := adjResolutionCounit_we cof fib W adj hC hR hunit Y
    have hmap : IsIso (WD.Q.map p) := Localization.inverts WD.Q WD p hp
    letI := hmap
    exact (asIso (facF.hom.app q.Q)).trans (asIso (WD.Q.map p))
  · let qY := cofibrantResolution cof fib W hC (R.obj Y)
    let qZ := cofibrantResolution cof fib W hC (R.obj Z)
    let m := resolutionMap cof fib W hC (R.map f)
    have hfac :
        F.map ((cofWeakEquivalences cof W).Q.map m) ≫ facF.hom.app qZ.Q =
          facF.hom.app qY.Q ≫
            WD.Q.map (L.map ((cofInclusion cof).map m)) := by
      simpa only [Functor.comp_map] using facF.hom.naturality m
    change F.map ((cofWeakEquivalences cof W).Q.map m) ≫
          (facF.hom.app qZ.Q ≫
            WD.Q.map (adjResolutionCounit cof fib W adj hC Z)) =
        (facF.hom.app qY.Q ≫
          WD.Q.map (adjResolutionCounit cof fib W adj hC Y)) ≫ WD.Q.map f
    calc
      F.map ((cofWeakEquivalences cof W).Q.map m) ≫
          (facF.hom.app qZ.Q ≫
            WD.Q.map (adjResolutionCounit cof fib W adj hC Z)) =
        (F.map ((cofWeakEquivalences cof W).Q.map m) ≫ facF.hom.app qZ.Q) ≫
          WD.Q.map (adjResolutionCounit cof fib W adj hC Z) := by
            rw [Category.assoc]
      _ = (facF.hom.app qY.Q ≫
            WD.Q.map (L.map ((cofInclusion cof).map m))) ≫
          WD.Q.map (adjResolutionCounit cof fib W adj hC Z) := by rw [hfac]
      _ = facF.hom.app qY.Q ≫
          (WD.Q.map (L.map ((cofInclusion cof).map m)) ≫
            WD.Q.map (adjResolutionCounit cof fib W adj hC Z)) :=
              Category.assoc _ _ _
      _ = facF.hom.app qY.Q ≫
          WD.Q.map (adjResolutionCounit cof fib W adj hC Y ≫ f) := by
            rw [← WD.Q.map_comp, adjResolutionCounit_naturality]
      _ = (facF.hom.app qY.Q ≫
            WD.Q.map (adjResolutionCounit cof fib W adj hC Y)) ≫ WD.Q.map f := by
            rw [WD.Q.map_comp, Category.assoc]

noncomputable def derivedAdjunctionEquivalence {D : Type u₂} [Category.{v₂} D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (hC : IsSemiModelCategory C cof fib W) {WD : MorphismProperty D}
    (hR : WD = W.inverseImage R)
    (hunit : ∀ X : C, IsCofibrantFor cof X → W (adj.unit.app X)) :
    (cofWeakEquivalences cof W).Localization ≌ WD.Localization := by
  let Wc := cofWeakEquivalences cof W
  let F := leftDerivedLocalizedFunctor cof fib W adj hC hR hunit
  let G := resolvedRightLocalizedFunctor cof fib W hC hR
  let facF := leftDerivedLocalizedFac cof fib W adj hC hR hunit
  let facG := resolvedRightLocalizedFac cof fib W hC hR
  let eFG : Wc.Q ⋙ (F ⋙ G) ≅
      cofInclusion cof ⋙ L ⋙ R ⋙ cofibrantResolutionFunctor cof fib W hC :=
    (Functor.associator Wc.Q F G).symm ≪≫
      Functor.isoWhiskerRight facF G ≪≫
      Functor.associator (cofInclusion cof ⋙ L) WD.Q G ≪≫
      Functor.isoWhiskerLeft (cofInclusion cof ⋙ L) facG ≪≫
      (Functor.associator (cofInclusion cof ⋙ L) R
        (cofibrantResolutionFunctor cof fib W hC)).symm
  let unit := Localization.liftNatIso Wc.Q Wc
    (Wc.Q ⋙ 𝟭 Wc.Localization) (Wc.Q ⋙ (F ⋙ G))
    (𝟭 Wc.Localization) (F ⋙ G)
    (Functor.rightUnitor Wc.Q ≪≫
      adjDerivedUnitNatIso cof fib W adj hC hunit ≪≫ eFG.symm)
  let counit := Localization.liftNatIso WD.Q WD
    (WD.Q ⋙ (G ⋙ F)) WD.Q (G ⋙ F) (𝟭 WD.Localization)
    ((Functor.associator WD.Q G F).symm ≪≫
      Functor.isoWhiskerRight facG F ≪≫
      adjDerivedCounitNatIso cof fib W adj hC hR hunit)
  exact CategoryTheory.Equivalence.mk F G unit counit

end SemiModel

namespace Packages

theorem isLocalizedEquivalence_of_adjunction_proof
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {cof fib W : MorphismProperty C} (hC : IsSemiModelCategory C cof fib W)
    (_hfib : ∀ X : C, IsFibrantFor fib X) {WD : MorphismProperty D}
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (hR : WD = W.inverseImage R)
    (hunit : ∀ X : C, IsCofibrantFor cof X → W (adj.unit.app X)) :
    (LocalizerMorphism.ofEq hR).IsLocalizedEquivalence := by
  let G := resolvedRightLocalizedFunctor cof fib W hC hR
  let ι := inclusionLocalizedFunctor cof W
  let H := G ⋙ ι
  have hG : G.IsEquivalence :=
    Equivalence.isEquivalence_inverse
      (derivedAdjunctionEquivalence cof fib W adj hC hR hunit)
  have hι : ι.IsEquivalence :=
    Equivalence.isEquivalence_inverse (cofibrantLocalizationEquivalence cof fib W hC)
  letI : G.IsEquivalence := hG
  letI : ι.IsEquivalence := hι
  haveI : H.IsEquivalence := by
    dsimp [H]
    infer_instance
  let e : WD.Q ⋙ H ≅ R ⋙ W.Q :=
    (Functor.associator WD.Q G ι).symm ≪≫
      Functor.isoWhiskerRight
        (resolvedRightLocalizedFac cof fib W hC hR) ι ≪≫
      Functor.associator R (cofibrantResolutionFunctor cof fib W hC) ι ≪≫
      Functor.isoWhiskerLeft R (resolutionInclusionNatIso cof fib W hC)
  let Φ := LocalizerMorphism.ofEq hR
  letI : CatCommSq Φ.functor WD.Q W.Q H := by
    change CatCommSq R WD.Q W.Q H
    exact ⟨e.symm⟩
  exact LocalizerMorphism.IsLocalizedEquivalence.mk' Φ WD.Q W.Q H

end Packages

end HomotopyHypothesis.Localization.Adjunction

#print axioms HomotopyHypothesis.Localization.Adjunction.Packages.isLocalizedEquivalence_of_adjunction_proof
