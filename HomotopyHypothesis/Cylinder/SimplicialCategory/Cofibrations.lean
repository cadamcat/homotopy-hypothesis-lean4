import HomotopyHypothesis.Cylinder.SimplicialCategory.FreeAlgKan
import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.Packages.Classical.FinCellIsCylinderCategory
import HomotopyHypothesis.Blueprint.Henry.Packages.Classical.IsCylinderMorphismToFinCell
import HomotopyHypothesis.Blueprint.Henry.Packages.Simplicial.ExistsStandardRealization
import HomotopyHypothesis.Blueprint.Henry.Packages.Simplicial.StandardRealizationIsHomotopyFullyFaithful
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Cylinder.SemisimplicialCategory.CylinderAssembly
import HomotopyHypothesis.Cylinder.SemisimplicialCategory.WeakEquivalences
/-!
# Cofibration category structure, cobase change of trivial cofibrations, and retractions in `C^Δ`

This file proves:
1. `cDelta_isCofibrationCategory : IsCofibrationCategory CDelta.{u}`
2. `cDelta_trivialCofibration_cobaseChange`: pushouts of trivial cofibrations in `CDelta.{u}`
   are weak equivalences
3. `cDelta_exists_retraction`: every trivial cofibration in `CDelta.{u}` admits a retraction
4. 2-out-of-3 for weak equivalences in `CDelta.{u}`
5. Functoriality of `freeAlgKan` and pushouts of subfunctor unions `S₁ ⊔ S₂`
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra Opposite ConcreteCategory

namespace HomotopyHypothesis.Cylinder.SimplicialCategory

open HomotopyHypothesis.Henry

/-!
## Cellular maps and pushouts in `AlgKan` and `CDelta`
-/

lemma cellularMaps_of_isCellAttachment {X Y : AlgKan.{u}} {j : X ⟶ Y}
    (hj : AlgKan.IsCellAttachment j) : AlgKan.cellularMaps j :=
  .of j (Or.inl hj)

lemma cellularMaps_of_isIso {X Y : AlgKan.{u}} (f : X ⟶ Y) [IsIso f] :
    AlgKan.cellularMaps f :=
  .of f (Or.inr (MorphismProperty.isomorphisms.infer_property f))

instance : (AlgKan.cellularMaps.{u}).IsMultiplicative :=
  inferInstanceAs ((_ : MorphismProperty AlgKan.{u}).multiplicativeClosure.IsMultiplicative)

lemma isFinitelyCellular_of_isIso {X Y : AlgKan.{u}} (f : X ⟶ Y) [IsIso f]
    (hX : AlgKan.IsFinitelyCellular X) : AlgKan.IsFinitelyCellular Y := by
  induction hX generalizing Y with
  | initial A hIA =>
    rcases hIA with ⟨hIA⟩
    exact AlgKan.IsFinitelyCellular.initial Y ⟨IsInitial.ofIso hIA (asIso f)⟩
  | @attach A B j hA hj _ =>
    rcases hj with ⟨n, a, y, hcomm, huniv⟩
    refine AlgKan.IsFinitelyCellular.attach (j ≫ f) hA ⟨n, a, y ≫ f.hom, ?_, ?_⟩
    · rw [← Category.assoc, hcomm, Category.assoc]
      rfl
    · intro Z g z hz
      obtain ⟨g₀, ⟨hg₀l, hg₀r⟩, hg₀uniq⟩ := huniv Z g z hz
      refine ⟨inv f ≫ g₀, ⟨?_, ?_⟩, ?_⟩
      · rw [Category.assoc, IsIso.hom_inv_id_assoc, hg₀l]
      · have hfinv : f.hom ≫ (inv f).hom = 𝟙 _ := congrArg AlgKan.Hom.hom (IsIso.hom_inv_id f)
        change (y ≫ f.hom) ≫ (inv f).hom ≫ g₀.hom = z
        rw [Category.assoc y, ← Category.assoc f.hom, hfinv, Category.id_comp, hg₀r]
      · rintro g' ⟨hg'l, hg'r⟩
        have hg'0 : f ≫ g' = g₀ := by
          apply hg₀uniq
          refine ⟨?_, hg'r⟩
          rw [← Category.assoc, hg'l]
        rw [← hg'0, IsIso.inv_hom_id_assoc]

lemma isFinitelyCellular_of_cellularMaps {X Y : AlgKan.{u}} {f : X ⟶ Y}
    (hf : AlgKan.cellularMaps f) (hX : AlgKan.IsFinitelyCellular X) :
    AlgKan.IsFinitelyCellular Y := by
  induction hf with
  | of f hf =>
    rcases hf with hf | hf
    · exact AlgKan.IsFinitelyCellular.attach f hX hf
    · have : IsIso f := hf
      exact isFinitelyCellular_of_isIso f hX
  | id A => exact hX
  | @comp_of A B Z i g hi hg ih =>
    have hB : AlgKan.IsFinitelyCellular B := ih hX
    rcases hg with hg | hg
    · exact AlgKan.IsFinitelyCellular.attach g hB hg
    · have : IsIso g := hg
      exact isFinitelyCellular_of_isIso g hB

lemma emptyAlgKanTo_cellularMaps {X : AlgKan.{u}} (hX : AlgKan.IsFinitelyCellular X) :
    AlgKan.cellularMaps (emptyAlgKanTo X) := by
  induction hX with
  | initial A hIA =>
    rcases hIA with ⟨hIA⟩
    have heq : emptyAlgKanTo A = (emptyAlgKanIsInitial.uniqueUpToIso hIA).hom :=
      emptyAlgKanIsInitial.hom_ext _ _
    rw [heq]
    exact cellularMaps_of_isIso _
  | attach j hA hj ih =>
    have heq : emptyAlgKanTo _ = emptyAlgKanTo _ ≫ j :=
      emptyAlgKanIsInitial.hom_ext _ _
    rw [heq]
    exact MorphismProperty.comp_mem _ _ _ ih (cellularMaps_of_isCellAttachment hj)

/-- Pushouts along `cellularMaps` exist in `AlgKan` and preserve `cellularMaps`. -/
theorem exists_pushout_of_cellularMaps {A B X : AlgKan.{u}} (i : A ⟶ B)
    (hi : AlgKan.cellularMaps i) (f : A ⟶ X) :
    ∃ (P : AlgKan.{u}) (k : B ⟶ P) (j : X ⟶ P),
      AlgKan.cellularMaps j ∧ IsPushout i f k j := by
  induction hi generalizing X with
  | of i hi =>
    rcases hi with hi | hi
    · obtain ⟨P₁, j₁, k₁, hj₁, hpo₁⟩ := exists_pushout_of_isCellAttachment i hi f
      exact ⟨P₁, k₁, j₁, cellularMaps_of_isCellAttachment hj₁, hpo₁⟩
    · have : IsIso i := hi
      exact ⟨X, inv i ≫ f, 𝟙 X, MorphismProperty.id_mem _ X, IsPushout.of_horiz_isIso ⟨by simp⟩⟩
  | id A =>
    exact ⟨X, f, 𝟙 X, MorphismProperty.id_mem _ X, IsPushout.of_horiz_isIso ⟨by simp⟩⟩
  | @comp_of A B Z i₁ i₂ hi₁ hi₂ ih =>
    obtain ⟨P₁, k₁, j₁, hj₁, hpo₁⟩ := ih f
    have hstep2 : ∃ (P₂ : AlgKan.{u}) (k₂ : Z ⟶ P₂) (j₂ : P₁ ⟶ P₂),
        AlgKan.cellularMaps j₂ ∧ IsPushout i₂ k₁ k₂ j₂ := by
      rcases hi₂ with hi₂ | hi₂
      · obtain ⟨P₂, j₂, k₂, hj₂, hpo₂⟩ := exists_pushout_of_isCellAttachment i₂ hi₂ k₁
        exact ⟨P₂, k₂, j₂, cellularMaps_of_isCellAttachment hj₂, hpo₂⟩
      · have : IsIso i₂ := hi₂
        exact ⟨P₁, inv i₂ ≫ k₁, 𝟙 P₁, MorphismProperty.id_mem _ P₁,
          IsPushout.of_horiz_isIso ⟨by simp⟩⟩
    obtain ⟨P₂, k₂, j₂, hj₂, hpo₂⟩ := hstep2
    exact ⟨P₂, k₂, j₁ ≫ j₂, MorphismProperty.comp_mem _ _ _ hj₁ hj₂, hpo₁.paste_horiz hpo₂⟩

/-- If four objects in `CDelta` form a pushout square in `AlgKan`, they also form a pushout square
in `CDelta`. -/
lemma isPushout_cDelta_of_algKan {A B X P : CDelta.{u}}
    (i : A ⟶ B) (f : A ⟶ X) (k : B ⟶ P) (j : X ⟶ P)
    (h : IsPushout i.hom f.hom k.hom j.hom) :
    IsPushout i f k j :=
  IsPushout.of_map_of_faithful (ObjectProperty.ι _) h

/-- `CDelta` has pushouts along cofibrations. -/
theorem cDelta_hasPushout {A B X : CDelta.{u}} (i : A ⟶ B) (f : A ⟶ X)
    (hi : cofibrations CDelta.{u} i) : HasPushout i f := by
  obtain ⟨P₀, k₀, j₀, hj₀, hpo₀⟩ := exists_pushout_of_cellularMaps i.hom hi f.hom
  let P : CDelta.{u} := ⟨P₀, isFinitelyCellular_of_cellularMaps hj₀ X.property⟩
  let k : B ⟶ P := ObjectProperty.homMk k₀
  let j : X ⟶ P := ObjectProperty.homMk j₀
  exact (isPushout_cDelta_of_algKan i f k j hpo₀).hasPushout

/-- `CDelta` is a cofibration category. -/
theorem cDelta_isCofibrationCategory : IsCofibrationCategory CDelta.{u} where
  isomorphisms_le X Y f hf := by
    have : IsIso f := hf
    have : IsIso f.hom := Functor.map_isIso (ObjectProperty.ι _) f
    exact cellularMaps_of_isIso f.hom
  isMultiplicative := inferInstanceAs
    ((AlgKan.cellularMaps.{u}.inverseImage (ObjectProperty.ι _)).IsMultiplicative)
  exists_initial := ⟨initialCDelta.{u}, ⟨initialCDeltaIsInitial.{u}⟩⟩
  initial_cofibration {I} hI X := by
    let e : I ≅ initialCDelta.{u} := hI.uniqueUpToIso initialCDeltaIsInitial
    have heq : hI.to X = e.hom ≫ initialCDeltaIsInitial.to X := hI.hom_ext _ _
    rw [heq]
    change AlgKan.cellularMaps (e.hom.hom ≫ (initialCDeltaIsInitial.to X).hom)
    have : IsIso e.hom.hom := Functor.map_isIso (ObjectProperty.ι _) e.hom
    have h1 : AlgKan.cellularMaps e.hom.hom := cellularMaps_of_isIso e.hom.hom
    have h2 : (initialCDeltaIsInitial.to X).hom = emptyAlgKanTo X.obj :=
      emptyAlgKanIsInitial.hom_ext _ _
    rw [h2]
    exact MorphismProperty.comp_mem _ _ _ h1 (emptyAlgKanTo_cellularMaps X.property)
  hasPushout := cDelta_hasPushout
  isStableUnderCobaseChange := ⟨by
    intro A A' B B' f g f' g' sq hf
    obtain ⟨P₀, k₀, j₀, hj₀, hpo₀⟩ := exists_pushout_of_cellularMaps f.hom hf g.hom
    let P : CDelta.{u} := ⟨P₀, isFinitelyCellular_of_cellularMaps hj₀ B.property⟩
    let k : A' ⟶ P := ObjectProperty.homMk k₀
    let j : B ⟶ P := ObjectProperty.homMk j₀
    have sq₀ : IsPushout f g k j := isPushout_cDelta_of_algKan f g k j hpo₀
    have sq₁ : IsPushout f g g' f' := sq.flip
    let e : P ≅ B' :=
      { hom := sq₀.desc g' f' sq₁.w
        inv := sq₁.desc k j sq₀.w
        hom_inv_id := sq₀.hom_ext
          (by rw [← Category.assoc, sq₀.inl_desc, sq₁.inl_desc, Category.comp_id])
          (by rw [← Category.assoc, sq₀.inr_desc, sq₁.inr_desc, Category.comp_id])
        inv_hom_id := sq₁.hom_ext
          (by rw [← Category.assoc, sq₁.inl_desc, sq₀.inl_desc, Category.comp_id])
          (by rw [← Category.assoc, sq₁.inr_desc, sq₀.inr_desc, Category.comp_id]) }
    have : IsIso e.hom.hom := ((ObjectProperty.ι _).mapIso e).isIso_hom
    have h1 : AlgKan.cellularMaps (j₀ ≫ e.hom.hom) :=
      MorphismProperty.comp_mem _ _ _ hj₀ (cellularMaps_of_isIso e.hom.hom)
    have hje : j ≫ e.hom = f' := sq₀.inr_desc g' f' sq₁.w
    rw [← hje]
    exact h1⟩

/-!
## Cobase change of trivial cofibrations, 2-out-of-3, and retractions in `CDelta`
-/

/-- 2-out-of-3 (left cancellation) for weak equivalences in `CDelta`. -/
lemma cDelta_weakEquivalence_of_comp_left {X Y Z : CDelta.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : weakEquivalences CDelta.{u} f) (hfg : weakEquivalences CDelta.{u} (f ≫ g)) :
    weakEquivalences CDelta.{u} g := by
  have hW := Cylinder.SemisimplicialCategory.cDelta_weakEquivalences_isWeakEquivalenceClass.{u}
  have h1 : weakEquivalences CDelta.{u} (𝟙 X ≫ f) := by simpa using hf
  exact (hW.2.2.1 (𝟙 X) f g h1 hfg).2.2.1

/-- 2-out-of-3 (right cancellation) for weak equivalences in `CDelta`. -/
lemma cDelta_weakEquivalence_of_comp_right {X Y Z : CDelta.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg : weakEquivalences CDelta.{u} g) (hfg : weakEquivalences CDelta.{u} (f ≫ g)) :
    weakEquivalences CDelta.{u} f := by
  have hW := Cylinder.SemisimplicialCategory.cDelta_weakEquivalences_isWeakEquivalenceClass.{u}
  have h2 : weakEquivalences CDelta.{u} (g ≫ 𝟙 Z) := by simpa using hg
  exact (hW.2.2.1 f g (𝟙 Z) hfg h2).1

/-- Pushouts of trivial cofibrations in `CDelta` are weak equivalences. -/
theorem cDelta_trivialCofibration_cobaseChange {A B X P : CDelta.{u}}
    (i : A ⟶ B) (f : A ⟶ X) (k : B ⟶ P) (j : X ⟶ P)
    (hpo : IsPushout i f k j) (hi : cofibrations CDelta.{u} i)
    (hwi : weakEquivalences CDelta.{u} i) :
    weakEquivalences CDelta.{u} j := by
  have hW := Cylinder.SemisimplicialCategory.cDelta_weakEquivalences_isWeakEquivalenceClass.{u}
  have hcof := cDelta_isCofibrationCategory.{u}
  have hpo_id : IsPushout (𝟙 A) f f (𝟙 X) := IsPushout.of_horiz_isIso ⟨by simp⟩
  have hidA_cof : cofibrations CDelta.{u} (𝟙 A) :=
    hcof.isomorphisms_le (𝟙 A) (MorphismProperty.isomorphisms.infer_property (𝟙 A))
  have hidA_weq : weakEquivalences CDelta.{u} (𝟙 A) :=
    hW.1 (𝟙 A) (MorphismProperty.isomorphisms.infer_property (𝟙 A))
  have hidX_weq : weakEquivalences CDelta.{u} (𝟙 X) :=
    hW.1 (𝟙 X) (MorphismProperty.isomorphisms.infer_property (𝟙 X))
  simpa using hW.2.2.2 (𝟙 A) f f (𝟙 X) i f k j (𝟙 A) i (𝟙 X) j
    hpo_id hpo hidA_cof hi hidA_weq hwi hidX_weq rfl (by simp) hpo.w.symm rfl

/-- Every trivial cofibration in `CDelta` admits a retraction. -/
theorem cDelta_exists_retraction {A B : CDelta.{u}} (i : A ⟶ B)
    (hi : cofibrations CDelta.{u} i) (hwi : weakEquivalences CDelta.{u} i) :
    ∃ r : B ⟶ A, i ≫ r = 𝟙 A := by
  obtain ⟨R, hR⟩ := Packages.exists_standardRealization.{u}
  let F := hR.isCellularRealization.toFinCell
  have hF_cyl : IsCylinderMorphism F :=
    Packages.isCylinderMorphism_toFinCell hR.isCellularRealization
  have hFinCell : IsCylinderCategory FinCell.{u} := Packages.finCell_isCylinderCategory.{u}
  have hFi_cof : cofibrations FinCell.{u} (F.map i) := hF_cyl.map_cofibration i hi
  have hFi_weq : weakEquivalences FinCell.{u} (F.map i) := hF_cyl.map_weakEquivalence i hwi
  obtain ⟨r₀, hr₀⟩ := hFinCell.exists_retraction (F.map i) hFi_cof hFi_weq
  have hFF : IsHomotopyFullyFaithful F := Packages.standardRealization_isHomotopyFullyFaithful hR
  obtain ⟨r, hr, _⟩ := hFF i hi (𝟙 A) r₀ (by rw [hr₀, F.map_id])
  exact ⟨r, hr⟩

/-!
## Functoriality of `freeAlgKan` and pushouts of subfunctor unions
-/

/-- The morphism `freeAlgKan A ⟶ freeAlgKan B` induced by a semi-simplicial map `f : A ⟶ B`. -/
noncomputable def freeAlgKanMap {A B : SemiSSet.{u}} (f : A ⟶ B) :
    freeAlgKan A ⟶ freeAlgKan B :=
  (freeAlgKan_isFreeOn A (freeAlgKan B) (f ≫ freeAlgKanUnit B)).choose

@[simp]
lemma freeAlgKanUnit_comp_freeAlgKanMap {A B : SemiSSet.{u}} (f : A ⟶ B) :
    freeAlgKanUnit A ≫ (freeAlgKanMap f).hom = f ≫ freeAlgKanUnit B :=
  (freeAlgKan_isFreeOn A (freeAlgKan B) (f ≫ freeAlgKanUnit B)).choose_spec.1

lemma freeAlgKan_hom_ext {A : SemiSSet.{u}} {Z : AlgKan.{u}} {g₁ g₂ : freeAlgKan A ⟶ Z}
    (h : freeAlgKanUnit A ≫ g₁.hom = freeAlgKanUnit A ≫ g₂.hom) :
    g₁ = g₂ := by
  obtain ⟨u, _, huniq⟩ := freeAlgKan_isFreeOn A Z (freeAlgKanUnit A ≫ g₂.hom)
  exact (huniq g₁ h).trans (huniq g₂ rfl).symm

@[simp]
lemma freeAlgKanMap_id (A : SemiSSet.{u}) :
    freeAlgKanMap (𝟙 A) = 𝟙 (freeAlgKan A) := by
  apply freeAlgKan_hom_ext
  change freeAlgKanUnit A ≫ (freeAlgKanMap (𝟙 A)).hom = freeAlgKanUnit A ≫ 𝟙 (freeAlgKan A).X
  rw [freeAlgKanUnit_comp_freeAlgKanMap, Category.id_comp, Category.comp_id]

@[simp]
lemma freeAlgKanMap_comp {A B C : SemiSSet.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    freeAlgKanMap (f ≫ g) = freeAlgKanMap f ≫ freeAlgKanMap g := by
  apply freeAlgKan_hom_ext
  have h1 := freeAlgKanUnit_comp_freeAlgKanMap (f ≫ g)
  have h2 := freeAlgKanUnit_comp_freeAlgKanMap f
  have h3 := freeAlgKanUnit_comp_freeAlgKanMap g
  calc freeAlgKanUnit A ≫ (freeAlgKanMap (f ≫ g)).hom
    _ = (f ≫ g) ≫ freeAlgKanUnit C := h1
    _ = f ≫ (g ≫ freeAlgKanUnit C) := Category.assoc f g _
    _ = f ≫ (freeAlgKanUnit B ≫ (freeAlgKanMap g).hom) := by rw [← h3]
    _ = (f ≫ freeAlgKanUnit B) ≫ (freeAlgKanMap g).hom := (Category.assoc f _ _).symm
    _ = (freeAlgKanUnit A ≫ (freeAlgKanMap f).hom) ≫ (freeAlgKanMap g).hom := by rw [← h2]
    _ = freeAlgKanUnit A ≫ (freeAlgKanMap f).hom ≫ (freeAlgKanMap g).hom := Category.assoc _ _ _

/-- Action at `Δ` of the pushout map `(S₁ ⊔ S₂).toFunctor ⟶ Z`. -/
noncomputable def subfunctorSupDescApp {B Z : SemiSSet.{u}} (S₁ S₂ : Subfunctor B)
    (u₁ : S₁.toFunctor ⟶ Z) (u₂ : S₂.toFunctor ⟶ Z)
    (Δ : Henry.SemiSimplexCategoryᵒᵖ) (x : (S₁ ⊔ S₂).toFunctor.obj Δ) : Z.obj Δ := by
  classical
  exact if hx₁ : x.1 ∈ S₁.obj Δ then
    u₁.app Δ ⟨x.1, hx₁⟩
  else
    u₂.app Δ ⟨x.1, by
      rcases x.2 with h1 | h2
      · exact (hx₁ h1).elim
      · exact h2⟩

lemma subfunctorSupDescApp_of_mem_left {B Z : SemiSSet.{u}} (S₁ S₂ : Subfunctor B)
    (u₁ : S₁.toFunctor ⟶ Z) (u₂ : S₂.toFunctor ⟶ Z)
    {Δ : Henry.SemiSimplexCategoryᵒᵖ} (x : (S₁ ⊔ S₂).toFunctor.obj Δ) (hx₁ : x.1 ∈ S₁.obj Δ) :
    subfunctorSupDescApp S₁ S₂ u₁ u₂ Δ x = u₁.app Δ ⟨x.1, hx₁⟩ := by
  dsimp [subfunctorSupDescApp]
  rw [dite_eq_left_of_eq_true (eq_true hx₁)]

lemma subfunctorSupDescApp_of_mem_right {B Z : SemiSSet.{u}} (S₁ S₂ : Subfunctor B)
    (u₁ : S₁.toFunctor ⟶ Z) (u₂ : S₂.toFunctor ⟶ Z)
    (hu : Subfunctor.homOfLe (inf_le_left : S₁ ⊓ S₂ ≤ S₁) ≫ u₁ =
      Subfunctor.homOfLe (inf_le_right : S₁ ⊓ S₂ ≤ S₂) ≫ u₂)
    {Δ : Henry.SemiSimplexCategoryᵒᵖ} (x : (S₁ ⊔ S₂).toFunctor.obj Δ) (hx₂ : x.1 ∈ S₂.obj Δ) :
    subfunctorSupDescApp S₁ S₂ u₁ u₂ Δ x = u₂.app Δ ⟨x.1, hx₂⟩ := by
  by_cases hx₁ : x.1 ∈ S₁.obj Δ
  · rw [subfunctorSupDescApp_of_mem_left S₁ S₂ u₁ u₂ x hx₁]
    exact ConcreteCategory.congr_hom (congr_app hu Δ) ⟨x.1, ⟨hx₁, hx₂⟩⟩
  · dsimp [subfunctorSupDescApp]
    rw [dite_eq_right_of_eq_false (eq_false hx₁)]

/-- Universal morphism `(S₁ ⊔ S₂).toFunctor ⟶ Z` from compatible morphisms on `S₁` and `S₂`. -/
@[simps]
noncomputable def subfunctorSupDesc {B Z : SemiSSet.{u}} (S₁ S₂ : Subfunctor B)
    (u₁ : S₁.toFunctor ⟶ Z) (u₂ : S₂.toFunctor ⟶ Z)
    (hu : Subfunctor.homOfLe (inf_le_left : S₁ ⊓ S₂ ≤ S₁) ≫ u₁ =
      Subfunctor.homOfLe (inf_le_right : S₁ ⊓ S₂ ≤ S₂) ≫ u₂) :
    (S₁ ⊔ S₂).toFunctor ⟶ Z where
  app Δ := ↾(subfunctorSupDescApp S₁ S₂ u₁ u₂ Δ)
  naturality {Δ Δ'} f := by
    ext x
    rcases x.2 with hx₁ | hx₂
    · have hfx₁ : B.map f x.1 ∈ S₁.obj Δ' := S₁.map f hx₁
      change subfunctorSupDescApp S₁ S₂ u₁ u₂ Δ' ((S₁ ⊔ S₂).toFunctor.map f x) =
        Z.map f (subfunctorSupDescApp S₁ S₂ u₁ u₂ Δ x)
      rw [subfunctorSupDescApp_of_mem_left S₁ S₂ u₁ u₂ x hx₁,
        subfunctorSupDescApp_of_mem_left S₁ S₂ u₁ u₂ _ hfx₁]
      exact NatTrans.naturality_apply u₁ f ⟨x.1, hx₁⟩
    · have hfx₂ : B.map f x.1 ∈ S₂.obj Δ' := S₂.map f hx₂
      change subfunctorSupDescApp S₁ S₂ u₁ u₂ Δ' ((S₁ ⊔ S₂).toFunctor.map f x) =
        Z.map f (subfunctorSupDescApp S₁ S₂ u₁ u₂ Δ x)
      rw [subfunctorSupDescApp_of_mem_right S₁ S₂ u₁ u₂ hu x hx₂,
        subfunctorSupDescApp_of_mem_right S₁ S₂ u₁ u₂ hu _ hfx₂]
      exact NatTrans.naturality_apply u₂ f ⟨x.1, hx₂⟩

@[simp]
lemma homOfLe_left_comp_subfunctorSupDesc {B Z : SemiSSet.{u}} (S₁ S₂ : Subfunctor B)
    (u₁ : S₁.toFunctor ⟶ Z) (u₂ : S₂.toFunctor ⟶ Z)
    (hu : Subfunctor.homOfLe (inf_le_left : S₁ ⊓ S₂ ≤ S₁) ≫ u₁ =
      Subfunctor.homOfLe (inf_le_right : S₁ ⊓ S₂ ≤ S₂) ≫ u₂) :
    Subfunctor.homOfLe (le_sup_left : S₁ ≤ S₁ ⊔ S₂) ≫ subfunctorSupDesc S₁ S₂ u₁ u₂ hu = u₁ := by
  ext Δ ⟨y, hy⟩
  exact subfunctorSupDescApp_of_mem_left S₁ S₂ u₁ u₂ ⟨y, Or.inl hy⟩ hy

@[simp]
lemma homOfLe_right_comp_subfunctorSupDesc {B Z : SemiSSet.{u}} (S₁ S₂ : Subfunctor B)
    (u₁ : S₁.toFunctor ⟶ Z) (u₂ : S₂.toFunctor ⟶ Z)
    (hu : Subfunctor.homOfLe (inf_le_left : S₁ ⊓ S₂ ≤ S₁) ≫ u₁ =
      Subfunctor.homOfLe (inf_le_right : S₁ ⊓ S₂ ≤ S₂) ≫ u₂) :
    Subfunctor.homOfLe (le_sup_right : S₂ ≤ S₁ ⊔ S₂) ≫ subfunctorSupDesc S₁ S₂ u₁ u₂ hu = u₂ := by
  ext Δ ⟨y, hy⟩
  exact subfunctorSupDescApp_of_mem_right S₁ S₂ u₁ u₂ hu ⟨y, Or.inr hy⟩ hy

lemma subfunctorSup_hom_ext {B Z : SemiSSet.{u}} (S₁ S₂ : Subfunctor B)
    {f₁ f₂ : (S₁ ⊔ S₂).toFunctor ⟶ Z}
    (hl : Subfunctor.homOfLe (le_sup_left : S₁ ≤ S₁ ⊔ S₂) ≫ f₁ =
      Subfunctor.homOfLe (le_sup_left : S₁ ≤ S₁ ⊔ S₂) ≫ f₂)
    (hr : Subfunctor.homOfLe (le_sup_right : S₂ ≤ S₁ ⊔ S₂) ≫ f₁ =
      Subfunctor.homOfLe (le_sup_right : S₂ ≤ S₁ ⊔ S₂) ≫ f₂) :
    f₁ = f₂ := by
  ext Δ ⟨y, hy⟩
  rcases hy with hy₁ | hy₂
  · exact ConcreteCategory.congr_hom (congr_app hl Δ) ⟨y, hy₁⟩
  · exact ConcreteCategory.congr_hom (congr_app hr Δ) ⟨y, hy₂⟩

/-- For any two subfunctors `S₁, S₂` of `B`, `freeAlgKan (S₁ ⊔ S₂).toFunctor` is the pushout in
`AlgKan` of `freeAlgKan S₁.toFunctor` and `freeAlgKan S₂.toFunctor` over
`freeAlgKan (S₁ ⊓ S₂).toFunctor`. -/
theorem isPushout_freeAlgKan_sup {B : SemiSSet.{u}} (S₁ S₂ : Subfunctor B) :
    IsPushout
      (freeAlgKanMap (Subfunctor.homOfLe (inf_le_left : S₁ ⊓ S₂ ≤ S₁)))
      (freeAlgKanMap (Subfunctor.homOfLe (inf_le_right : S₁ ⊓ S₂ ≤ S₂)))
      (freeAlgKanMap (Subfunctor.homOfLe (le_sup_left : S₁ ≤ S₁ ⊔ S₂)))
      (freeAlgKanMap (Subfunctor.homOfLe (le_sup_right : S₂ ≤ S₁ ⊔ S₂))) := by
  have hcomm_sub :
      Subfunctor.homOfLe (inf_le_left : S₁ ⊓ S₂ ≤ S₁) ≫
        Subfunctor.homOfLe (le_sup_left : S₁ ≤ S₁ ⊔ S₂) =
      Subfunctor.homOfLe (inf_le_right : S₁ ⊓ S₂ ≤ S₂) ≫
        Subfunctor.homOfLe (le_sup_right : S₂ ≤ S₁ ⊔ S₂) := by
    ext Δ x
    rfl
  have hcomm :
      freeAlgKanMap (Subfunctor.homOfLe (inf_le_left : S₁ ⊓ S₂ ≤ S₁)) ≫
        freeAlgKanMap (Subfunctor.homOfLe (le_sup_left : S₁ ≤ S₁ ⊔ S₂)) =
      freeAlgKanMap (Subfunctor.homOfLe (inf_le_right : S₁ ⊓ S₂ ≤ S₂)) ≫
        freeAlgKanMap (Subfunctor.homOfLe (le_sup_right : S₂ ≤ S₁ ⊔ S₂)) := by
    rw [← freeAlgKanMap_comp, ← freeAlgKanMap_comp, hcomm_sub]
  refine IsPushout.of_isColimit (PushoutCocone.IsColimit.mk hcomm
    (fun s => by
      have hs :
          Subfunctor.homOfLe (inf_le_left : S₁ ⊓ S₂ ≤ S₁) ≫
            (freeAlgKanUnit S₁.toFunctor ≫ s.inl.hom) =
          Subfunctor.homOfLe (inf_le_right : S₁ ⊓ S₂ ≤ S₂) ≫
            (freeAlgKanUnit S₂.toFunctor ≫ s.inr.hom) := by
        rw [← Category.assoc, ← freeAlgKanUnit_comp_freeAlgKanMap,
          ← Category.assoc, ← freeAlgKanUnit_comp_freeAlgKanMap,
          Category.assoc, Category.assoc]
        exact congrArg (freeAlgKanUnit (S₁ ⊓ S₂).toFunctor ≫ ·)
          (congrArg AlgKan.Hom.hom s.condition)
      exact (freeAlgKan_isFreeOn (S₁ ⊔ S₂).toFunctor s.pt
        (subfunctorSupDesc S₁ S₂
          (freeAlgKanUnit S₁.toFunctor ≫ s.inl.hom)
          (freeAlgKanUnit S₂.toFunctor ≫ s.inr.hom) hs)).choose)
    (fun s => by
      apply freeAlgKan_hom_ext
      change freeAlgKanUnit S₁.toFunctor ≫
        (freeAlgKanMap (Subfunctor.homOfLe (le_sup_left : S₁ ≤ S₁ ⊔ S₂))).hom ≫ _ =
        freeAlgKanUnit S₁.toFunctor ≫ s.inl.hom
      rw [← Category.assoc, freeAlgKanUnit_comp_freeAlgKanMap, Category.assoc,
        (freeAlgKan_isFreeOn (S₁ ⊔ S₂).toFunctor s.pt _).choose_spec.1,
        homOfLe_left_comp_subfunctorSupDesc])
    (fun s => by
      apply freeAlgKan_hom_ext
      change freeAlgKanUnit S₂.toFunctor ≫
        (freeAlgKanMap (Subfunctor.homOfLe (le_sup_right : S₂ ≤ S₁ ⊔ S₂))).hom ≫ _ =
        freeAlgKanUnit S₂.toFunctor ≫ s.inr.hom
      rw [← Category.assoc, freeAlgKanUnit_comp_freeAlgKanMap, Category.assoc,
        (freeAlgKan_isFreeOn (S₁ ⊔ S₂).toFunctor s.pt _).choose_spec.1,
        homOfLe_right_comp_subfunctorSupDesc])
    (fun s m hml hmr => by
      apply freeAlgKan_hom_ext
      rw [(freeAlgKan_isFreeOn (S₁ ⊔ S₂).toFunctor s.pt _).choose_spec.1]
      apply subfunctorSup_hom_ext S₁ S₂
      · rw [homOfLe_left_comp_subfunctorSupDesc, ← Category.assoc,
          ← freeAlgKanUnit_comp_freeAlgKanMap, Category.assoc, ← hml]
        rfl
      · rw [homOfLe_right_comp_subfunctorSupDesc, ← Category.assoc,
          ← freeAlgKanUnit_comp_freeAlgKanMap, Category.assoc, ← hmr]
        rfl))

end HomotopyHypothesis.Cylinder.SimplicialCategory
