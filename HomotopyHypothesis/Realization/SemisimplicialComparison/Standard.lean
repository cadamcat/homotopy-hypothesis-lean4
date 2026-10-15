import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.Packages.Classical.RealizationBoundaryRelativeFiniteCellComplex
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.HomotopyEquivalenceOfIsPushout
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Realization.SemisimplicialComparison.CDeltaFacts
import HomotopyHypothesis.Realization.SemisimplicialComparison.CellAttach
import HomotopyHypothesis.Realization.SemisimplicialComparison.Realization
import HomotopyHypothesis.Realization.SemisimplicialComparison.TopFacts
/-!
# The standard realization is a standard realization (H Def 5.2.5)

The partial left adjoint `R : C^Δ ⥤ TopCat` of the singular algebraic Kan complex functor is a
cellular realization: it sends cell attachments to pushouts of `‖∂Δ_n‖ ⟶ ‖Δ_n‖` (relative finite
cell complexes), initial objects to initial objects, pushouts along cofibrations to pushouts, and
the maps between free simplices to maps between contractible spaces; the smallest class of weak
equivalences of `C^Δ` is therefore sent to homotopy equivalences by the gluing lemma. It sends
free simplices to topological simplices, compatibly with the face maps.
-/

universe u

open CategoryTheory Limits Opposite MorphismProperty HomotopicalAlgebra

namespace HomotopyHypothesis.Realization.SemisimplicialComparison

open HomotopyHypothesis.Henry

/-- Composing a cell attachment with an isomorphism gives a cell attachment. -/
theorem CellData.isCellAttachment_comp_iso {X Y Y' : AlgKan.{u}} {j : X ⟶ Y} (d : CellData j)
    (e : Y ≅ Y') : AlgKan.IsCellAttachment (j ≫ e.hom) := by
  refine ⟨d.n, d.a, d.y ≫ e.hom.hom, ?_, fun Z g z hz => ?_⟩
  · rw [← Category.assoc, d.w, Category.assoc]; rfl
  · obtain ⟨g', ⟨h₁, h₂⟩, hu⟩ := d.univ Z g z hz
    refine ⟨e.inv ≫ g', ⟨by rw [Category.assoc, e.hom_inv_id_assoc, h₁], ?_⟩, ?_⟩
    · change d.y ≫ e.hom.hom ≫ e.inv.hom ≫ g'.hom = z
      have he : e.hom.hom ≫ e.inv.hom = 𝟙 _ := congrArg AlgKan.Hom.hom e.hom_inv_id
      rw [← Category.assoc e.hom.hom, he, Category.id_comp]
      exact h₂
    · rintro g'' ⟨h₁', h₂'⟩
      rw [← hu (e.hom ≫ g'') ⟨by rw [← Category.assoc, h₁'], by rw [← h₂']; rfl⟩,
        e.inv_hom_id_assoc]

theorem isFinitelyCellular_of_iso {A B : AlgKan.{u}} (e : A ≅ B) (hA : A.IsFinitelyCellular) :
    B.IsFinitelyCellular := by
  induction hA generalizing B with
  | initial A hA =>
    obtain ⟨hA⟩ := hA
    exact .initial _ ⟨hA.ofIso e⟩
  | attach j hX hj _ => exact .attach _ hX ((AlgKan.IsCellAttachment.data hj).isCellAttachment_comp_iso e)

/-- The standard realization of a cell attachment is a relative finite cell complex. -/
theorem stdR_map_cell {X Y : CDelta.{u}} (j : X ⟶ Y) (hj : AlgKan.IsCellAttachment j.hom) :
    Top.relativeFiniteCellComplexes (stdR.map j) := by
  let d := AlgKan.IsCellAttachment.data hj
  obtain ⟨B, ηB, hB⟩ := exists_free_boundary.{u} d.n
  obtain ⟨D, ηD, hD⟩ := exists_free_simplex.{u} d.n
  obtain ⟨ι, hι, -⟩ := hB D.obj ((SemiSSet.boundary d.n).ι ≫ ηD)
  obtain ⟨abar, habar, -⟩ := hB X.obj d.a
  obtain ⟨ybar, hybar, -⟩ := hD Y.obj d.y
  have sq := d.isPushout hB hD hι habar hybar
  let ιC : B ⟶ D := ObjectProperty.homMk ι
  have sqR := stdR_isPushout (i := ιC) (f := ObjectProperty.homMk abar)
    (k := ObjectProperty.homMk ybar) (j := j) sq
  have hR : Top.relativeFiniteCellComplexes (stdR.map ιC) := by
    have e := stdR_map_freeIso hB hD ιC (SemiSSet.boundary d.n).ι hι
    have : stdR.map ιC = (freeIso hB).hom ≫
        SemiSSet.realization.map (SemiSSet.boundary d.n).ι ≫ (freeIso hD).inv := by
      rw [← Category.assoc, ← e, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [this]
    exact relFinCell_comp (relFinCell_of_isIso _) (relFinCell_comp
      (Packages.realization_boundary_relativeFiniteCellComplex d.n).1 (relFinCell_of_isIso _))
  exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout sqR.flip hR

/-- Cellular maps between finitely cellular objects realize to relative finite cell complexes. -/
theorem stdR_map_cellular {A B : AlgKan.{u}} (i : A ⟶ B) (hi : AlgKan.cellularMaps i)
    (hA : A.IsFinitelyCellular) :
    ∃ hB : B.IsFinitelyCellular, Top.relativeFiniteCellComplexes
      (stdR.map (ObjectProperty.homMk i : (⟨A, hA⟩ : CDelta.{u}) ⟶ ⟨B, hB⟩)) := by
  revert hA
  induction hi with
  | of i hi =>
    intro hA
    rcases hi with hi | hi
    · exact ⟨.attach _ hA hi, stdR_map_cell _ hi⟩
    · have : IsIso i := hi
      refine ⟨isFinitelyCellular_of_iso (asIso i) hA, ?_⟩
      have hI : IsIso (ObjectProperty.homMk i : (⟨_, hA⟩ : CDelta.{u}) ⟶
          ⟨_, isFinitelyCellular_of_iso (asIso i) hA⟩) :=
        ⟨⟨ObjectProperty.homMk (inv i), ObjectProperty.hom_ext _ (by simp),
          ObjectProperty.hom_ext _ (by simp)⟩⟩
      have := Functor.map_isIso stdR (ObjectProperty.homMk i : (⟨_, hA⟩ : CDelta.{u}) ⟶
          ⟨_, isFinitelyCellular_of_iso (asIso i) hA⟩)
      exact relFinCell_of_isIso _
  | id A =>
    intro hA
    refine ⟨hA, ?_⟩
    have : (ObjectProperty.homMk (𝟙 A) : (⟨A, hA⟩ : CDelta.{u}) ⟶ ⟨A, hA⟩) = 𝟙 _ := rfl
    rw [this, CategoryTheory.Functor.map_id]
    exact relFinCell_id _
  | comp_of i₁ i₂ _ h₂ ih =>
    intro hA
    obtain ⟨hB₁, h₁⟩ := ih hA
    rcases h₂ with h₂ | h₂
    · refine ⟨.attach _ hB₁ h₂, ?_⟩
      have : (ObjectProperty.homMk (i₁ ≫ i₂) : (⟨_, hA⟩ : CDelta.{u}) ⟶ ⟨_, .attach _ hB₁ h₂⟩) =
          ObjectProperty.homMk i₁ ≫ (ObjectProperty.homMk i₂ : (⟨_, hB₁⟩ : CDelta.{u}) ⟶ _) := rfl
      rw [this, CategoryTheory.Functor.map_comp]
      exact relFinCell_comp h₁ (stdR_map_cell _ h₂)
    · have : IsIso i₂ := h₂
      let hB := isFinitelyCellular_of_iso (asIso i₂) hB₁
      refine ⟨hB, ?_⟩
      have e : (ObjectProperty.homMk (i₁ ≫ i₂) : (⟨_, hA⟩ : CDelta.{u}) ⟶ ⟨_, hB⟩) =
          ObjectProperty.homMk i₁ ≫ (ObjectProperty.homMk i₂ : (⟨_, hB₁⟩ : CDelta.{u}) ⟶ _) := rfl
      rw [e, CategoryTheory.Functor.map_comp]
      have hI : IsIso (ObjectProperty.homMk i₂ : (⟨_, hB₁⟩ : CDelta.{u}) ⟶ ⟨_, hB⟩) :=
        ⟨⟨ObjectProperty.homMk (inv i₂), ObjectProperty.hom_ext _ (by simp),
          ObjectProperty.hom_ext _ (by simp)⟩⟩
      have := Functor.map_isIso stdR (ObjectProperty.homMk i₂ : (⟨_, hB₁⟩ : CDelta.{u}) ⟶ ⟨_, hB⟩)
      exact relFinCell_comp h₁ (relFinCell_of_isIso _)

theorem stdR_map_cofibration {X Y : CDelta.{u}} (f : X ⟶ Y) (hf : cofibrations CDelta.{u} f) :
    Top.relativeFiniteCellComplexes (stdR.map f) := by
  obtain ⟨_, h⟩ := stdR_map_cellular f.hom hf X.property
  exact h

theorem cellular_from_empty {X : AlgKan.{u}} (hX : X.IsFinitelyCellular) :
    AlgKan.cellularMaps (isInitial_emptyKan.to X) := by
  induction hX with
  | initial X hX =>
    obtain ⟨hX⟩ := hX
    have : IsIso (isInitial_emptyKan.to X) :=
      ⟨hX.to _, isInitial_emptyKan.hom_ext _ _, hX.hom_ext _ _⟩
    exact .of _ (Or.inr (inferInstance : IsIso (isInitial_emptyKan.to X)))
  | attach j _ hj ih =>
    rw [isInitial_emptyKan.hom_ext (isInitial_emptyKan.to _) (isInitial_emptyKan.to _ ≫ j)]
    exact .comp_of _ _ ih (Or.inl hj)

theorem stdR_obj_mem (X : CDelta.{u}) : Top.IsFiniteCellComplex (stdR.obj X) := by
  have h := stdR_map_cofibration (ObjectProperty.homMk (isInitial_emptyKan.to X.obj) :
    emptyC ⟶ X) (cellular_from_empty X.property)
  have hI := stdR_isInitial isInitial_emptyC.{u}
  have : initial.to (stdR.obj X) =
      (initialIsInitial.uniqueUpToIso hI).hom ≫ stdR.map
        (ObjectProperty.homMk (isInitial_emptyKan.to X.obj) : emptyC ⟶ X) :=
    initialIsInitial.hom_ext _ _
  change Top.relativeFiniteCellComplexes (initial.to (stdR.obj X))
  rw [this]
  exact relFinCell_comp (relFinCell_of_isIso _) h

theorem stdR_map_isPushout {A B X P : CDelta.{u}} (i : A ⟶ B) (f : A ⟶ X) (k : B ⟶ P)
    (j : X ⟶ P) (h : IsPushout i f k j) (hi : cofibrations CDelta.{u} i) :
    IsPushout (stdR.map i) (stdR.map f) (stdR.map k) (stdR.map j) :=
  stdR_isPushout (isPushout_alg_of_isPushout h hi)

/-- The class of maps realized to homotopy equivalences. -/
def stdRWeq : MorphismProperty CDelta.{u} := fun _ _ f => Top.homotopyEquivalences (stdR.map f)

theorem stdRWeq_isWeakEquivalenceClass :
    IsWeakEquivalenceClass CDelta.{u} (cofibrations CDelta.{u}) stdRWeq := by
  refine ⟨fun X Y f hf => ?_, ?_, ?_, ?_⟩
  · have : IsIso f := hf
    have := Functor.map_isIso stdR f
    exact hoeq_of_isIso (stdR.map f)
  · exact
      { id_mem := fun X => by
          change Top.homotopyEquivalences (stdR.map (𝟙 X))
          rw [CategoryTheory.Functor.map_id]
          exact hoeq_of_isIso _
        comp_mem := fun f g hf hg => by
          change Top.homotopyEquivalences (stdR.map (f ≫ g))
          rw [CategoryTheory.Functor.map_comp]
          exact hoeq_comp hf hg }
  · intro X Y Z T f g h hfg hgh
    have := hoeq_twoOutOfSix (stdR.map f) (stdR.map g) (stdR.map h)
      (by rw [← CategoryTheory.Functor.map_comp]; exact hfg)
      (by rw [← CategoryTheory.Functor.map_comp]; exact hgh)
    refine ⟨this.1, this.2.1, this.2.2.1, ?_⟩
    change Top.homotopyEquivalences (stdR.map (f ≫ g ≫ h))
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    exact this.2.2.2
  · intro A B X P A' B' X' P' i f k j i' f' k' j' vA vB vX φ sq sq' hi hi' hA hB hX c₁ c₂ c₃ c₄
    exact Packages.homotopyEquivalence_of_isPushout _ _ _ _ _ _ _ _ _ _ _ _
      (stdR_map_isPushout i f k j sq hi) (stdR_map_isPushout i' f' k' j' sq' hi')
      (stdR_map_cofibration i hi) (stdR_map_cofibration i' hi') hA hB hX
      (by rw [← CategoryTheory.Functor.map_comp, c₁, CategoryTheory.Functor.map_comp])
      (by rw [← CategoryTheory.Functor.map_comp, c₂, CategoryTheory.Functor.map_comp])
      (by rw [← CategoryTheory.Functor.map_comp, c₃, CategoryTheory.Functor.map_comp])
      (by rw [← CategoryTheory.Functor.map_comp, c₄, CategoryTheory.Functor.map_comp])

theorem simplexMaps_le_stdRWeq : CDelta.simplexMaps.{u} ≤ stdRWeq := by
  rintro X Y f ⟨m, n, σ, ηX, ηY, hX, hY, -⟩
  have : ContractibleSpace (stdR.obj X) :=
    (TopCat.homeoOfIso (simplexIso hX)).contractibleSpace_iff.mpr inferInstance
  have : ContractibleSpace (stdR.obj Y) :=
    (TopCat.homeoOfIso (simplexIso hY)).contractibleSpace_iff.mpr inferInstance
  exact hoeq_of_contractibleSpace _

theorem stdR_map_weakEquivalence {X Y : CDelta.{u}} (f : X ⟶ Y)
    (hf : weakEquivalences CDelta.{u} f) : Top.homotopyEquivalences (stdR.map f) :=
  (sInf_le (⟨stdRWeq_isWeakEquivalenceClass, simplexMaps_le_stdRWeq⟩ :
    stdRWeq ∈ {W | IsWeakEquivalenceClass CDelta.{u} (cofibrations CDelta.{u}) W ∧
      CDelta.simplexMaps ≤ W}) : _ ≤ stdRWeq) f hf

theorem stdR_isCellularRealization : IsCellularRealization stdR.{u} where
  obj_mem := stdR_obj_mem
  map_cofibration _ _ f hf := stdR_map_cofibration f hf
  map_weakEquivalence _ _ f hf := stdR_map_weakEquivalence f hf
  map_initial _ hI := ⟨stdR_isInitial hI⟩
  map_isPushout _ _ _ _ i f k j h hi := stdR_map_isPushout i f k j h hi

theorem stdR_isStandardRealization : IsStandardRealization stdR.{u} where
  isCellularRealization := stdR_isCellularRealization
  simplex := ⟨fun _ _ _ hX => simplexIso hX,
    fun _ _ _ _ _ _ hY hX σ f hf => stdR_map_simplexIso hY hX σ f hf⟩

/-- **H Def 5.2.5**: a standard realization of `C^Δ` exists. -/
theorem exists_standardRealization_proof :
    ∃ R : CDelta.{u} ⥤ TopCat.{u}, IsStandardRealization R :=
  ⟨stdR, stdR_isStandardRealization⟩

end HomotopyHypothesis.Realization.SemisimplicialComparison
