import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.FinCellHomotopicRelIff
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.RelativeFiniteCellComplexHomotopyExtension
import HomotopyHypothesis.Blueprint.Henry.RelativeCells.Part1
import HomotopyHypothesis.Blueprint.Henry.RelativeCells.Part2
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Gluing.RelativeHomotopy.GlueHomotopy
import HomotopyHypothesis.Realization.SemisimplicialComparison.CDeltaFacts
import HomotopyHypothesis.Realization.SemisimplicialComparison.CellAttach
import HomotopyHypothesis.Realization.SemisimplicialComparison.Comparison
import HomotopyHypothesis.Realization.SemisimplicialComparison.Standard
/-!
# Standard realizations are homotopy fully faithful (H Prop 5.2.8)

Induction over the cells of a cofibration of `C^Δ`: a single cell is lifted by H Lemma 5.2.7
(`standardRealization_relative_cells`) and the homotopy relative to the boundary of the cell glues
over the realized pushout; a composite is handled with the homotopy extension property of relative
finite cell complexes.
-/

universe u

open CategoryTheory Limits Opposite MorphismProperty HomotopicalAlgebra

namespace HomotopyHypothesis.Realization.SemisimplicialComparison

open HomotopyHypothesis.Henry

/-- Shrinking the fixed set of a relative homotopy. -/
theorem homotopicRel_mono' {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f₀ f₁ : C(X, Y)} {S S' : Set X} (h : f₀.HomotopicRel f₁ S) (hS : S' ⊆ S) :
    f₀.HomotopicRel f₁ S' :=
  h.map fun F => ⟨F.toHomotopy, fun t x hx => F.prop' t x (hS hx)⟩

section

variable {R : CDelta.{u} ⥤ TopCat.{u}} (hR : IsStandardRealization R)

omit hR in

/-- The relative lifting property of a map of `C^Δ` against `R` (H Prop 5.2.8 for one map). -/
def RelLift (R : CDelta.{u} ⥤ TopCat.{u}) {A B : CDelta.{u}} (i : A ⟶ B) : Prop :=
  ∀ (X : CDelta.{u}) (x : A ⟶ X) (v : R.obj B ⟶ R.obj X), R.map i ≫ v = R.map x →
    ∃ v' : B ⟶ X, i ≫ v' = x ∧
      (R.map v').hom.HomotopicRel v.hom (Set.range (R.map i).hom)

theorem relLift_of_isIso {A B : CDelta.{u}} (i : A ⟶ B) [IsIso i] : RelLift R i := by
  intro X x v hv
  refine ⟨inv i ≫ x, by simp, ?_⟩
  have : R.map (inv i ≫ x) = v := by
    rw [CategoryTheory.Functor.map_comp, ← hv, CategoryTheory.Functor.map_inv,
      IsIso.inv_hom_id_assoc]
  rw [this]
  exact ContinuousMap.HomotopicRel.refl _

include hR in
theorem relLift_cell {X₀ Y₀ : CDelta.{u}} (j : X₀ ⟶ Y₀) (hj : AlgKan.IsCellAttachment j.hom) :
    RelLift R j := by
  intro X x v hv
  let d := AlgKan.IsCellAttachment.data hj
  obtain ⟨B, ηB, hB⟩ := exists_free_boundary.{u} d.n
  obtain ⟨D, ηD, hD⟩ := exists_free_simplex.{u} d.n
  obtain ⟨ι, hι, -⟩ := hB D.obj ((SemiSSet.boundary d.n).ι ≫ ηD)
  obtain ⟨abar, habar, -⟩ := hB X₀.obj d.a
  obtain ⟨ybar, hybar, -⟩ := hD Y₀.obj d.y
  have sq := d.isPushout hB hD hι habar hybar
  let ιC : B ⟶ D := ObjectProperty.homMk ι
  let abarC : B ⟶ X₀ := ObjectProperty.homMk abar
  let ybarC : D ⟶ Y₀ := ObjectProperty.homMk ybar
  have sqC : IsPushout ιC abarC ybarC j := isPushout_of_alg sq
  have hcof : cofibrations CDelta.{u} ιC := cofibration_of_isFreeOn_boundary hB hD ιC hι
  have sqR := hR.isCellularRealization.map_isPushout ιC abarC ybarC j sqC hcof
  let F := hR.isCellularRealization.toFinCell
  let f : F.obj D ⟶ F.obj X := F.map ybarC ≫ (ObjectProperty.homMk v : F.obj Y₀ ⟶ F.obj X)
  have hf : F.map ιC ≫ f = F.map (abarC ≫ x) := by
    ext1
    change R.map ιC ≫ R.map ybarC ≫ v = R.map (abarC ≫ x)
    rw [← Category.assoc, sqR.w, Category.assoc, hv, CategoryTheory.Functor.map_comp]
  obtain ⟨x', hx', cyl, H, h₀, h₁⟩ :=
    Packages.standardRealization_relative_cells hR d.n ηB ηD hB hD ιC hι (abarC ≫ x) f hf
  have hFcof : cofibrations FinCell.{u} (F.map ιC) :=
    hR.isCellularRealization.map_cofibration ιC hcof
  have hx'R : (R.map x').hom.HomotopicRel (R.map ybarC ≫ v).hom (Set.range (R.map ιC).hom) :=
    (Packages.finCell_homotopicRel_iff (F.map ιC) hFcof (R.map x') (R.map ybarC ≫ v)).2
      ⟨cyl, H.hom, congrArg (fun t => t.hom) h₀, congrArg (fun t => t.hom) h₁⟩
  have hz : (SemiSSet.boundary d.n).ι ≫ ηD ≫ x'.hom.hom = d.a ≫ x.hom.hom := by
    rw [← Category.assoc, ← hι, Category.assoc]
    have e := congrArg (fun t => t.hom.hom) hx'
    change ι.hom ≫ x'.hom.hom = abar.hom ≫ x.hom.hom at e
    rw [e, ← Category.assoc, habar]
  obtain ⟨v'', ⟨hv₁, hv₂⟩, -⟩ := d.univ X.obj x.hom (ηD ≫ x'.hom.hom) hz
  let v' : Y₀ ⟶ X := ObjectProperty.homMk v''
  have hjv : j ≫ v' = x := ObjectProperty.hom_ext _ hv₁
  have hyv : ybarC ≫ v' = x' := ObjectProperty.hom_ext _ (isFreeOn_hom_ext hD (by
    change ηD ≫ ybar.hom ≫ v''.hom = _
    rw [← Category.assoc, hybar, hv₂]))
  refine ⟨v', hjv, Gluing.RelativeHomotopy.homotopicRel_of_isPushout_proof sqR ?_ ?_⟩
  · rw [← CategoryTheory.Functor.map_comp, hjv, hv]
  · rw [← CategoryTheory.Functor.map_comp, hyv]
    exact hx'R

theorem relLift_comp {A B₁ B : CDelta.{u}} {i₁ : A ⟶ B₁} {i₂ : B₁ ⟶ B} (h₁ : RelLift R i₁)
    (h₂ : RelLift R i₂) (hc : Top.relativeFiniteCellComplexes (R.map i₂)) :
    RelLift R (i₁ ≫ i₂) := by
  intro X x v hv
  rw [CategoryTheory.Functor.map_comp, Category.assoc] at hv
  obtain ⟨v₁, hv₁, ⟨K⟩⟩ := h₁ X x (R.map i₂ ≫ v) hv
  obtain ⟨w, H', hH'⟩ := Packages.relativeFiniteCellComplex_homotopyExtension (R.map i₂) hc v.hom
    (R.map v₁).hom K.symm.toHomotopy
  let wT : R.obj B ⟶ R.obj X := TopCat.ofHom w
  have hw : R.map i₂ ≫ wT = R.map v₁ := by
    ext a
    have e := hH' 1 a
    rw [ContinuousMap.Homotopy.apply_one, ContinuousMap.Homotopy.apply_one] at e
    exact e
  obtain ⟨v', hv', hL⟩ := h₂ X v₁ wT hw
  refine ⟨v', by rw [Category.assoc, hv', hv₁], ?_⟩
  have hS : Set.range (R.map (i₁ ≫ i₂)).hom ⊆ Set.range (R.map i₂).hom := by
    rintro _ ⟨a, rfl⟩
    exact ⟨(R.map i₁).hom a, by rw [CategoryTheory.Functor.map_comp]; rfl⟩
  have hH : v.hom.HomotopicRel w (Set.range (R.map (i₁ ≫ i₂)).hom) := by
    refine ⟨⟨H', fun t p hp => ?_⟩⟩
    obtain ⟨a, rfl⟩ := hp
    have e₁ : (R.map (i₁ ≫ i₂)).hom a = (R.map i₂).hom ((R.map i₁).hom a) := by
      rw [CategoryTheory.Functor.map_comp]; rfl
    change H' (t, (R.map (i₁ ≫ i₂)).hom a) = v.hom ((R.map (i₁ ≫ i₂)).hom a)
    rw [e₁, hH']
    change K.toHomotopy.symm (t, _) = _
    rw [ContinuousMap.Homotopy.symm_apply]
    erw [K.eq_fst _ ⟨a, rfl⟩]
    have e₂ := congrArg (fun t => t.hom a) hv
    have e₃ := congrArg (fun t => (R.map t).hom a) hv₁
    simp only [TopCat.hom_comp, ContinuousMap.comp_apply, CategoryTheory.Functor.map_comp]
      at e₂ e₃
    rw [e₃, ← e₂]
  exact (homotopicRel_mono' hL hS).trans hH.symm

include hR in
theorem relLift_generator {A B : CDelta.{u}} (i : A ⟶ B)
    (hi : AlgKan.IsCellAttachment i.hom ∨ MorphismProperty.isomorphisms AlgKan.{u} i.hom) :
    RelLift R i ∧ Top.relativeFiniteCellComplexes (R.map i) := by
  have hcof : cofibrations CDelta.{u} i := MorphismProperty.multiplicativeClosure.of _ hi
  refine ⟨?_, hR.isCellularRealization.map_cofibration i hcof⟩
  rcases hi with hi | hi
  · exact relLift_cell hR i hi
  · have : IsIso i.hom := hi
    have : IsIso i := ⟨⟨ObjectProperty.homMk (inv i.hom), ObjectProperty.hom_ext _ (by simp),
      ObjectProperty.hom_ext _ (by simp)⟩⟩
    exact relLift_of_isIso i

include hR in
theorem relLift_cellular {A B : AlgKan.{u}} (i : A ⟶ B) (hi : AlgKan.cellularMaps i)
    (hA : A.IsFinitelyCellular) :
    ∃ hB : B.IsFinitelyCellular,
      RelLift R (ObjectProperty.homMk i : (⟨A, hA⟩ : CDelta.{u}) ⟶ ⟨B, hB⟩) := by
  revert hA
  induction hi with
  | of i hi =>
    intro hA
    rcases hi with hi | hi
    · exact ⟨.attach _ hA hi, (relLift_generator hR _ (Or.inl hi)).1⟩
    · have : IsIso i := hi
      exact ⟨isFinitelyCellular_of_iso (asIso i) hA, (relLift_generator hR _ (Or.inr hi)).1⟩
  | id A =>
    intro hA
    exact ⟨hA, relLift_of_isIso (R := R) (𝟙 (⟨A, hA⟩ : CDelta.{u}))⟩
  | comp_of i₁ i₂ _ h₂ ih =>
    intro hA
    obtain ⟨hB₁, h₁⟩ := ih hA
    rcases h₂ with h₂ | h₂
    · obtain ⟨g₁, g₂⟩ := relLift_generator hR
        (ObjectProperty.homMk i₂ : (⟨_, hB₁⟩ : CDelta.{u}) ⟶ ⟨_, .attach _ hB₁ h₂⟩) (Or.inl h₂)
      exact ⟨_, relLift_comp h₁ g₁ g₂⟩
    · have : IsIso i₂ := h₂
      obtain ⟨g₁, g₂⟩ := relLift_generator hR
        (ObjectProperty.homMk i₂ : (⟨_, hB₁⟩ : CDelta.{u}) ⟶
          ⟨_, isFinitelyCellular_of_iso (asIso i₂) hB₁⟩) (Or.inr h₂)
      exact ⟨_, relLift_comp h₁ g₁ g₂⟩

end

/-- **H Prop 5.2.8**: a standard realization is homotopy fully faithful. -/
theorem standardRealization_isHomotopyFullyFaithful_proof {R : CDelta.{u} ⥤ TopCat.{u}}
    (hR : IsStandardRealization R) :
    IsHomotopyFullyFaithful hR.isCellularRealization.toFinCell := by
  intro A B X i hi x v hv
  obtain ⟨_, hL⟩ := relLift_cellular hR i.hom hi A.property
  obtain ⟨v', hv', hH⟩ := hL X x v.hom (congrArg (fun t => t.hom) hv)
  refine ⟨v', hv', ?_⟩
  obtain ⟨cyl, h, h₀, h₁⟩ := (Packages.finCell_homotopicRel_iff
    (hR.isCellularRealization.toFinCell.map i) (hR.isCellularRealization.map_cofibration i hi)
    (R.map v') v.hom).1 hH
  exact ⟨cyl, ObjectProperty.homMk h, by ext1; simpa using h₀, by ext1; simpa using h₁⟩

end HomotopyHypothesis.Realization.SemisimplicialComparison
