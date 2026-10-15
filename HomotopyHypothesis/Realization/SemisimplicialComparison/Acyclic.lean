import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.FinCellHomotopicRelIff
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.HomotopyEquivalenceOfIsPushout
import HomotopyHypothesis.Blueprint.Henry.RelativeCells.Part1
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Gluing.HomotopyInvariance.AttachInvariance
import HomotopyHypothesis.Realization.SemisimplicialComparison.CDeltaFacts
import HomotopyHypothesis.Realization.SemisimplicialComparison.CellAttach
import HomotopyHypothesis.Realization.SemisimplicialComparison.Comparison
import HomotopyHypothesis.Realization.SemisimplicialComparison.DiskSimplex
import HomotopyHypothesis.Realization.SemisimplicialComparison.FullyFaithful
import HomotopyHypothesis.Realization.SemisimplicialComparison.Standard
import HomotopyHypothesis.Realization.SemisimplicialComparison.TopFacts
/-!
# Standard realizations are acyclic (H Thm 5.2.10)

Homotopy surjectivity by induction on the cells of a finite cell complex `Y`: if `Y ≃ R X` and
`Y⁺ = Y ⊔_{∂𝔻 n} 𝔻 n`, identify `(𝔻 n, ∂𝔻 n)` with the realization of the free cell
`(F Δ_n, F ∂Δ_n)`, replace the attaching map `∂𝔻 n ⟶ R X` up to homotopy by the realization of a
map `F ∂Δ_n ⟶ X` (homotopy full faithfulness), and attach the corresponding cell to `X`; the gluing
lemma and the homotopy invariance of attaching maps conclude.
-/

universe u

open CategoryTheory Limits Opposite MorphismProperty HomotopicalAlgebra

namespace HomotopyHypothesis.Realization.SemisimplicialComparison

open HomotopyHypothesis.Henry

section

variable {R : CDelta.{u} ⥤ TopCat.{u}} (hR : IsStandardRealization R)

include hR in
/-- The realization of the free cell `F ∂Δ_n ⟶ F Δ_n` is the disk boundary inclusion. -/
theorem exists_disk_cell (n : ℕ) :
    ∃ (B D : CDelta.{u}) (ηB : (SemiSSet.boundary.{u} n).toFunctor ⟶ B.obj.X)
      (ηD : SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶ D.obj.X)
      (_ : B.obj.IsFreeOn ηB) (_ : D.obj.IsFreeOn ηD) (ι : B ⟶ D)
      (_ : ηB ≫ ι.hom.hom = (SemiSSet.boundary n).ι ≫ ηD),
      Nonempty (CategoryTheory.Arrow.mk (TopCat.diskBoundaryInclusion.{u} n) ≅ CategoryTheory.Arrow.mk (R.map ι)) := by
  obtain ⟨B, ηB, hB⟩ := exists_free_boundary.{u} n
  obtain ⟨D, ηD, hD⟩ := exists_free_simplex.{u} n
  obtain ⟨ι, hι, -⟩ := hB D.obj ((SemiSSet.boundary n).ι ≫ ηD)
  let ιC : B ⟶ D := ObjectProperty.homMk ι
  have := isIso_phi_subfunctor hR n (SemiSSet.boundary n) B ηB hB
  have := isIso_phi_simplex hR hD
  let e : CategoryTheory.Arrow.mk (SemiSSet.realization.{u}.map (SemiSSet.boundary.{u} n).ι) ≅
      CategoryTheory.Arrow.mk (R.map ιC) :=
    Arrow.isoMk (asIso (SemiSSet.realization.map ηB ≫ phiA hR B))
      (asIso (SemiSSet.realization.map ηD ≫ phiA hR D))
      (phi_comm hR ηB ηD _ ιC hι).symm
  exact ⟨B, D, ηB, ηD, hB, hD, ιC, hι, ⟨(nonempty_diskArrowIso n).some.symm ≪≫ e⟩⟩

include hR in
/-- One cell of homotopy surjectivity. -/
theorem surj_step {Y₀ Y₁ : TopCat.{u}} (n : ℕ) (a : TopCat.diskBoundary.{u} n ⟶ Y₀)
    (f : Y₀ ⟶ Y₁) (b : TopCat.disk.{u} n ⟶ Y₁)
    (sq : IsPushout a (TopCat.diskBoundaryInclusion n) f b) (X : CDelta.{u}) (w : Y₀ ⟶ R.obj X)
    (hw : Top.homotopyEquivalences w) :
    ∃ (X' : CDelta.{u}) (w' : Y₁ ⟶ R.obj X'), Top.homotopyEquivalences w' := by
  obtain ⟨B, D, ηB, ηD, hB, hD, ι, hι, ⟨e⟩⟩ := exists_disk_cell hR n
  let eA := Comma.leftIso e
  let eB := Comma.rightIso e
  have ew : TopCat.diskBoundaryInclusion n ≫ eB.hom = eA.hom ≫ R.map ι := (e.hom.w).symm
  obtain ⟨v, hvdef⟩ : ∃ v : R.obj B ⟶ R.obj X, v = eA.inv ≫ a ≫ w := ⟨_, rfl⟩
  -- the attaching map up to homotopy
  let F := hR.isCellularRealization.toFinCell
  have hcofB : cofibrations CDelta.{u} (isInitial_emptyC.to B) := by
    have h := cellular_from_empty B.property
    have e' : isInitial_emptyC.to B = ObjectProperty.homMk (isInitial_emptyKan.to B.obj) :=
      isInitial_emptyC.hom_ext _ _
    rw [e']
    exact h
  have hI := Classical.choice (hR.isCellularRealization.map_initial isInitial_emptyC.{u})
  obtain ⟨a', -, cylH⟩ := standardRealization_isHomotopyFullyFaithful_proof hR
    (isInitial_emptyC.to B) hcofB (isInitial_emptyC.to X) (ObjectProperty.homMk v)
    (ObjectProperty.hom_ext _ (hI.hom_ext _ _))
  obtain ⟨cyl, H, h₀, h₁⟩ := cylH
  have hrel := (Packages.finCell_homotopicRel_iff (F.map (isInitial_emptyC.to B))
    (hR.isCellularRealization.map_cofibration _ hcofB) (R.map a') v).2
      ⟨cyl, H.hom, congrArg (fun t => t.hom) h₀, congrArg (fun t => t.hom) h₁⟩
  -- the cell attached to `X`
  let d := attachData X.obj n (ηB ≫ a'.hom.hom)
  let X' : CDelta.{u} := ⟨attach X.obj n (ηB ≫ a'.hom.hom),
    .attach _ X.property (attach_isCellAttachment _ _ _)⟩
  obtain ⟨ybar, hybar, -⟩ := hD X'.obj d.y
  have sqA := d.isPushout hB hD hι (abar := a'.hom) rfl hybar
  let ybarC : D ⟶ X' := ObjectProperty.homMk ybar
  let jC : X ⟶ X' := ObjectProperty.homMk (attachJ X.obj n (ηB ≫ a'.hom.hom))
  have sqC : IsPushout ι a' ybarC jC := isPushout_of_alg sqA
  have hcofι : cofibrations CDelta.{u} ι := cofibration_of_isFreeOn_boundary hB hD ι hι
  have sqR := hR.isCellularRealization.map_isPushout ι a' ybarC jC sqC hcofι
  have hRι := hR.isCellularRealization.map_cofibration ι hcofι
  -- compare `Y₁` with the pushout along `v`
  have sqP := IsPushout.of_hasPushout (R.map ι) v
  have hcell : Top.relativeFiniteCellComplexes (TopCat.diskBoundaryInclusion.{u} n) :=
    MorphismProperty.multiplicativeClosure.of _ (Or.inl (MorphismProperty.pushouts_mk _
      (IsPushout.of_horiz_isIso ⟨by simp⟩ : IsPushout (𝟙 _) (TopCat.diskBoundaryInclusion.{u} n)
        (TopCat.diskBoundaryInclusion.{u} n) (𝟙 _)) (MorphismProperty.ofHoms.mk n)))
  have hc₂ : a ≫ w = eA.hom ≫ v := by rw [hvdef, Iso.hom_inv_id_assoc]
  let φ : Y₁ ⟶ pushout (R.map ι) v := sq.flip.desc (eB.hom ≫ pushout.inl _ _)
    (w ≫ pushout.inr _ _) (by
      rw [← Category.assoc, ew, Category.assoc, pushout.condition, ← Category.assoc,
        ← Category.assoc, hc₂])
  have hφ : Top.homotopyEquivalences φ :=
    Packages.homotopyEquivalence_of_isPushout _ _ _ _ _ _ _ _ eA.hom eB.hom w φ sq.flip sqP
      hcell hRι (hoeq_of_isIso _) (hoeq_of_isIso _) hw ew hc₂ (sq.flip.inl_desc _ _ _)
      (sq.flip.inr_desc _ _ _)
  obtain ⟨ψ, hψ⟩ := Gluing.HomotopyInvariance.exists_homotopyEquivalence_of_isPushout_homotopic_proof hRι
    (g₀ := v) (g₁ := R.map a') hrel.homotopic.symm sqP sqR
  exact ⟨X', φ ≫ ψ, hoeq_comp hφ hψ⟩

include hR in
theorem surj_of_relFinCell {Y₀ Y₁ : TopCat.{u}} (f : Y₀ ⟶ Y₁)
    (hf : Top.relativeFiniteCellComplexes f) :
    (∃ (X : CDelta.{u}) (w : Y₀ ⟶ R.obj X), Top.homotopyEquivalences w) →
      ∃ (X : CDelta.{u}) (w : Y₁ ⟶ R.obj X), Top.homotopyEquivalences w := by
  have gen : ∀ {Y₀ Y₁ : TopCat.{u}} (f : Y₀ ⟶ Y₁),
      (Top.cellBoundaries.pushouts ⊔ MorphismProperty.isomorphisms TopCat.{u}) f →
      (∃ (X : CDelta.{u}) (w : Y₀ ⟶ R.obj X), Top.homotopyEquivalences w) →
        ∃ (X : CDelta.{u}) (w : Y₁ ⟶ R.obj X), Top.homotopyEquivalences w := by
    rintro Y₀ Y₁ f hf ⟨X₀, w, hw⟩
    rcases hf with ⟨A, B, p, a, b, ⟨n⟩, sq⟩ | hf
    · exact surj_step hR n a f b sq X₀ w hw
    · have : IsIso f := hf
      exact ⟨X₀, inv f ≫ w, hoeq_comp (hoeq_of_isIso _) hw⟩
  induction hf with
  | of f hf => exact gen f hf
  | id => exact id
  | comp_of f g _ hg ih => exact fun h => gen g hg (ih h)

end

/-- **H Thm 5.2.10**: a standard realization is acyclic. -/
theorem standardRealization_isAcyclic_proof {R : CDelta.{u} ⥤ TopCat.{u}}
    (hR : IsStandardRealization R) : IsAcyclic hR.isCellularRealization.toFinCell := by
  refine ⟨fun Y => ?_, standardRealization_isHomotopyFullyFaithful_proof hR⟩
  have hI := Classical.choice (hR.isCellularRealization.map_initial isInitial_emptyC.{u})
  have : IsIso (initialIsInitial.to (R.obj emptyC)) :=
    ⟨⟨hI.to _, initialIsInitial.hom_ext _ _, hI.hom_ext _ _⟩⟩
  obtain ⟨X, w, hw⟩ := surj_of_relFinCell hR _ Y.property
    ⟨emptyC, initialIsInitial.to _, hoeq_of_isIso _⟩
  exact ⟨X, ObjectProperty.homMk w, hw⟩

end HomotopyHypothesis.Realization.SemisimplicialComparison
