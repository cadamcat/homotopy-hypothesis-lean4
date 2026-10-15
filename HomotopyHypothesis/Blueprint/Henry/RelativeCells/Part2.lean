import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.KanSimplices.Part1
import HomotopyHypothesis.Blueprint.Henry.KanSimplices.Part2
import HomotopyHypothesis.Blueprint.Henry.Packages.Simplicial.StandardRealizationComparison
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.FinCellHomotopicRelIff
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.RelativeLiftOfHomotopyEquivalence
import HomotopyHypothesis.Blueprint.Henry.RelativeCells.Part1
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Blueprint.Henry.Topology

/-!
# `HomotopyHypothesis.Blueprint.Henry.RelativeCells`, part 2

Lines 36–136 of `HomotopyHypothesis.Blueprint.Henry.RelativeCells`, split so that the modules of the development form an acyclic import graph.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopyHypothesis.Henry

/-- **H Lemma 5.2.7** (H:2914–2936): for a standard realization `R`, a cell boundary `a : ∂Δ_n ⟶ X`
in `C^Δ` (on free objects) and a filler `f : R(Δ_n) ⟶ R X` of `R a`, there is a cell `x` with
boundary `a` whose realization is homotopic to `f` relative to the boundary. Proved from
`standardRealization_comparison` (H Lemma 5.2.6), `relativeLift_of_homotopyEquivalence`,
`isKan_exists_simplex_homotopicRel` (Rourke–Sanderson, Thm. 5.3) and
`finCell_homotopicRel_iff`. -/
theorem Packages.standardRealization_relative_cells {R : CDelta.{u} ⥤ TopCat.{u}}
    (hR : IsStandardRealization R) (n : ℕ) {B D X : CDelta.{u}}
    (ηB : (SemiSSet.boundary.{u} n).toFunctor ⟶ B.obj.X)
    (ηD : SemiSSet.stdSimplex.obj (SemiSimplexCategory.mk n) ⟶ D.obj.X)
    (hB : B.obj.IsFreeOn ηB) (hD : D.obj.IsFreeOn ηD) (ι : B ⟶ D)
    (hι : ηB ≫ ι.hom.hom = (SemiSSet.boundary n).ι ≫ ηD) (a : B ⟶ X)
    (f : hR.isCellularRealization.toFinCell.obj D ⟶ hR.isCellularRealization.toFinCell.obj X)
    (hf : hR.isCellularRealization.toFinCell.map ι ≫ f = hR.isCellularRealization.toFinCell.map a) :
    ∃ x : D ⟶ X, ι ≫ x = a ∧
      RelHomotopic (hR.isCellularRealization.toFinCell.map ι)
        (hR.isCellularRealization.toFinCell.map x) f := by
  obtain ⟨φ, hφ, hbd, hsx⟩ := Packages.standardRealization_comparison hR
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ∀ Y : CDelta.{u}, SemiSSet.realization.obj Y.obj.X ⟶ R.obj Y,
      ∀ Y, ψ Y = φ.app Y := ⟨fun Y => φ.app Y, fun _ => rfl⟩
  have nat : ∀ {Y Z : CDelta.{u}} (y : Y ⟶ Z),
      SemiSSet.realization.map y.hom.hom ≫ ψ Z = ψ Y ≫ R.map y := by
    intro Y Z y
    rw [hψ, hψ]
    exact φ.naturality y
  have hψX : Top.homotopyEquivalences (ψ X) := by
    rw [hψ]
    exact hφ X
  have : IsIso (SemiSSet.realization.map ηB ≫ ψ B) := by
    rw [hψ]
    exact hbd n B ηB hB
  have : IsIso (SemiSSet.realization.map ηD ≫ ψ D) := by
    rw [hψ]
    exact hsx n D ηD hD
  let eB := asIso (SemiSSet.realization.map ηB ≫ ψ B)
  let eD := asIso (SemiSSet.realization.map ηD ≫ ψ D)
  have hfR : R.map ι ≫ f.hom = R.map a := congrArg (fun k => k.hom) hf
  have hcof : cofibrations CDelta.{u} ι := cofibration_of_isFreeOn_boundary hB hD ι hι
  have hRι : Top.relativeFiniteCellComplexes (R.map ι) :=
    hR.isCellularRealization.map_cofibration ι hcof
  -- the realized boundary inclusion and `R ι` correspond under `eB` and `eD`
  have hbdD : SemiSSet.realization.map (SemiSSet.boundary n).ι ≫ eD.hom = eB.hom ≫ R.map ι := by
    simp only [eD, eB, asIso_hom]
    rw [← Category.assoc, ← Functor.map_comp, ← hι, Functor.map_comp, Category.assoc, nat ι]
    simp only [Category.assoc]
  have e1 : SemiSSet.realization.map (ηB ≫ a.hom.hom) ≫ ψ X = eB.hom ≫ R.map a := by
    rw [Functor.map_comp, Category.assoc, nat a]
    simp [eB]
  -- transport the filler to the realization of the underlying semi-simplicial set
  let a' : R.obj B ⟶ SemiSSet.realization.obj X.obj.X :=
    eB.inv ≫ SemiSSet.realization.map (ηB ≫ a.hom.hom)
  have ha' : a' ≫ ψ X = R.map ι ≫ f.hom := by
    simp only [a', Category.assoc, e1, Iso.inv_hom_id_assoc, hfR]
  obtain ⟨l, hl, hlφ⟩ :=
    (Packages.relativeLift_of_homotopyEquivalence (R.map ι) hRι (ψ X) hψX).1 a' f.hom ha'
  let l₁ := eD.hom ≫ l
  have hl₁ : SemiSSet.realization.map (SemiSSet.boundary n).ι ≫ l₁ =
      SemiSSet.realization.map (ηB ≫ a.hom.hom) := by
    simp only [l₁]
    rw [← Category.assoc, hbdD, Category.assoc, hl]
    simp [a']
  -- a simplex with the prescribed boundary
  have hKan : X.obj.X.IsKan := fun m k h => ⟨X.obj.fill m k h, X.obj.fill_spec m k h⟩
  obtain ⟨σ, hσ, hσl⟩ :=
    Packages.isKan_exists_simplex_homotopicRel X.obj.X hKan n (ηB ≫ a.hom.hom) l₁ hl₁
  obtain ⟨g, hg, -⟩ := hD X.obj σ
  let x : D ⟶ X := ObjectProperty.homMk g
  have hx : ι ≫ x = a := by
    ext1
    refine (hB X.obj (ηB ≫ a.hom.hom)).unique ?_ rfl
    change ηB ≫ ι.hom.hom ≫ g.hom = ηB ≫ a.hom.hom
    rw [← Category.assoc, hι, Category.assoc, hg, hσ]
  refine ⟨x, hx, ?_⟩
  have e2 : eD.hom ≫ R.map x = SemiSSet.realization.map σ ≫ ψ X := by
    simp only [eD, asIso_hom, Category.assoc]
    rw [← nat x, ← Category.assoc, ← Functor.map_comp]
    exact congrArg (fun k => SemiSSet.realization.map k ≫ ψ X) hg
  -- homotopies relative to the realized boundary
  set S := Set.range (SemiSSet.realization.map (SemiSSet.boundary.{u} n).ι).hom
  have hS : ∀ s ∈ S, eD.hom.hom s ∈ Set.range (R.map ι).hom := by
    rintro _ ⟨t, rfl⟩
    exact ⟨eB.hom.hom t, (congrArg (fun k => k.hom t) hbdD).symm⟩
  have h₁ : (eD.hom ≫ R.map x).hom.HomotopicRel (eD.hom ≫ f.hom).hom S := by
    rw [e2]
    have hA := hσl.comp_continuousMap (ψ X).hom
    have hB' := homotopicRel_comp_right hlφ eD.hom.hom hS
    exact hA.trans hB'
  have hS' : ∀ p ∈ Set.range (R.map ι).hom, eD.inv.hom p ∈ S := by
    rintro _ ⟨q, rfl⟩
    refine ⟨eB.inv.hom q, ?_⟩
    have := congrArg (fun k => (eB.inv ≫ k ≫ eD.inv).hom q) hbdD
    simpa using this
  have key : (R.map x).hom.HomotopicRel f.hom.hom (Set.range (R.map ι).hom) := by
    have hid : (eD.hom.hom).comp (eD.inv.hom) = ContinuousMap.id _ := by
      rw [← TopCat.hom_comp, Iso.inv_hom_id, TopCat.hom_id]
    have := homotopicRel_comp_right h₁ eD.inv.hom hS'
    simpa [hid] using this
  obtain ⟨cyl, h, h₀, h₁'⟩ := (Packages.finCell_homotopicRel_iff
    (hR.isCellularRealization.toFinCell.map ι) hRι (R.map x) f.hom).1 key
  exact ⟨cyl, ObjectProperty.homMk h, by ext1; simpa using h₀, by ext1; simpa using h₁'⟩
