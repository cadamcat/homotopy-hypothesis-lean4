import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.DiskBoundaryIsFiniteCellComplex
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Realization.Boundary.RealizationBoundary
/-!
# The realized boundary of a semi-simplicial simplex is a finite cell complex

The barycentric-coordinate model identifies the realized simplex pair with the standard disk pair.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra TopCat
open HomotopyHypothesis.Henry

namespace HomotopyHypothesis.Realization.Boundary

theorem realization_boundary_relativeFiniteCellComplex_proof (n : ℕ) :
    Top.relativeFiniteCellComplexes
        (SemiSSet.realization.{u}.map (SemiSSet.boundary.{u} n).ι) ∧
      Top.IsFiniteCellComplex
        (SemiSSet.realization.{u}.obj (SemiSSet.boundary.{u} n).toFunctor) := by
  let f := SemiSSet.realization.{u}.map (SemiSSet.boundary.{u} n).ι
  let eA := TopCat.isoOfHomeo (realizationBoundaryToDiskBoundaryHomeomorph n)
  let eB := realizationSimplexToDiskIso n
  let db := TopCat.diskBoundaryInclusion.{u} n
  have hSquare : f ≫ eB.hom = eA.hom ≫ db := by
    simpa [f, eA, eB, db] using realizationBoundaryToDiskBoundary_square n
  let P : MorphismProperty TopCat.{u} :=
    (Top.cellBoundaries.pushouts ⊔ MorphismProperty.isomorphisms TopCat.{u})
  have hDiskBoundary : P db := by
    apply Or.inl
    apply MorphismProperty.le_pushouts
    exact MorphismProperty.ofHoms.mk n
  have hIsoA : P eA.hom := by
    apply Or.inr
    infer_instance
  have hIsoBInv : P eB.inv := by
    apply Or.inr
    infer_instance
  have hfEq : f = eA.hom ≫ db ≫ eB.inv := by
    calc
      f = f ≫ (eB.hom ≫ eB.inv) := by simp
      _ = (f ≫ eB.hom) ≫ eB.inv := by simp [Category.assoc]
      _ = (eA.hom ≫ db) ≫ eB.inv := by rw [hSquare]
      _ = eA.hom ≫ db ≫ eB.inv := by simp [Category.assoc]
  have hRelative : P.multiplicativeClosure f := by
    rw [hfEq]
    exact MorphismProperty.multiplicativeClosure.comp_of (eA.hom ≫ db) eB.inv
      (MorphismProperty.multiplicativeClosure.comp_of eA.hom db
        (MorphismProperty.le_multiplicativeClosure P eA.hom hIsoA) hDiskBoundary)
      hIsoBInv
  have hDiskBoundaryFinite :=
    HomotopyHypothesis.Henry.Packages.diskBoundary_isFiniteCellComplex.{u} n
  change P.multiplicativeClosure (initial.to (TopCat.diskBoundary.{u} n)) at hDiskBoundaryFinite
  have hInitialSquare :
      initial.to (SemiSSet.realization.{u}.obj (SemiSSet.boundary.{u} n).toFunctor) ≫ eA.hom =
        initial.to (TopCat.diskBoundary.{u} n) := by
    apply initial.hom_ext
  have hInitialEq :
      initial.to (SemiSSet.realization.{u}.obj (SemiSSet.boundary.{u} n).toFunctor) =
        initial.to (TopCat.diskBoundary.{u} n) ≫ eA.inv := by
    calc
      initial.to (SemiSSet.realization.{u}.obj (SemiSSet.boundary.{u} n).toFunctor) =
          initial.to (SemiSSet.realization.{u}.obj (SemiSSet.boundary.{u} n).toFunctor) ≫
            (eA.hom ≫ eA.inv) := by simp
      _ = (initial.to (SemiSSet.realization.{u}.obj (SemiSSet.boundary.{u} n).toFunctor) ≫
          eA.hom) ≫ eA.inv := by simp [Category.assoc]
      _ = initial.to (TopCat.diskBoundary.{u} n) ≫ eA.inv := by rw [hInitialSquare]
  have hIsoAInv : P eA.inv := by
    apply Or.inr
    infer_instance
  have hFiniteBoundary :
      P.multiplicativeClosure
        (initial.to (SemiSSet.realization.{u}.obj (SemiSSet.boundary.{u} n).toFunctor)) := by
    rw [hInitialEq]
    exact MorphismProperty.multiplicativeClosure.comp_of _ _ hDiskBoundaryFinite hIsoAInv
  exact ⟨hRelative, hFiniteBoundary⟩

#print axioms realization_boundary_relativeFiniteCellComplex_proof

end HomotopyHypothesis.Realization.Boundary
