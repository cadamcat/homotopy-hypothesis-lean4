import HomotopyHypothesis.Blueprint.Defs
noncomputable section

namespace HomotopyHypothesis.FiniteCategory.Subcategory

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open OAI.Grothendieck
open OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Blueprint

theorem disk_finitelyCellular_proof (C : GlobularTheory.{u}) (n : ℕ) :
    IsFinitelyCellular C (GlobularTheory.Model.disk C n) := by
  induction n with
  | zero =>
      change finiteCellMaps C (I C 0)
      apply MorphismProperty.le_multiplicativeClosure
      apply Or.inl
      apply MorphismProperty.le_pushouts
      exact MorphismProperty.ofHoms.mk 0
  | succ n ih =>
      let i := I C n
      let G : MorphismProperty C.Model :=
        (MorphismProperty.ofHoms (fun j : ℕ => I C j)).pushouts ⊔
          MorphismProperty.isomorphisms C.Model
      have hinlG : G (pushout.inl i i) := by
        apply Or.inl
        exact (MorphismProperty.ofHoms (fun j : ℕ => I C j)).pushouts_mk
          (IsPushout.of_hasPushout i i)
          (MorphismProperty.ofHoms.mk n)
      have hinl : finiteCellMaps C (pushout.inl i i) :=
        (MorphismProperty.le_multiplicativeClosure G) _ hinlG
      have hboundary : finiteCellMaps C
          (initial.to (disk C n) ≫ pushout.inl i i) := by
        exact MorphismProperty.multiplicativeClosure.comp_of _ _ ih hinlG
      have hboundary' : finiteCellMaps C (initial.to (boundaryDisk C (n + 1))) := by
        have heq : initial.to (boundaryDisk C (n + 1)) =
            initial.to (disk C n) ≫ pushout.inl i i := by
          apply initial.hom_ext
        rw [heq]
        exact hboundary
      have hcellG : G (I C (n + 1)) := by
        apply Or.inl
        apply MorphismProperty.le_pushouts
        exact MorphismProperty.ofHoms.mk (n + 1)
      have hcell : finiteCellMaps C (I C (n + 1)) :=
        (MorphismProperty.le_multiplicativeClosure G) _ hcellG
      have hcomp : finiteCellMaps C
          (initial.to (boundaryDisk C (n + 1)) ≫ I C (n + 1)) :=
        MorphismProperty.multiplicativeClosure.comp_of _ _ hboundary' hcellG
      change finiteCellMaps C (initial.to (disk C (n + 1)))
      have heq : initial.to (disk C (n + 1)) =
          initial.to (boundaryDisk C (n + 1)) ≫ I C (n + 1) := by
        apply initial.hom_ext
      rw [heq]
      exact hcomp

#print axioms disk_finitelyCellular_proof

end HomotopyHypothesis.FiniteCategory.Subcategory
