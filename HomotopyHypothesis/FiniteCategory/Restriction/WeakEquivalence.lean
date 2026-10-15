import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.DiskBoundaryIsFiniteCellComplex
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.FinCellHomotopicRelIff
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.RelativeLiftOfWeakEquivalence
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Blueprint.Henry.Topology
universe u

open CategoryTheory Limits HomotopicalAlgebra TopCat HomotopyHypothesis.Henry

namespace HomotopyHypothesis.FiniteCategory.Restriction

private theorem disk_isFiniteCellComplex (n : ℕ) :
    Top.IsFiniteCellComplex (disk.{u} n) := by
  let G : MorphismProperty TopCat.{u} :=
    Top.cellBoundaries.pushouts ⊔ MorphismProperty.isomorphisms TopCat.{u}
  have hboundary : Top.relativeFiniteCellComplexes (initial.to (diskBoundary.{u} n)) :=
    HomotopyHypothesis.Henry.Packages.diskBoundary_isFiniteCellComplex n
  change G.multiplicativeClosure (initial.to (diskBoundary.{u} n)) at hboundary
  have hcell : G (diskBoundaryInclusion.{u} n) := by
    apply Or.inl
    apply MorphismProperty.le_pushouts
    exact MorphismProperty.ofHoms.mk n
  change Top.relativeFiniteCellComplexes (initial.to (disk.{u} n))
  change G.multiplicativeClosure (initial.to (disk.{u} n))
  have heq : initial.to (disk.{u} n) =
      initial.to (diskBoundary.{u} n) ≫ diskBoundaryInclusion.{u} n := by
    apply initial.hom_ext
  rw [heq]
  exact MorphismProperty.multiplicativeClosure.comp_of _ _ hboundary hcell

theorem finCellRestriction_weakEquivalence_iff_proof
    (hι : IsCellularRealization (ObjectProperty.ι Top.IsFiniteCellComplex.{u}))
    {X Y : TopCat.{u}} (f : X ⟶ Y) :
    Top.weakEquivalences f ↔
      Completion.weakEquivalences FinCell.{u} ((topRestriction hι).map f) := by
  constructor
  · intro hf A B i hi a b hab
    change A.obj ⟶ X at a
    change B.obj ⟶ Y at b
    change a ≫ f = i.hom ≫ b at hab
    obtain ⟨l, hli, hrel⟩ :=
      HomotopyHypothesis.Henry.Packages.relativeLift_of_weakEquivalence
        i.hom hi f hf a b hab
    obtain ⟨cyl, h, h₀, h₁⟩ :=
      (HomotopyHypothesis.Henry.Packages.finCell_homotopicRel_iff i hi
        (l ≫ f) b).mp hrel
    refine ⟨l, cyl, h, hli, ?_, ?_⟩
    · change (cyl.j₀ ≫ cyl.c).hom ≫ h = l ≫ f at h₀
      exact h₀
    · change (cyl.j₁ ≫ cyl.c).hom ≫ h = b at h₁
      exact h₁
  · intro hf n a b hab
    let A : FinCell.{u} := ⟨diskBoundary.{u} n,
      HomotopyHypothesis.Henry.Packages.diskBoundary_isFiniteCellComplex n⟩
    let B : FinCell.{u} := ⟨disk.{u} n, disk_isFiniteCellComplex n⟩
    let i : A ⟶ B := ⟨diskBoundaryInclusion.{u} n⟩
    have hi : cofibrations FinCell.{u} i := by
      change Top.relativeFiniteCellComplexes (diskBoundaryInclusion.{u} n)
      apply MorphismProperty.le_multiplicativeClosure
      apply Or.inl
      apply MorphismProperty.le_pushouts
      exact MorphismProperty.ofHoms.mk n
    have h := hf i hi a b hab
    obtain ⟨l, cyl, H, hli, h₀, h₁⟩ := h
    change (cyl.j₀ ≫ cyl.c).hom ≫ H = l ≫ f at h₀
    change (cyl.j₁ ≫ cyl.c).hom ≫ H = b at h₁
    have hrel :=
      (HomotopyHypothesis.Henry.Packages.finCell_homotopicRel_iff i hi
        (l ≫ f) b).mpr ⟨cyl, H, h₀, h₁⟩
    exact ⟨l, hli, hrel⟩

end HomotopyHypothesis.FiniteCategory.Restriction

#print axioms HomotopyHypothesis.FiniteCategory.Restriction.finCellRestriction_weakEquivalence_iff_proof
