import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Horn.DeformationRetraction.Package

/-!
# `realization_hornCells_deformationRetract`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Classical`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial

namespace HomotopyHypothesis.Henry.Packages

/-- **Free horn attachments realize to deformation retracts** (Goerss–Jardine, discussion before
I.3.3; Brown, 7.3.8). If `j : A ⟶ B` is a transfinite composite of pushouts of coproducts of horn
inclusions `Λ^{n+1}_k ⟶ Δ_{n+1}` of semi-simplicial sets (as in the free addition of horn fillers,
H:2891–2894), then `‖j‖` has a retraction `r` with `r ≫ ‖j‖` homotopic to the identity relative to
`‖A‖`. Proof: an explicit retraction of the horn prism `(Λ^n_k × I) ∪ (Δ^n × ∂I) ⊆ Δ^n × I` (radial
projection from a point beyond the missing face) extends homotopies across each horn cell; at limit
stages compatible homotopies glue since `− × I` preserves the colimit. -/
theorem realization_hornCells_deformationRetract {A B : SemiSSet.{u}} (j : A ⟶ B)
    (hj : MorphismProperty.transfiniteCompositions.{u}
      (MorphismProperty.coproducts.{u} (MorphismProperty.ofHoms (fun p : Σ n : ℕ, Fin (n + 2) =>
        (SemiSSet.horn.{u} (p.1 + 1) p.2).ι))).pushouts j) :
    ∃ r : SemiSSet.realization.obj B ⟶ SemiSSet.realization.obj A,
      SemiSSet.realization.map j ≫ r = 𝟙 _ ∧
        (r ≫ SemiSSet.realization.map j).hom.HomotopicRel (ContinuousMap.id _)
          (Set.range (SemiSSet.realization.map j).hom) := by apply @_root_.HomotopyHypothesis.Henry.Packages.realization_hornCells_deformationRetract_proof <;> assumption
