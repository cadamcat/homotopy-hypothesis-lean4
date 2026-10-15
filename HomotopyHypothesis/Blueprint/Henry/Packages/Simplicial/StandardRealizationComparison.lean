import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Realization.SemisimplicialComparison.Comparison

/-!
# `standardRealization_comparison`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Simplicial`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopyHypothesis.Henry.Packages

/-- H Lemma 5.2.6 (H:2880–2912): for a standard realization `R`, the comparison maps
`φ_X : ‖X‖ ⟶ R X` from the realization of the underlying semi-simplicial set (sending the realized
simplex of `σ : Δ_n ⟶ X` to `R` of the corresponding map out of the free simplex) form a natural
transformation of homotopy equivalences. Each `X` is obtained by cell attachments followed by free
additions of horn fillers (H:2891–2894); the horn attachments realize to strong deformation
retracts, also after infinitely many of them (the horn prism `(Λ^n_k × I) ∪ (Δ^n × ∂I)` is a
retract of `Δ^n × I`; compatible cellwise homotopies glue), and the gluing lemma for finite cell
attachments concludes. On objects free on `∂Δ_n` or `Δ_n` the composite `‖∂Δ_n‖ ⟶ ‖X‖ ⟶ R X`
(resp. `‖Δ_n‖ ⟶ ‖X‖ ⟶ R X`) is an isomorphism. Inputs: `realization_hornCells_deformationRetract`,
`homotopyEquivalence_of_isPushout`, `realization_boundary_relativeFiniteCellComplex`. -/
theorem standardRealization_comparison {R : CDelta.{u} ⥤ TopCat.{u}}
    (hR : IsStandardRealization R) :
    ∃ φ : ObjectProperty.ι AlgKan.IsFinitelyCellular.{u} ⋙ AlgKan.forget ⋙ SemiSSet.realization ⟶
      R,
      (∀ X : CDelta.{u}, Top.homotopyEquivalences (φ.app X)) ∧
      (∀ (n : ℕ) (Y : CDelta.{u}) (η : (SemiSSet.boundary.{u} n).toFunctor ⟶ Y.obj.X),
        Y.obj.IsFreeOn η → IsIso (SemiSSet.realization.map η ≫ φ.app Y)) ∧
      ∀ (n : ℕ) (Y : CDelta.{u})
        (η : SemiSSet.stdSimplex.obj (SemiSimplexCategory.mk n) ⟶ Y.obj.X),
        Y.obj.IsFreeOn η → IsIso (SemiSSet.realization.map η ≫ φ.app Y) := by apply @_root_.HomotopyHypothesis.Realization.SemisimplicialComparison.standardRealization_comparison_proof <;> assumption
