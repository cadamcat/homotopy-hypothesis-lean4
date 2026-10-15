import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Approximation.CompactFactorization.Factorization

/-!
# `exists_factorization_of_compactSpace`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Topology`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra TopCat

namespace HomotopyHypothesis.Henry.Packages

/-- **Compact support in cell complexes** (Hirschhorn, Props. 4.10–4.11 and Cor. 4.12, which allow
any order of the attachments). Let `f : X ⟶ Y` be a transfinite composition of relative finite cell
complexes starting from a finite cell complex `X`. Then the maps from the stages to `Y` are
injective, and every map from a compact space to `Y` factors through some stage. (A compact subset
of a cell complex meets only finitely many cells.) -/
theorem exists_factorization_of_compactSpace {J : Type u} [LinearOrder J] [SuccOrder J]
    [OrderBot J] [WellFoundedLT J] {X Y : TopCat.{u}} {f : X ⟶ Y}
    (c : Top.relativeFiniteCellComplexes.TransfiniteCompositionOfShape J f)
    (hX : Top.IsFiniteCellComplex X) :
    (∀ j : J, Function.Injective (c.incl.app j).hom) ∧
    ∀ (K : TopCat.{u}) [CompactSpace K] (g : K ⟶ Y),
      ∃ (j : J) (g' : K ⟶ c.F.obj j), g' ≫ c.incl.app j = g := by apply @_root_.HomotopyHypothesis.Henry.Packages.exists_factorization_of_compactSpace_proof <;> assumption
