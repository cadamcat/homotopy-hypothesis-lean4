import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.FiniteCategory.UnitWeakEquivalence.Unit

/-!
# `finCellRestriction_unit_weakEquivalence`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Spaces`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra TopCat

namespace HomotopyHypothesis.Henry.Packages

/-- **The unit is a weak equivalence at cofibrant objects** (H Prop 2.4.16(2) for the inclusion of
finite cell complexes, with the repair of H:1432 by compact support). A cofibrant object `X` of
the completion is a retract of a cellular one, `colim X_i` along pushouts of representable
cofibrations (H:1022–1037); its left adjoint image `L X` is a transfinite composition of relative
finite cell complexes starting from the empty space, so for every finite cell complex `d`,
`X(d) = colim Top(d, X_i) ≅ Top(d, L X)` by `exists_factorization_of_compactSpace` (applied to
`d` and to `d × [0, 1]` for homotopies). Hence the unit `X ⟶ R (L X)` is an isomorphism on cellular
objects and a weak equivalence on their retracts. -/
theorem finCellRestriction_unit_weakEquivalence
    (hι : IsCellularRealization (ObjectProperty.ι Top.IsFiniteCellComplex.{u}))
    {L : Completion.{u} FinCell.{u} ⥤ TopCat.{u}} (adj : L ⊣ topRestriction hι)
    (X : Completion.{u} FinCell.{u})
    (hX : IsCofibrantFor (Completion.cofibrations FinCell.{u}) X) :
    Completion.weakEquivalences FinCell.{u} (adj.unit.app X) := by apply @_root_.HomotopyHypothesis.Henry.Packages.finCellRestriction_unit_weakEquivalence_proof <;> assumption
