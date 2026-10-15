import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.FiniteCategory.CellularRealization.IsCellularRealization

/-!
# `isCellularRealization_finCellι`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Topology`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra TopCat

namespace HomotopyHypothesis.Henry.Packages

/-- The inclusion of finite cell complexes into spaces is a cellular realization of the cylinder
category of finite cell complexes: the empty space is a finite cell complex, initial objects of
`FinCell` are empty, and the pushout in spaces of a relative finite cell complex between finite cell
complexes along a map of finite cell complexes is a finite cell complex, hence is the pushout in
`FinCell` (Hirschhorn, §4; the attachment order of the cells is arbitrary). -/
theorem isCellularRealization_finCellι :
    IsCellularRealization (ObjectProperty.ι Top.IsFiniteCellComplex.{u}) := @_root_.HomotopyHypothesis.FiniteCategory.CellularRealization.isCellularRealization_finCellι_proof
