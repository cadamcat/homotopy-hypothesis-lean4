import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.CylinderCategoryTheory.Proofs

/-!
# `homotopyEquivalence_of_contractibleSpace`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Classical`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial

namespace HomotopyHypothesis.Henry.Packages

/-- Any map between contractible spaces is a homotopy equivalence. -/
theorem homotopyEquivalence_of_contractibleSpace {X Y : TopCat.{u}} [ContractibleSpace X]
    [ContractibleSpace Y] (f : X ⟶ Y) : Top.homotopyEquivalences f := _root_.HomotopyHypothesis.CylinderCategoryTheory.homotopyEquivalence_of_contractibleSpace_proof ..
