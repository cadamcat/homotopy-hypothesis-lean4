import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.CylinderCategoryTheory.Proofs

/-!
# `contractibleSpace_toTop_zero`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Classical`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial

namespace HomotopyHypothesis.Henry.Packages

/-- The topological `0`-simplex is contractible (it is a point). -/
theorem contractibleSpace_toTop_zero :
    ContractibleSpace (SemiSSet.toTop.{u}.obj (SemiSimplexCategory.mk 0)) := @_root_.HomotopyHypothesis.CylinderCategoryTheory.contractibleSpace_toTop_zero_proof
