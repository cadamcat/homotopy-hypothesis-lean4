import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.FiniteCategory.Restriction.RightAdjoint

/-!
# `finCellRestriction_isRightAdjoint`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Spaces`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra TopCat

namespace HomotopyHypothesis.Henry.Packages

/-- **The restricted Hom functor has a left adjoint** (H Prop 2.4.15, H:1355). The left adjoint
sends a completion presheaf `X` to the colimit of the finite cell complexes over its elements (the
left Kan extension of the inclusion along the Yoneda embedding, computed on a small skeleton of
`FinCell`, `finCell_essentiallySmall`); `TopCat` is cocomplete. -/
theorem finCellRestriction_isRightAdjoint
    (hι : IsCellularRealization (ObjectProperty.ι Top.IsFiniteCellComplex.{u})) :
    (topRestriction hι).IsRightAdjoint := _root_.HomotopyHypothesis.FiniteCategory.Restriction.finCellRestriction_isRightAdjoint_proof ..
