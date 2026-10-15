import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.FiniteCategory.Restriction.WeakEquivalence

/-!
# `finCellRestriction_weakEquivalence_iff`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Spaces`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra TopCat

namespace HomotopyHypothesis.Henry.Packages

/-- **Weak equivalences of spaces are detected by finite cell complexes** (H:1432–1440 repaired,
H Prop 2.4.16(1)). A map `f` of spaces is in `Top.weakEquivalences` if and only if `R f` is a weak
equivalence of the completion of `FinCell`. Translate relative cylinders of `FinCell` into
homotopies relative to a subcomplex (`finCell_homotopicRel_iff`); then `⇒` is
`relativeLift_of_weakEquivalence`, and `⇐` is the defining property of `R f` applied to the
cofibrations `∂𝔻 n ⟶ 𝔻 n` of `FinCell` (`diskBoundary_isFiniteCellComplex`). -/
theorem finCellRestriction_weakEquivalence_iff
    (hι : IsCellularRealization (ObjectProperty.ι Top.IsFiniteCellComplex.{u})) {X Y : TopCat.{u}}
    (f : X ⟶ Y) :
    Top.weakEquivalences f ↔ Completion.weakEquivalences FinCell.{u} ((topRestriction hι).map f) :=
  _root_.HomotopyHypothesis.FiniteCategory.Restriction.finCellRestriction_weakEquivalence_iff_proof ..
