import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Homotopy.RelativeLifting.WeakEquivalence

/-!
# `relativeLift_of_weakEquivalence`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Topology`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra TopCat

namespace HomotopyHypothesis.Henry.Packages

/-- **Relative lifting against weak homotopy equivalences** (Hatcher, Lemma 4.6 and the relative
form of Prop. 4.22, specialized to relative finite cell complexes). The class
`Top.weakEquivalences` is defined by this lifting property against the cell boundaries
`∂𝔻 n ⟶ 𝔻 n`; it extends to every relative finite cell complex `i : A ⟶ B`: given `a : A ⟶ X` and
`b : B ⟶ Y` with `a ≫ f = i ≫ b`, there is `l : B ⟶ X` extending `a` with `l ≫ f` homotopic to `b`
relative to `A`. Proof by induction over the cells: lift the next cell by the defining property,
glue the resulting homotopy with the constant one on the cells already treated, and extend it over
the remaining cells by `relativeFiniteCellComplex_homotopyExtension`. -/
theorem relativeLift_of_weakEquivalence {A B X Y : TopCat.{u}} (i : A ⟶ B)
    (hi : Top.relativeFiniteCellComplexes i) (f : X ⟶ Y) (hf : Top.weakEquivalences f)
    (a : A ⟶ X) (b : B ⟶ Y) (h : a ≫ f = i ≫ b) :
    ∃ l : B ⟶ X, i ≫ l = a ∧ (l ≫ f).hom.HomotopicRel b.hom (Set.range i.hom) := by apply @_root_.HomotopyHypothesis.Homotopy.RelativeLifting.relativeLift_of_weakEquivalence_proof <;> assumption
