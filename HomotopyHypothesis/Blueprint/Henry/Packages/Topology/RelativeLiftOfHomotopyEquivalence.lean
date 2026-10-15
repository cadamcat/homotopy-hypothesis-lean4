import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Homotopy.RelativeLifting.HomotopyEquivalence.Part1

/-!
# `relativeLift_of_homotopyEquivalence`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Topology`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra TopCat

namespace HomotopyHypothesis.Henry.Packages

/-- **Relative homotopy classes and homotopy equivalences** (Brown, 7.2.5 Cor. 1 and 7.2.6). For a
relative finite cell complex `i : A ⟶ B` and a homotopy equivalence `φ : Y ⟶ Z`, composition with
`φ` is a bijection from extensions of `a : A ⟶ Y` along `i` modulo homotopy relative to `A` to
extensions of `a ≫ φ` modulo homotopy relative to `A`: every extension of `a ≫ φ` is homotopic
relative to `A` to the image of an extension of `a` (surjectivity), and two extensions of `a` whose
images are homotopic relative to `A` are homotopic relative to `A` (injectivity). Only the homotopy
extension property is used. -/
theorem relativeLift_of_homotopyEquivalence {A B Y Z : TopCat.{u}} (i : A ⟶ B)
    (hi : Top.relativeFiniteCellComplexes i) (φ : Y ⟶ Z) (hφ : Top.homotopyEquivalences φ) :
    (∀ (a : A ⟶ Y) (g : B ⟶ Z), a ≫ φ = i ≫ g →
      ∃ l : B ⟶ Y, i ≫ l = a ∧ (l ≫ φ).hom.HomotopicRel g.hom (Set.range i.hom)) ∧
    ∀ l l' : B ⟶ Y, i ≫ l = i ≫ l' →
      (l ≫ φ).hom.HomotopicRel (l' ≫ φ).hom (Set.range i.hom) →
        l.hom.HomotopicRel l'.hom (Set.range i.hom) := by apply @_root_.HomotopyHypothesis.Homotopy.RelativeLifting.relativeLift_of_homotopyEquivalence_proof <;> assumption
