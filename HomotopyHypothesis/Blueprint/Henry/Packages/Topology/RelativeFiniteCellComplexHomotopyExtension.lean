import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Homotopy.ExtensionPrinciple.Proofs.Part1

/-!
# `relativeFiniteCellComplex_homotopyExtension`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Topology`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra TopCat

namespace HomotopyHypothesis.Henry.Packages

/-- **Homotopy extension property** of relative finite cell complexes (Hatcher, Prop. 0.16, by
induction over the attachments in any order of dimensions, using that `𝔻 n × [0, 1]` retracts onto
`𝔻 n × {0} ∪ ∂𝔻 n × [0, 1]` and that the product with `[0, 1]` preserves the pushouts). For a
relative finite cell complex `i : A ⟶ B`, a map `f : B ⟶ Z` and a homotopy starting at `f ∘ i`
extend to a homotopy starting at `f`. -/
theorem relativeFiniteCellComplex_homotopyExtension {A B Z : TopCat.{u}} (i : A ⟶ B)
    (hi : Top.relativeFiniteCellComplexes i) (f : C(B, Z)) (g : C(A, Z))
    (H : (f.comp i.hom).Homotopy g) :
    ∃ (g' : C(B, Z)) (H' : f.Homotopy g'), ∀ (t : unitInterval) (a : A), H' (t, i.hom a) = H (t, a) :=
  by apply @_root_.HomotopyHypothesis.Homotopy.ExtensionPrinciple.relativeFiniteCellComplex_homotopyExtension_proof <;> assumption
