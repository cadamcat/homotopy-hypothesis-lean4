import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.RelPrismApproximation.Part2

/-!
# `exists_relPrism_simplicialApproximation`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Approximation`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Henry.Packages

open SemiSSet

/-- **Relative simplicial approximation for semi-simplicial sets** (Rourke–Sanderson, Thm. 5.1,
finite case). Let `Y` be finite, `J ⊆ Y`, `g : J ⟶ X` and `f : ‖Y‖ ⟶ ‖X‖` with `f = ‖g‖` on
`‖J‖`. There is a relative prism `S` of `Y` relative to `J` and a simplicial map
`f' : ‖S.Y'‖ ⟶ ‖X‖` equal to `‖g‖` on `J`, such that `f'`, transported to `‖Y‖` through the prism,
is homotopic to `f` relative to `‖J‖`. Proof: the image of `f` lies in a finite `X₀ ⊇ g J`
(`realization_exists_finite_subcomplex`); apply `zeeman_relativeApproximation` to the second derived
subdivisions `F Y` modulo `F J` and `F X₀` (`exists_derivedSubdivision`) and compose with the last
vertex map of `X₀`; attach the prism `P J` to the subdivision along `F J` (the collar of `J`), and
the prism `P Y` to Zeeman's prism along `F Y`. -/
theorem exists_relPrism_simplicialApproximation {Y X : SemiSSet.{u}} (hY : Y.IsFinite)
    (J : Subfunctor Y) (g : J.toFunctor ⟶ X) (f : realization.obj Y ⟶ realization.obj X)
    (hf : realization.map J.ι ≫ f = realization.map g) :
    ∃ (S : RelPrism Y J) (f' : realization.obj S.Y' ⟶ realization.obj X),
      IsSimplicial f' ∧ realization.map S.j ≫ f' = realization.map g ∧
        (realization.map S.c₁ ≫ S.ρ ≫ f').hom.HomotopicRel f.hom
          (Set.range (realization.map J.ι).hom) := by apply (config := {allowSynthFailures := true}) @_root_.HomotopyHypothesis.Approximation.Topological.exists_relPrism_simplicialApproximation_proof <;> assumption
