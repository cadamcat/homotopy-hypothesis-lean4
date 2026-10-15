import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Gluing.FiniteCellular.Gluing

/-!
# `homotopyEquivalence_of_isPushout`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Topology`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra TopCat

namespace HomotopyHypothesis.Henry.Packages

/-- **Gluing lemma** (May–Ponto, Lemma 2.1.3; Brown, Thm. 7.5.7; Hatcher, Prop. 0.18 for the
attaching-map invariance). A map between pushout squares `B ← A → C` and `B' ← A' → C'` whose legs
`A ⟶ B`, `A' ⟶ B'` are relative finite cell complexes, and whose three components are homotopy
equivalences, induces a homotopy equivalence of the pushouts. The spaces `C`, `C'` are
arbitrary. -/
theorem homotopyEquivalence_of_isPushout {A B C P A' B' C' P' : TopCat.{u}} (i : A ⟶ B)
    (f : A ⟶ C) (k : B ⟶ P) (j : C ⟶ P) (i' : A' ⟶ B') (f' : A' ⟶ C') (k' : B' ⟶ P')
    (j' : C' ⟶ P') (vA : A ⟶ A') (vB : B ⟶ B') (vC : C ⟶ C') (φ : P ⟶ P')
    (h : IsPushout i f k j) (h' : IsPushout i' f' k' j') (hi : Top.relativeFiniteCellComplexes i)
    (hi' : Top.relativeFiniteCellComplexes i') (hA : Top.homotopyEquivalences vA)
    (hB : Top.homotopyEquivalences vB) (hC : Top.homotopyEquivalences vC)
    (c₁ : i ≫ vB = vA ≫ i') (c₂ : f ≫ vC = vA ≫ f') (c₃ : k ≫ φ = vB ≫ k')
    (c₄ : j ≫ φ = vC ≫ j') : Top.homotopyEquivalences φ := by apply (config := {allowSynthFailures := true}) @_root_.HomotopyHypothesis.Henry.Packages.homotopyEquivalence_of_isPushout_proof <;> assumption
