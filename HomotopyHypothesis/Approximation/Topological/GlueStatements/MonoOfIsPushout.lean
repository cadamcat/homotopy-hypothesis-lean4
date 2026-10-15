import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Gluing.Simplicial.Glue

/-!
# `mono_of_isPushout`

One declaration of `HomotopyHypothesis.Approximation.Topological.GlueStatements`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- Monomorphisms of semi-simplicial sets are stable under pushout. -/
theorem mono_of_isPushout {A B C D : SemiSSet.{u}} {f : A ⟶ B} {g : A ⟶ C} {h : B ⟶ D}
    {k : C ⟶ D} (sq : IsPushout f g h k) [Mono f] : Mono k := by apply (config := {allowSynthFailures := true}) @_root_.HomotopyHypothesis.Gluing.Simplicial.mono_of_isPushout_proof <;> assumption
