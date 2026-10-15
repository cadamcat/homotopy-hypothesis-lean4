import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Gluing.Simplicial.Glue

/-!
# `isFinite_of_isPushout`

One declaration of `HomotopyHypothesis.Approximation.Topological.GlueStatements`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- A pushout of finite semi-simplicial sets is finite. -/
theorem isFinite_of_isPushout {A B C D : SemiSSet.{u}} {f : A ⟶ B} {g : A ⟶ C} {h : B ⟶ D}
    {k : C ⟶ D} (sq : IsPushout f g h k) (hB : B.IsFinite) (hC : C.IsFinite) : D.IsFinite :=
  by apply @_root_.HomotopyHypothesis.Gluing.Simplicial.isFinite_of_isPushout_proof <;> assumption
