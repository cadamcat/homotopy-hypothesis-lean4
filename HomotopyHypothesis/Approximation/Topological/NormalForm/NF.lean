import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.Complex

/-!
# `NF`

One declaration of `HomotopyHypothesis.Approximation.Topological.NormalForm`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- A normal form: a surjective vertex map onto a simplex of `X`. -/
structure NF (X : SemiSSet.{u}) (n : ℕ) where
  /-- the dimension of the carrier simplex -/
  m : ℕ
  /-- the vertex map -/
  v : Fin (n + 1) → Fin (m + 1)
  /-- the carrier simplex -/
  x : X.obj (op (Henry.SemiSimplexCategory.mk m))
  surj : Function.Surjective v
