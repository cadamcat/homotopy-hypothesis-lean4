import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.FiniteRealization.Proofs

/-!
# `vertexMap_comp`

One declaration of `HomotopyHypothesis.Approximation.Topological.A7Statements`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- Composite of affine vertex maps. -/
theorem vertexMap_comp {n m k : ℕ} (v : Fin (n + 1) → Fin (m + 1))
    (w : Fin (m + 1) → Fin (k + 1)) :
    vertexMap.{u} v ≫ vertexMap w = vertexMap (w ∘ v) := _root_.HomotopyHypothesis.Approximation.FiniteRealization.vertexMap_comp_proof ..
