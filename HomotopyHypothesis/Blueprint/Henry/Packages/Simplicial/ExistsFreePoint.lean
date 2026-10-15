import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Realization.SemisimplicialComparison.FreePoint

/-!
# `exists_free_point`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Simplicial`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopyHypothesis.Henry.Packages

/-- Existence of free cells: the free algebraic Kan complex on `Δ₀` is finitely cellular (one cell
attached to the empty complex). Free algebraic Kan complexes and free cell attachments exist since
algebraic Kan complexes are the models of a finite-limit sketch (H:1577–1742, used concretely as in
H Prop 3.2.4). -/
theorem exists_free_point :
    ∃ (o : CDelta.{u}) (η : SemiSSet.stdSimplex.obj (SemiSimplexCategory.mk 0) ⟶ o.obj.X),
      o.obj.IsFreeOn η := @_root_.HomotopyHypothesis.Realization.SemisimplicialComparison.exists_free_point_proof
