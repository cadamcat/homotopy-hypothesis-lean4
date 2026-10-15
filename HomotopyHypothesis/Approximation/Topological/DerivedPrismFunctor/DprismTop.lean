import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Dprism
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Inst42
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Rank

/-!
# `dprismTop`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet PV

namespace PV

variable {k l : ℕ}

end PV

/-- The top face of the derived cylinder of `Δ_k`. -/
noncomputable def dprismTop (k : ℕ) :
    stdSimplex.obj (Henry.SemiSimplexCategory.mk k) ⟶ dprism.{u} k :=
  (dprismComplex k).simplexMap (fun i => top i)
    (fun _ _ h => by
      change PV.rank _ < PV.rank _
      simpa [PV.rank, Prod.Lex.toLex_lt_toLex] using h)
    ⟨by simp, by simp, by simp⟩
