import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DV
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylD
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDBot
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDComplex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.Inst57
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.Rank

/-!
# `dcylDTop`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedCylinder`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

namespace DV

variable {n m : ℕ}

end DV

open DV

/-- The top copy of `Δ_n` in the derived double cylinder. -/
def dcylDTop {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1)) :
    stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶ dcylD.{u} v :=
  (dcylDComplex v).simplexMap (fun i => DV.top i)
    (fun _ _ h => by
      change DV.rank _ < DV.rank _
      simpa [DV.rank, Prod.Lex.toLex_lt_toLex] using h)
    ⟨by simp, by simp, by simp, by simp, by simp⟩
