import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DV
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDComplex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.Inst57

/-!
# `dcylD`

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

/-- The derived double cylinder, as a semi-simplicial set. -/
abbrev dcylD {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1)) : SemiSSet.{u} :=
  (dcylDComplex v).toSemiSSet
