import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismCos

/-!
# `dprismLan`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet PV

namespace PV

variable {k l : ℕ}

end PV

/-- The derived cylinder `D W` of a semi-simplicial set. -/
noncomputable abbrev dprismLan : SemiSSet.{u} ⥤ SemiSSet.{u} :=
  Henry.SemiSSet.stdSimplex.{u}.leftKanExtension dprismCos.{u}
