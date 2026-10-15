import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdCos

/-!
# `sdLan`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet PV

namespace PV

variable {k l : ℕ}

end PV

/-- The derived subdivision `W'` of a semi-simplicial set. -/
noncomputable abbrev sdLan : SemiSSet.{u} ⥤ SemiSSet.{u} :=
  Henry.SemiSSet.stdSimplex.{u}.leftKanExtension sdCos.{u}
