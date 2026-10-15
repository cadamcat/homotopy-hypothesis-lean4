import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismCos
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismTop
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismTopNaturality

/-!
# `dprismTopCos`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet PV

namespace PV

variable {k l : ℕ}

end PV

/-- The top ends of the derived cylinders, as a natural transformation. -/
noncomputable def dprismTopCos : Henry.SemiSSet.stdSimplex.{u} ⟶ dprismCos.{u} where
  app x := dprismTop x.obj.len
  naturality _ _ θ := dprismTop_naturality θ
