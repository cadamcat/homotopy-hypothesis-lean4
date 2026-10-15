import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.DerivedPrismNaturality.Proofs.Part2
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Dprism
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismCos
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismTop

/-!
# `dprismTop_naturality`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet PV

namespace PV

variable {k l : ℕ}

end PV

/-- The top ends of the derived cylinders. Frozen helper statement for the naturality. -/
theorem dprismTop_naturality {x y : Henry.SemiSimplexCategory} (θ : x ⟶ y) :
    Henry.SemiSSet.stdSimplex.map θ ≫ dprismTop.{u} y.obj.len = dprismTop.{u} x.obj.len ≫ dprismCos.map θ :=
  _root_.HomotopyHypothesis.Approximation.DerivedPrismNaturality.dprismTop_naturality_proof ..
