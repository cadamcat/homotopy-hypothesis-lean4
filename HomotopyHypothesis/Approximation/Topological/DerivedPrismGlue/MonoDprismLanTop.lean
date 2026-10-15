import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.PrismGluing.Proofs
import HomotopyHypothesis.Simplicial.BarycentricSubdivision.DerivedSubdivision
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismLanTop

/-!
# `mono_dprismLanTop`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedPrismGlue`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- The top end of the derived cylinder is a monomorphism. Frozen helper statement. -/
theorem mono_dprismLanTop (W : SemiSSet.{u}) : Mono (dprismLanTop.app W) := _root_.HomotopyHypothesis.Approximation.PrismGluing.mono_dprismLanTop_proof ..
