import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.Map
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.MapId
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.MapComp
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.MapStrictMonoOn
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.MapS
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismHom
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdHom
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdToDprism
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismCos
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdCos
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdToDprismCos
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismTop
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismTopNaturality
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismTopCos
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdLanToDprism
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismLanTop
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.AnodyneDprismLanRel

/-!
# Derived subdivisions and derived cylinders of semi-simplicial sets

The derived cylinders `D Δ_k` and the derived simplices `Δ_k'` (the middle ends) form
cosimplicial semi-simplicial sets; their left Kan extensions along the Yoneda embedding are the
derived cylinder `D W` and the derived subdivision `W'` of a semi-simplicial set `W` (the colimits
over the simplices of `W`). The derived cylinder contains `W` (top end) and `W'` (derived end).
-/

/-! The declarations of this file that the development uses are in the modules `HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.*`, one declaration per module. -/
