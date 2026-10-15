import HomotopyHypothesis.Approximation.Topological.DerivedPrismGlue.PrismP
import HomotopyHypothesis.Approximation.Topological.DerivedPrismGlue.PrismTop
import HomotopyHypothesis.Approximation.Topological.DerivedPrismGlue.PrismBot
import HomotopyHypothesis.Approximation.Topological.DerivedPrismGlue.MonoDprismLanTop
import HomotopyHypothesis.Approximation.Topological.DerivedPrismGlue.IsFiniteDprismLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismGlue.AnodynePrismTop
import HomotopyHypothesis.Approximation.Topological.DerivedPrismGlue.IsFiniteOfIso
import HomotopyHypothesis.Approximation.Topological.DerivedPrismGlue.IsSimplicialComplexOfIso

/-!
# The prism of the second derived subdivision

`P W = D W ⊔_{W'} D W'`: the derived cylinder of `W` glued at its derived end `W'` to the derived
cylinder of `W'` at its top end. Its ends are `W` (top end of `D W`) and `W''` (derived end of
`D W'`); it collapses onto `W''` relative to the prism over any `J ⊆ W`.
-/

/-! The declarations of this file that the development uses are in the modules `HomotopyHypothesis.Approximation.Topological.DerivedPrismGlue.*`, one declaration per module. -/
