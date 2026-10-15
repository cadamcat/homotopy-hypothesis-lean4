import HomotopyHypothesis.Blueprint.Interfaces.ExistsRealization
import HomotopyHypothesis.Blueprint.Interfaces.PiComparison
import HomotopyHypothesis.Blueprint.Interfaces.CompressionCriterion
import HomotopyHypothesis.Blueprint.Interfaces.PiIsRightAdjoint
import HomotopyHypothesis.Blueprint.Interfaces.WeakEquivalenceClosure
import HomotopyHypothesis.Blueprint.Interfaces.WeakEquivalenceTwoOutOfSix
import HomotopyHypothesis.Blueprint.Interfaces.LiftingTest
import HomotopyHypothesis.Blueprint.Interfaces.Fibrant
import HomotopyHypothesis.Blueprint.Interfaces.TrivialCofibrationLift
import HomotopyHypothesis.Blueprint.Interfaces.DiskFinitelyCellular
import HomotopyHypothesis.Blueprint.Interfaces.Disk0
import HomotopyHypothesis.Blueprint.Interfaces.AfinEssentiallySmall
import HomotopyHypothesis.Blueprint.Interfaces.AfinIotaMapInitial
import HomotopyHypothesis.Blueprint.Interfaces.AfinIotaMapIsPushout
import HomotopyHypothesis.Blueprint.Interfaces.AfinIsCylinderCategory
import HomotopyHypothesis.Blueprint.Interfaces.Disk0IsHTerminal
import HomotopyHypothesis.Blueprint.Interfaces.AfinIsCofibrantAt
import HomotopyHypothesis.Blueprint.Interfaces.AfinLiftsAtHTerminal
import HomotopyHypothesis.Blueprint.Interfaces.AfinIsCylinderCoherator
import HomotopyHypothesis.Blueprint.Interfaces.Restriction
import HomotopyHypothesis.Blueprint.Interfaces.CompletionIsEquivalence
import HomotopyHypothesis.Blueprint.Interfaces.CompletionWeakEquivalencesIff
import HomotopyHypothesis.Blueprint.Interfaces.CompletionWeakEquivalencesRespectsIso
import HomotopyHypothesis.Blueprint.Interfaces.CellularRealization
import HomotopyHypothesis.Blueprint.Interfaces.ContractibleDisk0
import HomotopyHypothesis.Blueprint.Interfaces.TopRestrictionIso
import HomotopyHypothesis.Blueprint.Interfaces.HenryComparison

/-!
# Packages of the outer blueprint

Each theorem below is a step of the proof, with its mathematical source. Sources:

* `A:n`: D. Ara, *On the homotopy theory of Grothendieck ∞-groupoids*, arXiv:1206.2941, line `n`
  of the TeX source.
* `H:n`: S. Henry, *Algebraic models of homotopy types and the homotopy hypothesis*,
  arXiv:1609.04622 v1, line `n` of the TeX source.
* `OA:k:n`: OpenAI, *The Grothendieck homotopy hypothesis via elementary expansions*, section file
  `k` (`01` preliminaries, `02` cutoffs and trees, `04` consequences), line `n`.

The packages fall into three groups (the transport to OpenAI's library definitions is in
`Blueprint/Bridge.lean`): the topological
side (realizations, `Π_∞` and homotopy groups, weak homotopy equivalences); the semi-model facts
of OpenAI's Cor. 4.1 that the chain uses; and the category `A_fin` of finitely cellular models,
which is a cylinder coherator whose completion is the category of models. Henry's comparison
theorem for cylinder coherators is imported through one interface package.
-/

/-! The declarations of this file that the development uses are in the modules `HomotopyHypothesis.Blueprint.Interfaces.*`, one declaration per module. -/
