import HomotopyHypothesis.Blueprint.Bridge.FaceToOAI
import HomotopyHypothesis.Blueprint.Bridge.FaceOfOAI
import HomotopyHypothesis.Blueprint.Bridge.GlobeToOAI
import HomotopyHypothesis.Blueprint.Bridge.GlobeOfOAI
import HomotopyHypothesis.Blueprint.Bridge.GlobeToOAICompGlobeOfOAI
import HomotopyHypothesis.Blueprint.Bridge.GlobeOfOAICompGlobeToOAI
import HomotopyHypothesis.Blueprint.Bridge.TopGlobesEq
import HomotopyHypothesis.Blueprint.Bridge.StatementOfOaiStatement

/-!
# Transport between the statement's vocabulary and OpenAI's library

`Challenge.lean` copies OpenAI's Comparator definitions verbatim into the namespace
`HomotopyHypothesis.Grothendieck`; the library defines the same notions in `OAI.Grothendieck`.
The two are distinct declarations, so the statement is transported explicitly.

Proved here: the globe categories are isomorphic (constructor by constructor), and under this
isomorphism the statement's topological globes are OpenAI-side globes (`rfl` on objects and on
each face). The remaining transport is the package `statement_of_oaiStatement`.
-/

/-! The declarations of this file that the development uses are in the modules `HomotopyHypothesis.Blueprint.Bridge.*`, one declaration per module. -/
