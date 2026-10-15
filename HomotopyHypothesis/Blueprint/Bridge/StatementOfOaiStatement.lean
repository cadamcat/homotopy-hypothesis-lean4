import HomotopyHypothesis.Bridge.Statement.Main
import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Challenge

/-!
# `statement_of_oaiStatement`

One declaration of `HomotopyHypothesis.Blueprint.Bridge`, in its own module so that it can import the module that proves it.
-/

noncomputable section

namespace HomotopyHypothesis.Blueprint

universe u

open CategoryTheory

namespace Packages

/-- **Bridge.** The statement on the definitions copied in `Challenge.lean` follows from the same
statement on OpenAI's library definitions. Route: extend `globeToOAI` to tables (an isomorphism of
inductive types) and to shapes, identifying the chosen realizations of shapes up to the canonical
isomorphisms of iterated pushouts; transport each globular theory (same hom-types, base maps
conjugated by these isomorphisms), its admissible pairs, free extensions, cellular presentation and
coherator property, its models (an isomorphism of categories), units, homotopy groups and weak
equivalences, and its topological realizations (using `topGlobes_eq`); `Π_∞` commutes with these
transports, and `Functor.IsLocalization` is invariant under the resulting isomorphism of
categories of models. -/
theorem statement_of_oaiStatement : OAIStatement.{u} → Statement.{u} := @_root_.HomotopyHypothesis.Blueprint.Packages.statement_of_oaiStatement_proof
