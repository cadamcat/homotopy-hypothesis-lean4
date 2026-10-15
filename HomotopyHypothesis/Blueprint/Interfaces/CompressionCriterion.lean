import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Challenge
import HomotopyHypothesis.Completion.Compression.Compression

/-!
# `compression_criterion`

One declaration of `HomotopyHypothesis.Blueprint.Interfaces`, in its own module so that it can import the module that proves it.
-/

noncomputable section

namespace HomotopyHypothesis.Blueprint.Packages

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Henry

/-- **Compression criterion** (H:1432–1440, Rem. 2.4.17 / Prop. 2.4.18, with the repair of the gap
review: direct π-set argument). A continuous map induces bijections on `π₀` and on all homotopy
groups at all base points if and only if it has the relative lifting property up to homotopy
relative to the boundary against every `∂𝔻 n ⟶ 𝔻 n`. -/
theorem compression_criterion :
    Henry.Top.weakEquivalences.{u} = weakHomotopyEquivalences.{u} := @_root_.HomotopyHypothesis.Completion.Compression.compression_criterion_proof
