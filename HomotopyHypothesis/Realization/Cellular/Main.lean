import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Realization.Cellular.BoundaryComparison
import HomotopyHypothesis.Realization.Cellular.EndpointLifting
import HomotopyHypothesis.Realization.Cellular.HemisphereLifting
noncomputable section

open CategoryTheory Limits
open OAI.Grothendieck
open HomotopyHypothesis.Henry

namespace HomotopyHypothesis.Blueprint.Packages

universe u

/-- A topological realization restricts to a cellular realization on finitely cellular objects. -/
theorem cellularRealization_proof {C : GlobularTheory.{u}} (hC : C.IsCoherator)
    (R : OAIRealization C) (L : C.Model ⥤ TopCat.{u}) (adj : L ⊣ R.Pi) :
    IsCellularRealization (Afin.ι hC ⋙ L) :=
  Realization.Cellular.cellularRealization_of_cells_and_pathLifting hC R L adj
    (Realization.Cellular.realizationBoundary_mem R L adj)
    (Realization.Cellular.realizationSource_hasLiftingProperty R L adj)

end HomotopyHypothesis.Blueprint.Packages

namespace HomotopyHypothesis.Realization.Cellular

universe u

/-- A topological realization is cellular on finitely cellular objects. -/
theorem cellularRealization_proof {C : GlobularTheory.{u}} (hC : C.IsCoherator)
    (R : Blueprint.OAIRealization C) (L : C.Model ⥤ TopCat.{u}) (adj : L ⊣ R.Pi) :
    IsCellularRealization (Blueprint.Afin.ι hC ⋙ L) :=
  Blueprint.Packages.cellularRealization_proof hC R L adj

end HomotopyHypothesis.Realization.Cellular
