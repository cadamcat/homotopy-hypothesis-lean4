import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Interfaces.Disk0
import HomotopyHypothesis.FiniteCategory.Lifting.ConditionalPackages
import HomotopyHypothesis.FiniteCategory.Lifting.RealizationInputs
/-!
# Pointed lifting for finite cellular models of a coherator

The finite cellular category is cofibrant relative to its zero-dimensional disk, and its exact
functors lift along pre-fibrations at homotopically terminal marked objects.
-/

universe u

open OAI.Grothendieck HomotopyHypothesis.Henry

namespace HomotopyHypothesis.Blueprint.Packages

/-- Relative cofibrancy of the finite cellular category at the zero-dimensional disk. -/
theorem afin_isCofibrantAt_proof {C : GlobularTheory.{u}} (hC : C.IsCoherator) :
    IsCofibrantAt.{u + 1, u} (Afin C hC) (disk0 hC) :=
  FiniteCategory.Lifting.afin_isCofibrantAt_of_helpers hC (FiniteCategory.Lifting.boundaryAdjointFamily_proof C)
    (FiniteCategory.Lifting.afinFunctorComparisonFamily_proof hC)

#print axioms HomotopyHypothesis.Blueprint.Packages.afin_isCofibrantAt_proof

/-- Pointed lifting at homotopically terminal objects for the finite cellular category. -/
theorem afin_liftsAtHTerminal_proof {C : GlobularTheory.{u}} (hC : C.IsCoherator) :
    LiftsAtHTerminal.{u + 1, u} (Afin C hC) (disk0 hC) :=
  FiniteCategory.Lifting.afin_liftsAtHTerminal_of_helpers hC (FiniteCategory.Lifting.boundaryAdjointFamily_proof C)
    (FiniteCategory.Lifting.afinFunctorComparisonFamily_proof hC)

#print axioms HomotopyHypothesis.Blueprint.Packages.afin_liftsAtHTerminal_proof

end HomotopyHypothesis.Blueprint.Packages
