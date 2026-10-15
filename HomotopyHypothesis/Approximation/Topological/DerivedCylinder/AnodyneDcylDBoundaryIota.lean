import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Cylinder.DoubleBoundaryCollapse.Proof
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylD
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDBoundary
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDBoundaryIota

/-!
# `anodyne_dcylDBoundaryι`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedCylinder`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

namespace DV

variable {n m : ℕ}

end DV

open DV

/-- **The derived double cylinder collapses onto its boundary** (Rourke–Sanderson, Lemmas 4.3 and
4.4: the prism derived at one end collapses onto that end and its sides; the mapping cylinder on
the derived simplex collapses onto its target and its sides). Frozen helper statement. -/
theorem anodyne_dcylDBoundaryι {n m : ℕ} (v : Fin (n + 1) → Fin (m + 1)) :
    anodyne (dcylDBoundaryι.{u} v) := _root_.HomotopyHypothesis.Cylinder.DoubleBoundaryCollapse.anodyne_dcylDBoundaryι_proof ..
