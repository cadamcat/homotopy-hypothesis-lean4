import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Realization.Boundary.RealizationBoundary
/-!
# The realized simplex pair is the disk pair

`(‖Δ_n‖, ‖∂Δ_n‖) ≅ (𝔻 n, ∂𝔻 n)` (Hatcher, Example 0.3), from the barycentric-coordinate model.
-/

universe u

open CategoryTheory Limits

namespace HomotopyHypothesis.Realization.SemisimplicialComparison

open HomotopyHypothesis.Henry

/-- The realized boundary inclusion of a simplex is isomorphic, as an arrow, to the inclusion of
the boundary sphere of the disk. -/
theorem nonempty_diskArrowIso (n : ℕ) :
    Nonempty (CategoryTheory.Arrow.mk (SemiSSet.realization.{u}.map (SemiSSet.boundary.{u} n).ι) ≅
      CategoryTheory.Arrow.mk (TopCat.diskBoundaryInclusion.{u} n)) :=
  ⟨Arrow.isoMk (TopCat.isoOfHomeo (Realization.Boundary.realizationBoundaryToDiskBoundaryHomeomorph n))
    (Realization.Boundary.realizationSimplexToDiskIso n)
    (Realization.Boundary.realizationBoundaryToDiskBoundary_square n).symm⟩

end HomotopyHypothesis.Realization.SemisimplicialComparison
