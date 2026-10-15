import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DV
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.Code
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.CodeInjective
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.Rank
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.RankInjective
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.Inst57
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDComplex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDBoundaryComplex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylD
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDBoundary
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDBoundaryIota
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDBot
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDTop
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.AnodyneDcylDBoundaryIota

/-!
# Derived double cylinders of vertex maps

For a vertex map `v : [n] ⟶ [m]`, the derived double cylinder `DCyl v` is the ordered simplicial
complex with vertices `top i` (`i ∈ [n]`), `mid S` (`S` a nonempty face of `Δ_n`, the barycentre
of `S`) and `bot c` (`c ∈ [m]`), ordered mid < top < bot, the middle vertices by decreasing size.
Its simplices are the sets `T ∪ {mid S₀ ⊋ ⋯ ⊋ mid S_r} ∪ B` with `T` and `B` not both nonempty,
`T ⊆ S_r` and `B ⊆ v(S_r)` (no condition when there is no middle vertex). The top half (top and
middle vertices) is the prism `Δ_n × I` derived at the middle end (Rourke–Sanderson, Lemma 4.3);
the bottom half (middle and bottom vertices) is the simplicial mapping cylinder of `v` on the
derived `Δ_n` (Cohen; Rourke–Sanderson §4, Lemma 4.4). Unlike staircase cylinders, the cylinders
over two faces of `Δ_n` meet exactly in the cylinder over their intersection.

The boundary `∂DCyl v` is the bottom `Δ_m` together with the cylinders over the proper faces of
`Δ_n`.
-/

/-! The declarations of this file that the development uses are in the modules `HomotopyHypothesis.Approximation.Topological.DerivedCylinder.*`, one declaration per module. -/
