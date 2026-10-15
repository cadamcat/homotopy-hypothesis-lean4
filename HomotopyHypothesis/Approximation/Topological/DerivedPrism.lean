import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Rank
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.RankInjective
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Inst42
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismBdryComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Dprism
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismBdry
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismBdryIota

/-!
# The derived cylinder of a simplex

For `k : ℕ`, the derived cylinder `D Δ_k` is the ordered simplicial complex with vertices `top i`
(`i ∈ [k]`) and `mid S` (`S` a nonempty face of `Δ_k`, its barycentre), ordered top < mid, the
middle vertices by increasing size. Its simplices are the sets `T ∪ {mid S₀ ⊊ ⋯ ⊊ mid S_r}` with
`T ⊆ S₀` (no condition when there is no middle vertex). It is the prism `Δ_k × I` with the end
`Δ_k` (top) and the derived `Δ_k` (middle) (Rourke–Sanderson, Lemma 4.3), and it is the cone from
`mid [k]` over the top face and the derived cylinders of the proper faces; it collapses onto the
derived end together with the derived cylinders of the proper faces.
-/

/-! The declarations of this file that the development uses are in the modules `HomotopyHypothesis.Approximation.Topological.DerivedPrism.*`, one declaration per module. -/
