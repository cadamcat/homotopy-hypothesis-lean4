import HomotopyHypothesis.Approximation.Topological.DerivedPrismTopology.ExistsDprismProjections

/-!
# Projections of the derived cylinder

The derived cylinder `D V` projects onto `‖V‖` in two ways: simplicially (`pr`: `top i ↦ i`,
`mid S ↦ max S`, on each derived cylinder of a simplex) and affinely (`πe`: `top i ↦ i`,
`mid S ↦` the barycentre of `S`). They agree on the top end `V`, and the straight line joins them
relative to it. On the derived end, `πe` is the barycentric homeomorphism `‖V'‖ ≅ ‖V‖` and `pr` is
the last vertex map.
-/

/-! The declarations of this file that the development uses are in the modules `HomotopyHypothesis.Approximation.Topological.DerivedPrismTopology.*`, one declaration per module. -/
