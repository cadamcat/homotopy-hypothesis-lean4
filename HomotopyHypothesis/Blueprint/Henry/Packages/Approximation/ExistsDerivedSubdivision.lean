import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Approximation.Topological.DerivedSubdivisionProof

/-!
# `exists_derivedSubdivision`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Approximation`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Henry.Packages

open SemiSSet

/-- **Second derived subdivision with its prism** (Rourke–Sanderson §4, Lemmas 4.2–4.3: after
deriving twice, a semi-simplicial set is an ordered simplicial complex; derived cylinders collapse
onto their derived end). The second barycentric derived `F` (cone points ordered after the vertices
of their base) with its natural homeomorphism `e`, last vertex map `lv`, the straight-line homotopy
between them, and the prism `P W = D(W) ∪_{W'} D(W')` of two derived cylinders; see
`DerivedSubdivision`. -/
theorem exists_derivedSubdivision : Nonempty DerivedSubdivision.{u} := @_root_.HomotopyHypothesis.Approximation.Topological.exists_derivedSubdivision_proof
