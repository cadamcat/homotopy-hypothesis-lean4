import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Simplicial.BarycentricSubdivision.DerivedSubdivision
import HomotopyHypothesis.Simplicial.SubdivisionComparison.Proof
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdLan

/-!
# `nonempty_sdLanIso`

One declaration of `HomotopyHypothesis.Approximation.Topological.DerivedSubdivisionCompare`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- **The glued derived subdivision is the nerve of strict chains of faces**, naturally. A simplex of
`sdLan W` is represented by a simplex `x` of `W` and a strictly increasing chain of nonempty faces
`S₀ ⊊ ⋯ ⊊ S_r` of `Δ_{dim x}`, modulo faces of `x`; its normal form has `S_r = [dim x]`, and it
corresponds to the strict chain of the faces of `x` along `S₀ ⊊ ⋯ ⊊ S_r` in the face category of
`W`. Frozen helper statement. -/
theorem nonempty_sdLanIso : Nonempty (sdLan.{u} ≅ Simplicial.BarycentricSubdivision.firstSubdivision.{u}) := @_root_.HomotopyHypothesis.Simplicial.SubdivisionComparison.nonempty_sdLanIso_proof
