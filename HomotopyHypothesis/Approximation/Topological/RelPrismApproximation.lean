import HomotopyHypothesis.Approximation.Topological.RelPrismApproximation.Part1
import HomotopyHypothesis.Approximation.Topological.RelPrismApproximation.Part2

/-!
# Relative simplicial approximation through a relative prism

Proof of `exists_relPrism_simplicialApproximation` (Rourke–Sanderson, *Δ-sets I*, Thm. 5.1, finite
case). The image of `f` lies in a finite `X₀ ⊇ g J`. Zeeman's theorem, applied to the second derived
subdivisions `F Y` (modulo `F J`) and `F X₀`, gives a subdivision `S₁` of `F Y` and a simplicial
approximation `g₁`; composed with the last vertex map of `X₀` it is simplicial into `X`, and on
`F J` it equals `lv ≫ ‖g‖`. The prism `P J` of the derived subdivision, attached along `F J`, is
a collar from `F J` to an unsubdivided copy of `J`, on which the simplicial projection followed by
`‖g‖` continues the map. The prism `P Y`, attached to Zeeman's prism along `F Y`, gives the prism
from the result to `Y`.
-/

/-! This file is split into the modules `HomotopyHypothesis.Approximation.Topological.RelPrismApproximation.Part*` so that the modules of the development form an acyclic import graph. -/
