import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Dprism
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Inst42
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismCos
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismTop

/-!
# `HomotopyHypothesis.Approximation.DerivedPrismNaturality.Proofs`, part 2

Lines 107–116 of `HomotopyHypothesis.Approximation.DerivedPrismNaturality.Proofs`, split so that the modules of the development form an acyclic import graph.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.DerivedPrismNaturality

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet
open HomotopyHypothesis.Approximation.Topological

theorem dprismTop_naturality_proof {x y : Henry.SemiSimplexCategory} (θ : x ⟶ y) :
    Henry.SemiSSet.stdSimplex.map θ ≫ dprismTop.{u} y.obj.len =
      dprismTop.{u} x.obj.len ≫ dprismCos.map θ := by
  apply uliftYonedaEquiv.injective
  simp only [uliftYonedaEquiv_comp]
  apply ULift.ext
  apply Subtype.ext
  funext i
  rfl
