import Mathlib.Tactic
import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.FiniteRealization.Proofs
import HomotopyHypothesis.Approximation.DerivedPrismTop.CellSingular
import HomotopyHypothesis.Approximation.DerivedPrismTop.DerivedPositions
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Inst42
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismCos
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.SdToDprism
universe u

open CategoryTheory Limits Opposite Convexity

namespace HomotopyHypothesis.Approximation.BarycentricCell

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet
open HomotopyHypothesis.Approximation.Topological
open HomotopyHypothesis.Approximation.DerivedPrismTop

private theorem dprismCellProjection_simplex {k n : ℕ}
    (σ : (dprismComplex k).Simplex n) :
    simplexChar.{u} (uliftYonedaEquiv.symm (ULift.up σ)) ≫
      dprismCellProjection.{u} k = dprismCellMap.{u} σ := by
  have h := Presheaf.uliftYonedaAdjunction_homEquiv_app.{u}
    (Henry.SemiSSet.stdSimplex.{u}.leftKanExtension toTop.{u})
    (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit toTop.{u})
    (dprismCellProjection.{u} k)
    (Z := op (Henry.SemiSimplexCategory.mk n)) (z := ULift.up σ)
  have hEquiv :
      (realAdj.{u}.homEquiv (dprismCos.{u}.obj (Henry.SemiSimplexCategory.mk k))
        (toTop.{u}.obj (Henry.SemiSimplexCategory.mk k))) (dprismCellProjection.{u} k) =
        dprismCellSingular.{u} k := Equiv.apply_symm_apply _ _
  rw [hEquiv] at h
  have hs :
      (dprismCellSingular.{u} k).app (op (Henry.SemiSimplexCategory.mk n))
        (ULift.up σ) = ULift.up (dprismCellMap.{u} σ) := rfl
  rw [hs] at h
  have h' := congrArg ULift.down h.symm
  change (simplexChar.{u} (uliftYonedaEquiv.symm (ULift.up σ)) ≫
    dprismCellProjection.{u} k) = dprismCellMap.{u} σ at h'
  exact h'

private theorem simplexChar_comp_realizationMap {K K' : SemiSSet.{u}} {n : ℕ}
    (y : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶ K)
    (f : K ⟶ K') :
    simplexChar y ≫ realization.map f = simplexChar (y ≫ f) := by
  simp only [simplexChar, Functor.map_comp]
  exact Category.assoc _ _ _

private theorem sdSimplex_map_dprism {k n : ℕ} (s : (sdComplex k).Simplex n) :
    Complex.simplexMap.{u} (sdComplex k) s.1 s.2.1 s.2.2 ≫
      (sdToDprism k).toSemiSSet =
    Complex.simplexMap.{u} (dprismComplex k) s.1 s.2.1 s.2.2.1 := by
  apply uliftYonedaEquiv.injective
  apply congrArg ULift.up
  apply Subtype.ext
  rfl

theorem baryCell_on_simplex {k n : ℕ} (s : (sdComplex k).Simplex n) :
    simplexChar.{u} (Complex.simplexMap.{u} (sdComplex k) s.1 s.2.1 s.2.2) ≫
      realization.map (sdToDprism k).toSemiSSet ≫ dprismCellProjection.{u} k =
    dprismCellMap.{u} ⟨s.1, s.2.1, s.2.2.1⟩ := by
  change (simplexChar.{u} (Complex.simplexMap.{u} (sdComplex k) s.1 s.2.1 s.2.2) ≫
    realization.map (sdToDprism k).toSemiSSet) ≫ dprismCellProjection.{u} k = _
  rw [simplexChar_comp_realizationMap, sdSimplex_map_dprism]
  exact dprismCellProjection_simplex ⟨s.1, s.2.1, s.2.2.1⟩

end HomotopyHypothesis.Approximation.BarycentricCell
