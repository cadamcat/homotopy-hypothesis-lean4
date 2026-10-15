import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.DerivedPrismProjection.ProjectionTop
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismCos
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismLan
universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.DerivedPrismProjection

open HomotopyHypothesis.Approximation.Topological HomotopyHypothesis.Henry
  HomotopyHypothesis.Henry.SemiSSet

/-- Every simplex of the realized derived cylinder comes from one of its derived-cylinder cells. -/
theorem exists_dprismLan_simplex_cell {V : SemiSSet.{u}} {n : ℕ}
    (z : Henry.SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk n) ⟶
      dprismLan.{u}.obj V) :
    ∃ (c : CostructuredArrow Henry.SemiSSet.stdSimplex.{u} V)
      (z' : Henry.SemiSSet.stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk n) ⟶
        dprismCos.{u}.obj c.left),
      z = z' ≫ (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}).app c.left ≫
        dprismLan.{u}.map c.hom := by
  classical
  let P := CostructuredArrow.proj Henry.SemiSSet.stdSimplex.{u} V
  let S := P ⋙ dprismCos.{u}
  let ev := (CategoryTheory.evaluation (Henry.SemiSimplexCategoryᵒᵖ) (Type u)).obj
    (op (Henry.SemiSimplexCategory.mk n))
  let Sₙ := S ⋙ ev
  let E : Functor.LeftExtension Henry.SemiSSet.stdSimplex.{u} dprismCos.{u} :=
    Functor.LeftExtension.mk dprismLan.{u}
      (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u})
  have hEall : E.IsPointwiseLeftKanExtension :=
    Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension dprismLan.{u}
      (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u})
  let c := E.coconeAt V
  have hc : IsColimit c := hEall V
  let cₙ := ev.mapCocone c
  have hcₙ : IsColimit cₙ := isColimitOfPreserves ev hc
  obtain ⟨c', x, hx⟩ :=
    CategoryTheory.Limits.Concrete.isColimit_exists_rep Sₙ hcₙ (uliftYonedaEquiv z)
  have hleg : c.ι.app c' =
      (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}).app c'.left ≫
        dprismLan.{u}.map c'.hom := by
    rfl
  have hx' :
      ((Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}).app c'.left ≫
        dprismLan.{u}.map c'.hom).app (op (Henry.SemiSimplexCategory.mk n)) x =
          uliftYonedaEquiv z := by
    change ev.map (c.ι.app c') x = uliftYonedaEquiv z at hx
    rw [hleg] at hx
    exact hx
  refine ⟨c', uliftYonedaEquiv.symm x, ?_⟩
  apply uliftYonedaEquiv.injective
  rw [uliftYonedaEquiv_comp]
  exact hx'.symm

end HomotopyHypothesis.Approximation.DerivedPrismProjection
