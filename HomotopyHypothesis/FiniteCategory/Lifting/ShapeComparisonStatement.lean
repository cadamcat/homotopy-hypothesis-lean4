import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.FiniteCategory.Lifting.EndomorphismTheory
import HomotopyHypothesis.FiniteCategory.Lifting.Exactness
universe u v u₁

open CategoryTheory Limits HomotopicalAlgebra
open OAI.Grothendieck HomotopyHypothesis.Henry

namespace HomotopyHypothesis.FiniteCategory.Lifting

/-- Compatible isomorphisms on the globes extend to an isomorphism on all finite globular sums,
when the source diagram has cofibrant seams and the intervening functor preserves them. -/
def ShapeComparisonStatement {X : Type u} [Category.{v} X] [CategoryWithCofibrations X]
    {Y : Type u₁} [Category.{v} Y] [CategoryWithCofibrations Y]
    (R : ShapeInterpretation X) (S : ShapeInterpretation Y) (p : X ⥤ Y)
    (_hp : IsCofibrationMorphism p)
    (_hR : ∀ (T : Shape) (b : ℕ) (hb : b < T.1), cofibrations X (R.functor.map (T.seam hb)))
    (e : ∀ n, p.obj (R.functor.obj (Shape.globe n)) ≅ S.functor.obj (Shape.globe n))
    (_hs : ∀ n, p.map (R.functor.map (Shape.source n)) ≫ (e (n+1)).hom =
      (e n).hom ≫ S.functor.map (Shape.source n))
    (_ht : ∀ n, p.map (R.functor.map (Shape.target n)) ≫ (e (n+1)).hom =
      (e n).hom ≫ S.functor.map (Shape.target n)) : Prop :=
  ∃ α : R.functor ⋙ p ≅ S.functor, ∀ n, α.app (Shape.globe n) = e n

end HomotopyHypothesis.FiniteCategory.Lifting
