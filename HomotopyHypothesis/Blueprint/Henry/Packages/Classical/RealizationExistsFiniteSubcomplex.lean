import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.FiniteSubcomplex.SemiSkeleton

/-!
# `realization_exists_finite_subcomplex`

One declaration of `HomotopyHypothesis.Blueprint.Henry.Packages.Classical`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial

namespace HomotopyHypothesis.Henry.Packages

/-- **Compact support in realizations of semi-simplicial sets** (Hirschhorn, Props. 4.10–4.11, for
the skeletal cell structure of `‖X‖`). A map from a compact space to `‖X‖` factors through the
realization of a finite semi-simplicial subset of `X` (finitely many simplices in each dimension and
none above some dimension), and the realization of a semi-simplicial subset is injective. Used to
reduce relative simplicial approximation to a finite target. -/
theorem realization_exists_finite_subcomplex (X : SemiSSet.{u}) :
    (∀ Y : Subfunctor X, Function.Injective (SemiSSet.realization.{u}.map Y.ι).hom) ∧
    ∀ (K : TopCat.{u}) [CompactSpace K] (g : K ⟶ SemiSSet.realization.{u}.obj X),
      ∃ Y : Subfunctor X, (∀ n : ℕ, (Y.obj (Opposite.op (SemiSimplexCategory.mk n))).Finite) ∧
        (∃ N : ℕ, ∀ n : ℕ, N < n → Y.obj (Opposite.op (SemiSimplexCategory.mk n)) = ∅) ∧
        ∃ g' : K ⟶ SemiSSet.realization.{u}.obj Y.toFunctor,
          g' ≫ SemiSSet.realization.{u}.map Y.ι = g := _root_.HomotopyHypothesis.Henry.Packages.realization_exists_finite_subcomplex_proof ..
