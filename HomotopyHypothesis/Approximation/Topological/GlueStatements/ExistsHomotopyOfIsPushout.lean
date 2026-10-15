import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Gluing.Simplicial.Glue

/-!
# `exists_homotopy_of_isPushout`

One declaration of `HomotopyHypothesis.Approximation.Topological.GlueStatements`, in its own module so that it can import the module that proves it.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- Homotopies glue over a pushout of spaces. -/
theorem exists_homotopy_of_isPushout {A B C D T : TopCat.{u}} {f : A ⟶ B} {g : A ⟶ C}
    {h : B ⟶ D} {k : C ⟶ D} (sq : IsPushout f g h k) (u₀ u₁ : D ⟶ T)
    (HB : ContinuousMap.Homotopy (h ≫ u₀).hom (h ≫ u₁).hom)
    (HC : ContinuousMap.Homotopy (k ≫ u₀).hom (k ≫ u₁).hom)
    (hBC : ∀ (t : unitInterval) (a : A), HB (t, f a) = HC (t, g a)) :
    ∃ H : ContinuousMap.Homotopy u₀.hom u₁.hom,
      (∀ (t : unitInterval) (b : B), H (t, h b) = HB (t, b)) ∧
        ∀ (t : unitInterval) (c : C), H (t, k c) = HC (t, c) := by apply @_root_.HomotopyHypothesis.Gluing.Simplicial.exists_homotopy_of_isPushout_proof <;> assumption
