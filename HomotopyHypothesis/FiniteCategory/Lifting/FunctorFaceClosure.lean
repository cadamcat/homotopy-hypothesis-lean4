import OAI.CategoryTheory.Globular.Model
universe u v

open CategoryTheory
open OAI.Grothendieck

namespace HomotopyHypothesis.FiniteCategory.Lifting

variable {X : Type u} [Category.{v} X]

/-- Proper globe faces map into any multiplicative class containing the adjacent source and
target maps. -/
theorem functorFace_mem (F : Globe ⥤ X) (P : MorphismProperty X) (hP : P.IsMultiplicative)
    (hs : ∀ n, P (F.map (Globe.source n))) (ht : ∀ n, P (F.map (Globe.target n)))
    {m n : ℕ} (h : m < n) (side : Bool) : P (F.map (Globe.face h side)) := by
  revert h
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro h
    by_cases e : m = n
    · subst m
      cases side
      · exact hs n
      · exact ht n
    · have hm : m < n := by omega
      have hface : Globe.face h side = Globe.face hm side ≫ Globe.source n := rfl
      rw [hface, F.map_comp]
      exact hP.comp_mem _ _ (ih hm) (hs n)

#print axioms functorFace_mem

end HomotopyHypothesis.FiniteCategory.Lifting
