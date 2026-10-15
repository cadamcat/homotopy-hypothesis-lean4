import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.ExteriorIteration
import HomotopyHypothesis.Approximation.Zeeman.InducedSubdivision
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.SubdivisionIteration
/-!
# Covers by induced subcomplexes

Least-carrier membership makes induced relative subdivision preserve unions
and the whole complex. A cover by two subcomplexes therefore persists through
iteration. Every simplex incident to a vertex outside one member lies in
the other member.
-/

universe u

open CategoryTheory Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- Induced subdivision preserves unions. -/
theorem inducedRelativeSubdivision_sup {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L A B : Subfunctor K) :
    inducedRelativeSubdivision hK L (A ⊔ B) =
      inducedRelativeSubdivision hK L A ⊔ inducedRelativeSubdivision hK L B := by
  ext X a
  rfl

/-- The subdivision induced by the whole complex is the whole subdivision. -/
theorem inducedRelativeSubdivision_top {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L : Subfunctor K) :
    inducedRelativeSubdivision hK L ⊤ = ⊤ := by
  ext X a
  rfl

/-- Iterated induced subdivision preserves unions. -/
theorem iteratedInducedSubdivision_sup {K : SemiSSet.{u}}
    (hK : K.IsFinite) (hKs : K.IsSimplicialComplex) (L A B : Subfunctor K) (r : ℕ) :
    iteratedInducedSubdivision hK hKs L (A ⊔ B) r =
      iteratedInducedSubdivision hK hKs L A r ⊔ iteratedInducedSubdivision hK hKs L B r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change inducedRelativeSubdivision _ _ (iteratedInducedSubdivision hK hKs L (A ⊔ B) r) = _
    rw [ih, inducedRelativeSubdivision_sup]
    rfl

/-- The whole complex induces the whole complex at every iteration. -/
theorem iteratedInducedSubdivision_top {K : SemiSSet.{u}}
    (hK : K.IsFinite) (hKs : K.IsSimplicialComplex) (L : Subfunctor K) (r : ℕ) :
    iteratedInducedSubdivision hK hKs L ⊤ r = ⊤ := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change inducedRelativeSubdivision _ _ (iteratedInducedSubdivision hK hKs L ⊤ r) = _
    rw [ih, inducedRelativeSubdivision_top]
    rfl

/-- A cover by subcomplexes persists through the relative subdivision tower. -/
theorem iteratedInducedSubdivision_cover {K : SemiSSet.{u}}
    (hK : K.IsFinite) (hKs : K.IsSimplicialComplex) (L A B : Subfunctor K)
    (hAB : A ⊔ B = ⊤) (r : ℕ) :
    iteratedInducedSubdivision hK hKs L A r ⊔ iteratedInducedSubdivision hK hKs L B r = ⊤ := by
  rw [← iteratedInducedSubdivision_sup, hAB, iteratedInducedSubdivision_top]

/-- An incident simplex lies in the other member when a vertex misses one member of a cover. -/
theorem simplex_mem_of_vertex_not_mem_of_cover {W : SemiSSet.{u}}
    (A B : Subfunctor W) (hAB : A ⊔ B = ⊤) {n : ℕ}
    (x : W.obj (op (Henry.SemiSimplexCategory.mk n))) (i : Fin (n + 1))
    (hi : vertex x i ∉ B.obj (op (Henry.SemiSimplexCategory.mk 0))) :
    x ∈ A.obj (op (Henry.SemiSimplexCategory.mk n)) := by
  have hx : x ∈ (A ⊔ B).obj (op (Henry.SemiSimplexCategory.mk n)) := by
    rw [hAB]
    trivial
  rcases hx with hx | hx
  · exact hx
  · exact (hi (B.map (vertexInclusion i).op hx)).elim

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.iteratedInducedSubdivision_cover
#print axioms HomotopyHypothesis.Approximation.Zeeman.simplex_mem_of_vertex_not_mem_of_cover
