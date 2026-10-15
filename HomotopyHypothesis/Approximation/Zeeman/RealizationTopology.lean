import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.Topology.Category.TopCat.Limits.Basic
import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.RealizationMaps
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
/-!
# Simplex representatives and the topology of realization

The pointwise Kan extension defining realization is a colimit of its
topological simplices. Every point has a simplex representative, and a map
out of realization is continuous precisely when its restrictions to those
simplices are continuous.
For a finite semi-simplicial set the realization is compact, as the image
of the finite disjoint union of its compact topological simplices.
-/

universe u v

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- The characteristic maps form the pointwise realization cocone. -/
noncomputable def realizationCocone (K : SemiSSet.{u}) :
    Cocone (CostructuredArrow.proj Henry.SemiSSet.stdSimplex K ⋙ toTop.{u}) :=
  (Functor.LeftExtension.mk realization
    (Henry.SemiSSet.stdSimplex.{u}.leftKanExtensionUnit toTop.{u})).coconeAt K

/-- Realization is the colimit of its topological simplices. -/
noncomputable def realizationCocone_isColimit (K : SemiSSet.{u}) :
    IsColimit (realizationCocone K) :=
  Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit
    Henry.SemiSSet.stdSimplex.{u} toTop.{u} K

/-- Every realization point belongs to the image of a characteristic map. -/
theorem exists_simplexChar_rep {K : SemiSSet.{u}} (z : realization.obj K) :
    ∃ (n : ℕ) (y : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶ K)
      (t : toTop.obj (Henry.SemiSimplexCategory.mk n)), (simplexChar y).hom t = z := by
  obtain ⟨j, t, ht⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget TopCat) (realizationCocone_isColimit K)) z
  exact ⟨j.left.obj.len, j.hom, t, ht⟩

/-- Continuity out of realization can be checked on all characteristic maps. -/
theorem continuous_realization_iff {K : SemiSSet.{u}} {T : Type v}
    [TopologicalSpace T] (f : realization.obj K → T) :
    Continuous f ↔ ∀ (n : ℕ)
      (y : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶ K),
      Continuous (f ∘ (simplexChar y).hom) := by
  refine (TopCat.continuous_iff_of_isColimit (realizationCocone K)
    (realizationCocone_isColimit K) f).trans ?_
  constructor
  · intro h n y
    exact h (CostructuredArrow.mk y)
  · intro h j
    exact h j.left.obj.len j.hom

/-- The realization of a finite semi-simplicial set is compact. -/
theorem compactSpace_realization_of_isFinite {K : SemiSSet.{u}} (hK : K.IsFinite) :
    CompactSpace (realization.obj K) := by
  have : Finite (Simplex K) := simplex_finite hK
  have (s : Simplex K) :
      CompactSpace (toTop.{u}.obj (Henry.SemiSimplexCategory.mk s.1)) := by
    change CompactSpace (ULift.{u} (Convexity.StdSimplex ℝ (Fin (s.1 + 1))))
    infer_instance
  let D := Σ s : Simplex K, toTop.{u}.obj (Henry.SemiSimplexCategory.mk s.1)
  let q : D → realization.obj K := fun p =>
    (simplexChar (uliftYonedaEquiv.symm p.1.2)).hom p.2
  have hq : Continuous q := continuous_sigma fun s =>
    (simplexChar (uliftYonedaEquiv.symm s.2)).hom.continuous
  have hsurj : Function.Surjective q := by
    intro z
    obtain ⟨n, y, t, ht⟩ := exists_simplexChar_rep z
    refine ⟨⟨⟨n, uliftYonedaEquiv y⟩, t⟩, ?_⟩
    simpa only [q, Equiv.symm_apply_apply] using ht
  exact hsurj.compactSpace hq

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.exists_simplexChar_rep
#print axioms HomotopyHypothesis.Approximation.Zeeman.continuous_realization_iff
#print axioms HomotopyHypothesis.Approximation.Zeeman.compactSpace_realization_of_isFinite
