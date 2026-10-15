import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.CompactSpaceOfIsFiniteCellComplex
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.ExistsFactorizationOfCompactSpace
import HomotopyHypothesis.Blueprint.Henry.Topology
/-!
# The restricted Hom functor and transfinite compositions of finite cell complexes

Compact support in a transfinite composition of relative finite cell complexes starting from a
finite cell complex (`exists_factorization_of_compactSpace`) says that the restriction
`R Y = Hom(−, Y)` to finite cell complexes takes the colimit of such a composition to a colimit of
the completion, computed objectwise: a map from a finite cell complex into the colimit factors
through a stage, and two maps into a stage agreeing in the colimit are equal.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra HomotopyHypothesis.Henry Opposite

namespace HomotopyHypothesis.FiniteCategory.UnitPresentation

variable {J : Type u} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
  {X Y : TopCat.{u}} {f : X ⟶ Y}

/-- Maps from a finite cell complex into a transfinite composition of relative finite cell
complexes factor through a stage. -/
theorem finiteCell_factor_through_stage
    (c : Top.relativeFiniteCellComplexes.TransfiniteCompositionOfShape J f)
    (hX : Top.IsFiniteCellComplex X) {K : TopCat.{u}} (hK : Top.IsFiniteCellComplex K)
    (g : K ⟶ Y) : ∃ (j : J) (g' : K ⟶ c.F.obj j), g' ≫ c.incl.app j = g := by
  haveI := Packages.compactSpace_of_isFiniteCellComplex hK
  exact (Packages.exists_factorization_of_compactSpace c hX).2 K g

/-- The stages of a transfinite composition of relative finite cell complexes are monomorphic in
the colimit. -/
theorem stage_hom_ext
    (c : Top.relativeFiniteCellComplexes.TransfiniteCompositionOfShape J f)
    (hX : Top.IsFiniteCellComplex X) {K : TopCat.{u}} {j : J} (g₁ g₂ : K ⟶ c.F.obj j)
    (h : g₁ ≫ c.incl.app j = g₂ ≫ c.incl.app j) : g₁ = g₂ := by
  ext p
  apply (Packages.exists_factorization_of_compactSpace c hX).1 j
  exact ConcreteCategory.congr_hom h p

variable (hι : IsCellularRealization (ObjectProperty.ι Top.IsFiniteCellComplex.{u}))

/-- The restriction to finite cell complexes takes the colimit of a transfinite composition of
relative finite cell complexes, starting from a finite cell complex, to a colimit of the
completion. -/
noncomputable def topRestriction_isColimit_transfinite
    (c : Top.relativeFiniteCellComplexes.TransfiniteCompositionOfShape J f)
    (hX : Top.IsFiniteCellComplex X) :
    IsColimit ((topRestriction hι).mapCocone (Cocone.mk Y c.incl)) := by
  apply isColimitOfReflects (ObjectProperty.ι (IsCompletionPresheaf.{u} FinCell.{u}))
  apply evaluationJointlyReflectsColimits
  intro d
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro g
    obtain ⟨j, g', hg'⟩ := finiteCell_factor_through_stage c hX d.unop.property
      (show d.unop.obj ⟶ Y from g)
    exact ⟨j, g', hg'.symm⟩
  · intro j g₁ g₂ h
    refine ⟨j, 𝟙 j, ?_⟩
    have h' : (show d.unop.obj ⟶ c.F.obj j from g₁) ≫ c.incl.app j =
        (show d.unop.obj ⟶ c.F.obj j from g₂) ≫ c.incl.app j := h
    have := stage_hom_ext c hX _ _ h'
    simp only [CategoryTheory.Functor.map_id]
    exact congrArg _ this

end HomotopyHypothesis.FiniteCategory.UnitPresentation
