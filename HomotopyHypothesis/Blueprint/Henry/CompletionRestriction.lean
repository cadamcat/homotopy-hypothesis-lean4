import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.Topology
/-!
# Restriction between completions

For a morphism of cofibration categories `F : C ⥤ D`, precomposition with `F` sends presheaves on
`D` satisfying the completion conditions to presheaves on `C` satisfying them. This is the right
adjoint `F^*` of the Quillen pair of H Prop 2.4.15–2.4.16 (H:1355–1430).

The fundamental `∞`-groupoid functor of a cellular realization `G` factors as the restriction along
the inclusion of finite cell complexes into spaces, followed by `F^*` for the corestriction
`F : C ⥤ FinCell` of `G`; this factorization holds by definition.
-/

universe w v u v' u'

open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace HomotopyHypothesis.Henry

section Restriction

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  {D : Type u'} [Category.{v'} D] [CategoryWithCofibrations D]

/-- Restriction of completion presheaves along a morphism of cofibration categories,
`P ↦ P ∘ F^op` (H:993, H:1367). -/
def Completion.restriction (F : C ⥤ D) (hF : IsCofibrationMorphism F) :
    Completion.{w} D ⥤ Completion.{w} C :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ (Functor.whiskeringLeft _ _ _).obj F.op) (fun P => by
    refine ⟨fun I hI => ?_, fun A B X Q i f k j h hi => ?_⟩
    · obtain ⟨hFI⟩ := hF.map_initial hI
      exact P.property.1 hFI
    · exact P.property.2 _ _ _ _ (hF.map_isPushout i f k j h hi) (hF.map_cofibration i hi))

end Restriction

/-- The fundamental `∞`-groupoid functor of a cellular realization `G` is the restriction along the
inclusion of finite cell complexes into spaces followed by the restriction along the corestriction
of `G` to finite cell complexes. -/
theorem topRestriction_eq_comp {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
    [CategoryWithWeakEquivalences C] {G : C ⥤ TopCat.{w}} (hG : IsCellularRealization G)
    (hι : IsCellularRealization (ObjectProperty.ι Top.IsFiniteCellComplex.{w}))
    (hF : IsCofibrationMorphism hG.toFinCell) :
    topRestriction hG = topRestriction hι ⋙ Completion.restriction.{w} hG.toFinCell hF :=
  rfl

end HomotopyHypothesis.Henry
