import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiModel
namespace HomotopyHypothesis.Cylinder.PreCylinderCategory

open CategoryTheory Limits HomotopicalAlgebra HomotopyHypothesis.Henry

universe v u

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C]

/-- 2-out-of-3 for weak equivalences, from 2-out-of-6 plus identities and composition. -/
theorem we_twoOutOfThree [IsCylinderCategory C] :
    (weakEquivalences C).HasTwoOutOfThreeProperty where
  comp_mem _ _ hf hg :=
    IsCylinderCategory.weakEquivalences_isMultiplicative.toIsStableUnderComposition.comp_mem _ _ hf hg
  of_postcomp f g hg hfg := by
    -- f≫g and g are WE → f is WE: use triple f, g, 𝟙
    have h2 : weakEquivalences C (g ≫ 𝟙 _) := by simpa using hg
    have := (IsCylinderCategory.twoOutOfSix (C := C) f g _ hfg h2)
    exact this.1
  of_precomp f g hf hfg := by
    -- f and f≫g are WE → g is WE: use triple 𝟙, f, g
    have h1 : weakEquivalences C (𝟙 _ ≫ f) := by simpa using hf
    have := (IsCylinderCategory.twoOutOfSix (C := C) _ f g h1 hfg)
    exact this.2.2.1

/-- Every identity is a weak equivalence. -/
theorem we_id [IsCylinderCategory C] (X : C) : weakEquivalences C (𝟙 X) :=
  IsCylinderCategory.isomorphisms_le_weakEquivalences _
    (MorphismProperty.isomorphisms.infer_property (f := 𝟙 X))

end HomotopyHypothesis.Cylinder.PreCylinderCategory
