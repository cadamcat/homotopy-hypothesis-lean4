import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
open CategoryTheory HomotopicalAlgebra HomotopyHypothesis.Henry

universe u

namespace HomotopyHypothesis.Cylinder.SliceCategory

/-- The weak equivalences of a homotopy slice inherit the cylinder-category axioms. -/
theorem sliceObj_weakEquivalence_axioms {C : Type (u + 1)} [Category.{u} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [IsCylinderCategory C]
    (X : C) :
    MorphismProperty.isomorphisms (SliceObj X) ≤ weakEquivalences (SliceObj X) ∧
      (weakEquivalences (SliceObj X)).IsMultiplicative ∧
      TwoOutOfSix (SliceObj X) (weakEquivalences (SliceObj X)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A B f hf
    change weakEquivalences C f.v₀
    haveI : IsIso f := hf
    haveI : IsIso f.v₀ := by
      refine ⟨(inv f).v₀, ?_, ?_⟩
      · exact congrArg (fun g : A ⟶ A => g.v₀) (IsIso.hom_inv_id f)
      · exact congrArg (fun g : B ⟶ B => g.v₀) (IsIso.inv_hom_id f)
    exact IsCylinderCategory.isomorphisms_le_weakEquivalences (C := C) f.v₀
      (MorphismProperty.isomorphisms.infer_property f.v₀)
  · haveI : (weakEquivalences (SliceObj X)).ContainsIdentities := ⟨fun A => by
      exact IsCylinderCategory.isomorphisms_le_weakEquivalences (C := C) (𝟙 A.A₀)
        (MorphismProperty.isomorphisms.infer_property (𝟙 A.A₀))⟩
    haveI : (weakEquivalences (SliceObj X)).IsStableUnderComposition := ⟨fun f g hf hg => by
      change weakEquivalences C f.v₀ at hf
      change weakEquivalences C g.v₀ at hg
      change weakEquivalences C (f.v₀ ≫ g.v₀)
      exact (IsCylinderCategory.weakEquivalences_isMultiplicative (C := C)).comp_mem
        f.v₀ g.v₀ hf hg⟩
    exact ⟨⟩
  · intro A B D E f g h hfg hgh
    change weakEquivalences C (f.v₀ ≫ g.v₀) at hfg
    change weakEquivalences C (g.v₀ ≫ h.v₀) at hgh
    obtain ⟨hf, hg, hh, hfgh⟩ :=
      IsCylinderCategory.twoOutOfSix (C := C) f.v₀ g.v₀ h.v₀ hfg hgh
    exact ⟨hf, hg, hh, hfgh⟩

#print axioms HomotopyHypothesis.Cylinder.SliceCategory.sliceObj_weakEquivalence_axioms

end HomotopyHypothesis.Cylinder.SliceCategory
