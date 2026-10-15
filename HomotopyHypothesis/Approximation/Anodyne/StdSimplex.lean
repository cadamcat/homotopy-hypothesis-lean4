import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Anodyne

open HomotopyHypothesis.Henry

theorem stdSimplex_isFinite_proof (n : ℕ) :
    (SemiSSet.stdSimplex.{u}.obj (HomotopyHypothesis.Henry.SemiSimplexCategory.mk n)).IsFinite := by
  constructor
  · intro m
    change Finite (ULift (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m ⟶
      HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))
    apply Finite.of_injective (fun σ : ULift
        (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m ⟶
          HomotopyHypothesis.Henry.SemiSimplexCategory.mk n) => σ.down.hom)
    intro a b hab
    apply ULift.ext
    exact CategoryTheory.WideSubcategory.hom_ext
      (P := MorphismProperty.monomorphisms SimplexCategory) hab
  · refine ⟨n, ?_⟩
    intro m h
    change IsEmpty (ULift (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m ⟶
      HomotopyHypothesis.Henry.SemiSimplexCategory.mk n))
    refine ⟨?_⟩
    intro σ
    let f := σ.down
    have hle : m ≤ n := by
      simpa only [SimplexCategory.len_mk] using
        (@SimplexCategory.len_le_of_mono _ _ f.hom f.property)
    omega

#print axioms stdSimplex_isFinite_proof

end HomotopyHypothesis.Approximation.Anodyne
