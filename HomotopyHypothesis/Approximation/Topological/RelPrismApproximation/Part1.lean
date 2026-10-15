import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Cylinder.AnodyneCells.Proofs
import HomotopyHypothesis.Approximation.Topological.FoldedCylinder
import HomotopyHypothesis.Approximation.Topological.GlueStatements.ExistsHomotopyOfIsPushout

/-!
# `HomotopyHypothesis.Approximation.Topological.RelPrismApproximation`, part 1

Lines 28–54 of `HomotopyHypothesis.Approximation.Topological.RelPrismApproximation`, split so that the modules of the development form an acyclic import graph.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

theorem anodyne_comp' {A B C : SemiSSet.{u}} {f : A ⟶ B} {g : B ⟶ C} (hf : anodyne f)
    (hg : anodyne g) : anodyne (f ≫ g) := by
  unfold anodyne at hf hg ⊢
  induction hg generalizing A with
  | of g hg => exact MorphismProperty.multiplicativeClosure.comp_of f g hf hg
  | id _ => simpa using hf
  | comp_of g₁ g₂ hg₁ hg₂ ih =>
      rw [← Category.assoc]
      exact MorphismProperty.multiplicativeClosure.comp_of _ _ (ih hf) hg₂

/-- A homotopy on one side of a pushout of spaces, relative to `S`, and a homotopy on the other side
agreeing with it on the common part, glue to a homotopy relative to the image of `S`. -/
theorem homotopicRel_of_isPushout {A B C D T : TopCat.{u}} {fa : A ⟶ B} {ga : A ⟶ C}
    {h : B ⟶ D} {k : C ⟶ D} (sq : IsPushout fa ga h k) (u₀ u₁ : D ⟶ T)
    (HB : ContinuousMap.Homotopy (h ≫ u₀).hom (h ≫ u₁).hom) (S : Set C)
    (HC : ContinuousMap.HomotopyRel (k ≫ u₀).hom (k ≫ u₁).hom S)
    (hBC : ∀ (t : unitInterval) (a : A), HB (t, fa a) = HC (t, ga a)) :
    u₀.hom.HomotopicRel u₁.hom (k.hom '' S) := by
  obtain ⟨H, -, hHC⟩ := exists_homotopy_of_isPushout sq u₀ u₁ HB HC.toHomotopy hBC
  refine ⟨⟨H, ?_⟩⟩
  rintro t _ ⟨c, hc, rfl⟩
  have h₁ := hHC t c
  have h₂ := HC.eq_fst t hc
  simp only [ContinuousMap.HomotopyWith.coe_toHomotopy] at h₁
  simp only [TopCat.hom_comp, ContinuousMap.comp_apply] at h₂
  exact h₁.trans h₂
