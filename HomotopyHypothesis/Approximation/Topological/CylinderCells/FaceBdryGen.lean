import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.CylinderCells.ElOf
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DV
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDBoundaryComplex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.DcylDComplex
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.Inst57
import HomotopyHypothesis.Approximation.Topological.FoldedCylinder
import HomotopyHypothesis.Approximation.Topological.NormalForm.NF

/-!
# `faceBdryGen`

One declaration of `HomotopyHypothesis.Approximation.Topological.CylinderCells`, in its own module.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

variable {X W : SemiSSet.{u}} (φ : W ⟶ sharp X)

/-- The cylinder over a proper face `b` of `y` (given by a morphism of elements `f`), mapped into
the boundary of the cylinder of `y`. -/
noncomputable def faceBdryGen {n : ℕ} (y : W.obj (op (Henry.SemiSimplexCategory.mk n)))
    {b : W.Elements} (f : elOf y ⟶ b) (hk : elDim b ≠ n) :
    (dcylDComplex (elNF φ b).v).Hom (dcylDBoundaryComplex (elNF φ (elOf y)).v) where
  f := (dcylDElMap φ f).f
  strictMonoOn := (dcylDElMap φ f).strictMonoOn
  map_S A hA := by
    refine ⟨(dcylDElMap φ f).map_S A hA, Or.inr ?_⟩
    have hns : ¬ Function.Surjective (semiEmb (elFace f)) := by
      intro hs
      apply hk
      have h₁ := Fintype.card_le_of_surjective _ hs
      have h₂ := Fintype.card_le_of_injective _ (semiEmb (elFace f)).injective
      have e₁ : elDim (elOf y) = n := rfl
      simp only [Fintype.card_fin, e₁] at h₁ h₂
      omega
    simp only [Function.Surjective, not_forall, not_exists] at hns
    obtain ⟨i, hi⟩ := hns
    refine ⟨i, ?_, ?_⟩
    · intro hmem
      obtain ⟨a, -, ha⟩ := Finset.mem_image.1 hmem
      cases a with
      | top i' => exact hi i' (by simpa [dcylDElMap, dcylDMapHom, DV.mapV] using ha)
      | mid S => simp [dcylDElMap, dcylDMapHom, DV.mapV] at ha
      | bot c => simp [dcylDElMap, dcylDMapHom, DV.mapV] at ha
    · intro S hmem hiS
      obtain ⟨a, -, ha⟩ := Finset.mem_image.1 hmem
      cases a with
      | top i' => simp [dcylDElMap, dcylDMapHom, DV.mapV] at ha
      | mid S' =>
        simp only [dcylDElMap, dcylDMapHom, DV.mapV, DV.mid.injEq] at ha
        subst ha
        obtain ⟨i', -, hi'⟩ := Finset.mem_map.1 hiS
        exact hi i' hi'
      | bot c => simp [dcylDElMap, dcylDMapHom, DV.mapV] at ha
