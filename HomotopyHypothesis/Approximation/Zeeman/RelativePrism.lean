import Mathlib.CategoryTheory.Limits.Presheaf
import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.Prism
/-!
# Relative subdivision prisms

The boundary of a relative prism consists of the subdivided end and the
cylinder over the fixed subcomplex. Its projection to the subdivided end
identifies that cylinder with the fixed subcomplex. Pushing out the relative
collapse along this projection gives a pinched subdivision prism.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- A linear subdivision and a prism collapsing relative to its fixed lateral boundary. -/
structure RelativePrismData (K : SemiSSet.{u}) (L : Subfunctor K) where
  Y' : SemiSSet.{u}
  finite : Y'.IsFinite
  h : realization.obj Y' ≅ realization.obj K
  linear : ∀ (n : ℕ) (y' : stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶ Y'),
    ∃ (m : ℕ) (y : stdSimplex.obj (Henry.SemiSimplexCategory.mk m) ⟶ K)
      (e : toTop.obj (Henry.SemiSimplexCategory.mk n) ⟶
        toTop.obj (Henry.SemiSimplexCategory.mk m)),
      IsLinearEmbedding e ∧ simplexChar y' ≫ h.hom = e ≫ simplexChar y
  j : L.toFunctor ⟶ Y'
  mono_j : Mono j
  hj : realization.map j ≫ h.hom = realization.map L.ι
  /-- The subdivided end together with the fixed lateral boundary. -/
  B : SemiSSet.{u}
  C : SemiSSet.{u}
  b : B ⟶ C
  hb : anodyne b
  /-- The projection of the relative boundary to the subdivided end. -/
  t : B ⟶ Y'
  c₁ : K ⟶ C
  /-- The copy of the fixed subcomplex at the original end. -/
  a : L.toFunctor ⟶ B
  hab : a ≫ b = L.ι ≫ c₁
  hat : a ≫ t = j
  ρ : realization.obj C ⟶ realization.obj Y'
  hρ : realization.map b ≫ ρ = realization.map t
  hρ₁ : realization.map c₁ ≫ ρ = h.inv

/-- Pinch the lateral boundary of a relative prism to obtain a relative subdivision. -/
noncomputable def RelativePrismData.pinch {K : SemiSSet.{u}} {L : Subfunctor K}
    (D : RelativePrismData K L) : RelSubdivision K L := by
  letI : PreservesColimitsOfSize.{0, 0} realization.{u} := by
    change PreservesColimitsOfSize.{0, 0} (uliftYoneda.{u}.leftKanExtension toTop.{u})
    exact Presheaf.preservesColimitsOfSize_leftKanExtension.{u, 0, u, 0, 0, u + 1, 0}
      (C := Henry.SemiSimplexCategory) (ℰ := TopCat.{u}) toTop.{u}
  have H := realization.map_isPushout (IsPushout.of_hasPushout D.b D.t)
  let rho := H.desc D.ρ (𝟙 _) (by simpa only [Category.comp_id] using D.hρ)
  refine
    { Y' := D.Y'
      finite := D.finite
      h := D.h
      linear := D.linear
      j := D.j
      mono_j := D.mono_j
      hj := D.hj
      C := pushout D.b D.t
      c₀ := pushout.inr D.b D.t
      c₁ := D.c₁ ≫ pushout.inl D.b D.t
      hc := ?_
      anodyne_c₀ := anodyne_of_isPushout (IsPushout.of_hasPushout D.b D.t).flip D.hb
      ρ := rho
      hρ₀ := ?_
      hρ₁ := ?_ }
  · calc
      D.j ≫ pushout.inr D.b D.t = D.a ≫ D.t ≫ pushout.inr D.b D.t := by
        rw [← Category.assoc, D.hat]
      _ = D.a ≫ D.b ≫ pushout.inl D.b D.t := by rw [pushout.condition]
      _ = L.ι ≫ D.c₁ ≫ pushout.inl D.b D.t := by
        rw [← Category.assoc, D.hab, Category.assoc]
  · exact H.inr_desc _ _ _
  · change realization.map (D.c₁ ≫ pushout.inl D.b D.t) ≫ rho = D.h.inv
    rw [Functor.map_comp, Category.assoc]
    change realization.map D.c₁ ≫
      (realization.map (pushout.inl D.b D.t) ≫ H.desc D.ρ (𝟙 _) _) = D.h.inv
    rw [H.inl_desc, D.hρ₁]

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.RelativePrismData.pinch
