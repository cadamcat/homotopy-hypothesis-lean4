import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.Complex
/-!
# Affine projections out of realizations of ordered simplicial complexes

A vertex map from an ordered simplicial complex to `[m]` induces, simplex by simplex, affine maps
into the topological simplex `|Δ^m|`; these glue to a map out of the realization (the realization is
left adjoint to the restricted Yoneda functor).
-/

universe u

open CategoryTheory Limits Opposite Convexity

namespace HomotopyHypothesis.Approximation.Topological

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

/-- The affine map between topological simplices induced by any vertex map. -/
noncomputable def affineMap {X Y : Henry.SemiSimplexCategory}
    (v : Fin (X.obj.len + 1) → Fin (Y.obj.len + 1)) : toTop.{u}.obj X ⟶ toTop.{u}.obj Y :=
  TopCat.uliftFunctor.{u}.map
    (TopCat.ofHom ⟨StdSimplex.map (R := ℝ) v, StdSimplex.continuous_map ℝ v⟩)

theorem toTop_map_eq_affineMap {X Y : Henry.SemiSimplexCategory} (θ : X ⟶ Y) :
    toTop.{u}.map θ = affineMap θ.1.toOrderHom := rfl

theorem affineMap_comp {X Y Z : Henry.SemiSimplexCategory}
    (v : Fin (X.obj.len + 1) → Fin (Y.obj.len + 1)) (w : Fin (Y.obj.len + 1) → Fin (Z.obj.len + 1)) :
    affineMap.{u} v ≫ affineMap w = affineMap (w ∘ v) := by
  ext x
  obtain ⟨x⟩ := x
  exact congrArg ULift.up
    (StdSimplex.map_map (R := ℝ) (show StdSimplex ℝ (Fin (X.obj.len + 1)) from x) v w)

variable {V : Type} [LinearOrder V]

/-- The natural transformation to the restricted Yoneda functor given by a vertex map. -/
noncomputable def Complex.affineNatTrans (K : Complex V) {m : ℕ} (π : V → Fin (m + 1)) :
    K.toSemiSSet.{u} ⟶
      (Presheaf.restrictedULiftYoneda.{u} toTop.{u}).obj
        (toTop.{u}.obj (Henry.SemiSimplexCategory.mk m)) where
  app k := TypeCat.ofHom fun σ => ULift.up
    (affineMap (X := k.unop) (Y := Henry.SemiSimplexCategory.mk m) (π ∘ σ.down.1))
  naturality k k' θ := by
    ext σ
    change ULift.up (affineMap.{u} (X := k'.unop) (Y := Henry.SemiSimplexCategory.mk m)
        (π ∘ σ.down.1 ∘ θ.unop.1.toOrderHom)) =
      ULift.up (toTop.map θ.unop ≫
        affineMap (X := k.unop) (Y := Henry.SemiSimplexCategory.mk m) (π ∘ σ.down.1))
    rw [toTop_map_eq_affineMap, affineMap_comp]
    rfl

/-- The affine projection `‖K‖ ⟶ |Δ^m|` of an ordered simplicial complex along a vertex map. -/
noncomputable def Complex.affineProj (K : Complex V) {m : ℕ} (π : V → Fin (m + 1)) :
    realization.obj K.toSemiSSet.{u} ⟶ toTop.{u}.obj (Henry.SemiSimplexCategory.mk m) :=
  ((Presheaf.uliftYonedaAdjunction.{u} (stdSimplex.{u}.leftKanExtension toTop.{u})
    (stdSimplex.{u}.leftKanExtensionUnit toTop.{u})).homEquiv _ _).symm
    (K.affineNatTrans π)

/-- The affine projection restricted to a simplex is the affine map of its vertex map. -/
theorem Complex.unit_map_affineProj (K : Complex V) {m : ℕ} (π : V → Fin (m + 1))
    {k : Henry.SemiSimplexCategory} (σ : K.toSemiSSet.{u}.obj (op k)) :
    (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app k ≫
        realization.map (uliftYonedaEquiv.symm σ) ≫ K.affineProj π =
      affineMap (X := k) (Y := Henry.SemiSimplexCategory.mk m) (π ∘ σ.down.1) := by
  have h := Presheaf.uliftYonedaAdjunction_homEquiv_app.{u}
    (stdSimplex.{u}.leftKanExtension toTop.{u}) (stdSimplex.{u}.leftKanExtensionUnit toTop.{u})
    (K.affineProj π) (Z := op k) σ
  rw [Complex.affineProj, Equiv.apply_symm_apply] at h
  exact (congrArg ULift.down h).symm

theorem Complex.affineProj_congr (K : Complex V) {m : ℕ} (π π' : V → Fin (m + 1))
    (h : ∀ (k : ℕ) (σ : K.Simplex k), π ∘ σ.1 = π' ∘ σ.1) :
    K.affineProj.{u} π = K.affineProj π' := by
  unfold Complex.affineProj
  congr 1
  ext k σ
  change ULift.up (affineMap (X := k.unop) (Y := Henry.SemiSimplexCategory.mk m)
      (π ∘ σ.down.1)) = ULift.up (affineMap (π' ∘ σ.down.1))
  rw [h _ σ.down]

theorem Complex.map_affineProj {V' : Type} [LinearOrder V'] {K : Complex V} {K' : Complex V'}
    (ψ : K.Hom K') {m : ℕ} (π : V' → Fin (m + 1)) :
    realization.map ψ.toSemiSSet.{u} ≫ K'.affineProj π = K.affineProj (π ∘ ψ.f) := by
  have e : ψ.toSemiSSet ≫ K'.affineNatTrans π = K.affineNatTrans (π ∘ ψ.f) := by
    ext k σ
    rfl
  unfold Complex.affineProj
  change (stdSimplex.{u}.leftKanExtension toTop.{u}).map ψ.toSemiSSet ≫ _ = _
  rw [← Adjunction.homEquiv_naturality_left_symm, e]

end HomotopyHypothesis.Approximation.Topological
