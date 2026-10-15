import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.DerivedPrismTop.CellSingular
import HomotopyHypothesis.Approximation.DerivedPrismTop.LanProjection
import HomotopyHypothesis.Approximation.DerivedPrismTop.LastVertex
import HomotopyHypothesis.Approximation.DerivedPrismTop.LastVertexLanProjection
import HomotopyHypothesis.Approximation.DerivedPrismTop.TopCellRestriction
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Dprism
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismCos
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismLan
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismLanTop
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismTopCos
/-!
# The top inclusion of the derived cylinder

The affine projection restricts to the identity on the top copy of every semi-simplicial set.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.DerivedPrismTop

open HomotopyHypothesis.Approximation.Topological HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet

private theorem id_isLeftKanExtension :
    (Functor.id SemiSSet.{u}).IsLeftKanExtension
      (Iso.refl (stdSimplex.{u} ⋙ Functor.id SemiSSet.{u})).hom := by
  exact Presheaf.isLeftKanExtension_of_preservesColimits.{u} (Functor.id SemiSSet.{u})
    (Iso.refl (stdSimplex.{u} ⋙ Functor.id SemiSSet.{u}))

/-- The composite of the top inclusion and the affine projection. -/
noncomputable def dprismLanProjectionTop : realization.{u} ⟶ realization.{u} where
  app V := realization.{u}.map (dprismLanTop.{u}.app V) ≫ dprismLanProjection.{u}.app V
  naturality V W φ := by
    have htop : φ ≫ dprismLanTop.{u}.app W =
        dprismLanTop.{u}.app V ≫ dprismLan.{u}.map φ := by
      simpa only [Functor.id_map] using dprismLanTop.{u}.naturality φ
    have hproj : realization.{u}.map (dprismLan.{u}.map φ) ≫
        dprismLanProjection.{u}.app W =
      dprismLanProjection.{u}.app V ≫ realization.{u}.map φ := by
      simpa only [Functor.comp_map] using dprismLanProjection.{u}.naturality φ
    calc
      realization.{u}.map φ ≫
          (realization.{u}.map (dprismLanTop.{u}.app W) ≫ dprismLanProjection.{u}.app W) =
        (realization.{u}.map φ ≫ realization.{u}.map (dprismLanTop.{u}.app W)) ≫
          dprismLanProjection.{u}.app W := by cat_disch
      _ = realization.{u}.map (φ ≫ dprismLanTop.{u}.app W) ≫
          dprismLanProjection.{u}.app W := by rw [← realization.map_comp]
      _ = realization.{u}.map (dprismLanTop.{u}.app V ≫ dprismLan.{u}.map φ) ≫
          dprismLanProjection.{u}.app W := by rw [htop]
      _ = (realization.{u}.map (dprismLanTop.{u}.app V) ≫
          realization.{u}.map (dprismLan.{u}.map φ)) ≫ dprismLanProjection.{u}.app W := by
            rw [realization.map_comp]
      _ = realization.{u}.map (dprismLanTop.{u}.app V) ≫
          (realization.{u}.map (dprismLan.{u}.map φ) ≫ dprismLanProjection.{u}.app W) := by
            cat_disch
      _ = realization.{u}.map (dprismLanTop.{u}.app V) ≫
          (dprismLanProjection.{u}.app V ≫ realization.{u}.map φ) := by rw [hproj]
      _ = (realization.{u}.map (dprismLanTop.{u}.app V) ≫
          dprismLanProjection.{u}.app V) ≫ realization.{u}.map φ := by cat_disch

private theorem dprismLanProjectionTop_unit_mk (k : ℕ) :
    (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
        (Henry.SemiSimplexCategory.mk k) ≫
      dprismLanProjectionTop.{u}.app
        (stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k)) =
    (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
        (Henry.SemiSimplexCategory.mk k) := by
  letI := id_isLeftKanExtension.{u}
  have htop := Functor.descOfIsLeftKanExtension_fac_app
    (F' := Functor.id SemiSSet.{u})
    (Iso.refl (stdSimplex.{u} ⋙ Functor.id SemiSSet.{u})).hom
    dprismLan.{u}
    (dprismTopCos.{u} ≫ stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u})
    (Henry.SemiSimplexCategory.mk k)
  have htop' : dprismLanTop.{u}.app
        (stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k)) =
      dprismTopCos.{u}.app (Henry.SemiSimplexCategory.mk k) ≫
        (stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}).app
          (Henry.SemiSimplexCategory.mk k) := by
    simpa only [dprismLanTop, Functor.id_obj, Functor.id_map, Iso.refl_hom,
      NatTrans.id_app, NatTrans.comp_app, Category.id_comp] using htop
  have hmap : realization.{u}.map (dprismLanTop.{u}.app
        (stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k))) =
      realization.{u}.map (dprismTopCos.{u}.app (Henry.SemiSimplexCategory.mk k)) ≫
        realization.{u}.map
          ((stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}).app
            (Henry.SemiSimplexCategory.mk k)) := by
    rw [htop', realization.map_comp]
  change (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
      (Henry.SemiSimplexCategory.mk k) ≫
    realization.{u}.map (dprismLanTop.{u}.app
      (stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k))) ≫
    dprismLanProjection.{u}.app
      (stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k)) = _
  rw [hmap]
  erw [Category.assoc, dprismLanProjection_cell.{u} k]
  exact dprismTop_cellProjection.{u} k

theorem dprismLanProjection_top :
    ∀ V : SemiSSet.{u},
      realization.{u}.map (dprismLanTop.{u}.app V) ≫ dprismLanProjection.{u}.app V = 𝟙 _ := by
  let γ : realization.{u} ⟶ realization.{u} := dprismLanProjectionTop.{u}
  have h : γ = 𝟙 _ := by
    let α := stdSimplex.{u}.leftKanExtensionUnit toTop.{u}
    letI : realization.{u}.IsLeftKanExtension α := by
      change (stdSimplex.{u}.leftKanExtension toTop.{u}).IsLeftKanExtension
        (stdSimplex.{u}.leftKanExtensionUnit toTop.{u})
      infer_instance
    let ψ : toTop.{u} ⟶ stdSimplex.{u} ⋙ realization.{u} :=
      α ≫ stdSimplex.{u}.whiskerLeft γ
    let ψid : toTop.{u} ⟶ stdSimplex.{u} ⋙ realization.{u} :=
      α ≫ stdSimplex.{u}.whiskerLeft (𝟙 realization.{u})
    have hψ : ψ = ψid := by
      apply NatTrans.ext
      funext j
      let j₀ := Henry.SemiSimplexCategory.mk j.obj.len
      let e : j₀ ⟶ j := eqToHom (semiSimplexMkEq j)
      have h₀ : ψ.app j₀ = ψid.app j₀ := by
        change (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app j₀ ≫
            γ.app (stdSimplex.{u}.obj j₀) =
          (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app j₀
        exact dprismLanProjectionTop_unit_mk.{u} j.obj.len
      have hψj := ψ.naturality e
      have hψidj := ψid.naturality e
      have hcancel : toTop.{u}.map e ≫ ψ.app j = toTop.{u}.map e ≫ ψid.app j := by
        calc
          toTop.{u}.map e ≫ ψ.app j =
              ψ.app j₀ ≫ (stdSimplex.{u} ⋙ realization.{u}).map e := hψj
          _ = ψid.app j₀ ≫ (stdSimplex.{u} ⋙ realization.{u}).map e := by rw [h₀]
          _ = toTop.{u}.map e ≫ ψid.app j := hψidj.symm
      exact (cancel_epi (toTop.{u}.map e)).1 hcancel
    have hψ' : α ≫ stdSimplex.{u}.whiskerLeft γ =
        α ≫ stdSimplex.{u}.whiskerLeft (𝟙 realization.{u}) := by
      simpa only [ψ, ψid] using hψ
    exact Functor.hom_ext_of_isLeftKanExtension (F' := realization.{u})
      (α := α) (G := realization.{u}) γ (𝟙 realization.{u}) hψ'
  intro V
  have hv := congrArg (fun f => f.app V) h
  simpa [γ, dprismLanProjectionTop] using hv

private theorem dprismLanLastVertexProjectionTop_unit_mk (k : ℕ) :
    (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
        (Henry.SemiSimplexCategory.mk k) ≫
      realization.{u}.map (dprismLanTop.{u}.app
        (stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k))) ≫
      dprismLanLastVertexProjection.{u}.app
        (stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k)) =
    (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
        (Henry.SemiSimplexCategory.mk k) := by
  letI := id_isLeftKanExtension.{u}
  have htop := Functor.descOfIsLeftKanExtension_fac_app
    (F' := Functor.id SemiSSet.{u})
    (Iso.refl (stdSimplex.{u} ⋙ Functor.id SemiSSet.{u})).hom
    dprismLan.{u}
    (dprismTopCos.{u} ≫ stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u})
    (Henry.SemiSimplexCategory.mk k)
  have htop' : dprismLanTop.{u}.app
        (stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k)) =
      dprismTopCos.{u}.app (Henry.SemiSimplexCategory.mk k) ≫
        (stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}).app
          (Henry.SemiSimplexCategory.mk k) := by
    simpa only [dprismLanTop, Functor.id_obj, Functor.id_map, Iso.refl_hom,
      NatTrans.id_app, NatTrans.comp_app, Category.id_comp] using htop
  have hmap : realization.{u}.map (dprismLanTop.{u}.app
        (stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k))) =
      realization.{u}.map (dprismTopCos.{u}.app (Henry.SemiSimplexCategory.mk k)) ≫
        realization.{u}.map
          ((stdSimplex.{u}.leftKanExtensionUnit dprismCos.{u}).app
            (Henry.SemiSimplexCategory.mk k)) := by
    rw [htop', realization.map_comp]
  change (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app
      (Henry.SemiSimplexCategory.mk k) ≫
    realization.{u}.map (dprismLanTop.{u}.app
      (stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k))) ≫
    dprismLanLastVertexProjection.{u}.app
      (stdSimplex.{u}.obj (Henry.SemiSimplexCategory.mk k)) = _
  rw [hmap]
  erw [Category.assoc, dprismLanLastVertexProjection_cell.{u} k]
  exact dprismTop_lastVertexCellProjection.{u} k


/-- The last-vertex projection also restricts to the identity on the top end. -/
noncomputable def dprismLanLastVertexProjectionTop : realization.{u} ⟶ realization.{u} where
  app V := realization.{u}.map (dprismLanTop.{u}.app V) ≫
    dprismLanLastVertexProjection.{u}.app V
  naturality V W φ := by
    have htop : φ ≫ dprismLanTop.{u}.app W =
        dprismLanTop.{u}.app V ≫ dprismLan.{u}.map φ := by
      simpa only [Functor.id_map] using dprismLanTop.{u}.naturality φ
    have hproj : realization.{u}.map (dprismLan.{u}.map φ) ≫
        dprismLanLastVertexProjection.{u}.app W =
      dprismLanLastVertexProjection.{u}.app V ≫ realization.{u}.map φ := by
      simpa only [Functor.comp_map] using dprismLanLastVertexProjection.{u}.naturality φ
    calc
      realization.{u}.map φ ≫
          (realization.{u}.map (dprismLanTop.{u}.app W) ≫
            dprismLanLastVertexProjection.{u}.app W) =
        (realization.{u}.map φ ≫ realization.{u}.map (dprismLanTop.{u}.app W)) ≫
          dprismLanLastVertexProjection.{u}.app W := by cat_disch
      _ = realization.{u}.map (φ ≫ dprismLanTop.{u}.app W) ≫
          dprismLanLastVertexProjection.{u}.app W := by rw [← realization.map_comp]
      _ = realization.{u}.map
            (dprismLanTop.{u}.app V ≫ dprismLan.{u}.map φ) ≫
          dprismLanLastVertexProjection.{u}.app W := by rw [htop]
      _ = (realization.{u}.map (dprismLanTop.{u}.app V) ≫
          realization.{u}.map (dprismLan.{u}.map φ)) ≫
            dprismLanLastVertexProjection.{u}.app W := by rw [realization.map_comp]
      _ = realization.{u}.map (dprismLanTop.{u}.app V) ≫
          (realization.{u}.map (dprismLan.{u}.map φ) ≫
            dprismLanLastVertexProjection.{u}.app W) := by cat_disch
      _ = realization.{u}.map (dprismLanTop.{u}.app V) ≫
          (dprismLanLastVertexProjection.{u}.app V ≫ realization.{u}.map φ) := by
            rw [hproj]
      _ = (realization.{u}.map (dprismLanTop.{u}.app V) ≫
          dprismLanLastVertexProjection.{u}.app V) ≫ realization.{u}.map φ := by cat_disch

theorem dprismLanLastVertexProjection_top :
    ∀ V : SemiSSet.{u},
      realization.{u}.map (dprismLanTop.{u}.app V) ≫
        dprismLanLastVertexProjection.{u}.app V = 𝟙 _ := by
  let γ := dprismLanLastVertexProjectionTop.{u}
  have h : γ = 𝟙 _ := by
    let α := stdSimplex.{u}.leftKanExtensionUnit toTop.{u}
    letI : realization.{u}.IsLeftKanExtension α := by
      change (stdSimplex.{u}.leftKanExtension toTop.{u}).IsLeftKanExtension
        (stdSimplex.{u}.leftKanExtensionUnit toTop.{u})
      infer_instance
    let ψ : toTop.{u} ⟶ stdSimplex.{u} ⋙ realization.{u} :=
      α ≫ stdSimplex.{u}.whiskerLeft γ
    let ψid : toTop.{u} ⟶ stdSimplex.{u} ⋙ realization.{u} :=
      α ≫ stdSimplex.{u}.whiskerLeft (𝟙 realization.{u})
    have hψ : ψ = ψid := by
      apply NatTrans.ext
      funext j
      let j₀ := Henry.SemiSimplexCategory.mk j.obj.len
      let e : j₀ ⟶ j := eqToHom (semiSimplexMkEq j)
      have h₀ : ψ.app j₀ = ψid.app j₀ := by
        change (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app j₀ ≫
            γ.app (stdSimplex.{u}.obj j₀) =
          (stdSimplex.{u}.leftKanExtensionUnit toTop.{u}).app j₀
        exact dprismLanLastVertexProjectionTop_unit_mk j.obj.len
      have hψj := ψ.naturality e
      have hψidj := ψid.naturality e
      have hcancel : toTop.{u}.map e ≫ ψ.app j = toTop.{u}.map e ≫ ψid.app j := by
        calc
          toTop.{u}.map e ≫ ψ.app j =
              ψ.app j₀ ≫ (stdSimplex.{u} ⋙ realization.{u}).map e := hψj
          _ = ψid.app j₀ ≫ (stdSimplex.{u} ⋙ realization.{u}).map e := by rw [h₀]
          _ = toTop.{u}.map e ≫ ψid.app j := hψidj.symm
      exact (cancel_epi (toTop.{u}.map e)).1 hcancel
    have hψ' : α ≫ stdSimplex.{u}.whiskerLeft γ =
        α ≫ stdSimplex.{u}.whiskerLeft (𝟙 realization.{u}) := by
      simpa only [ψ, ψid] using hψ
    exact Functor.hom_ext_of_isLeftKanExtension (F' := realization.{u})
      (α := α) (G := realization.{u}) γ (𝟙 realization.{u}) hψ'
  intro V
  have hv := congrArg (fun f => f.app V) h
  simpa [γ, dprismLanLastVertexProjectionTop] using hv


end HomotopyHypothesis.Approximation.DerivedPrismTop
