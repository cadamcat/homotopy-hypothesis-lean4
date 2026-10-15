import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.DerivedPrismTop.CellCosimplicial
import HomotopyHypothesis.Approximation.DerivedPrismTop.DerivedPositions
import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Inst42
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismCos
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismHom
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.Map
import HomotopyHypothesis.Approximation.Topological.Projection
/-!
# Singular maps of derived-cylinder cells

The affine maps on the cells assemble into singular simplices and hence into maps of
realizations.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.DerivedPrismTop

open HomotopyHypothesis.Approximation.Topological HomotopyHypothesis.Henry.SemiSSet

/-- The affine cell maps, viewed as a map to the singular semi-simplicial set of a simplex. -/
noncomputable def dprismCellSingular (k : ℕ) :
    dprismCos.{u}.obj (Henry.SemiSimplexCategory.mk k) ⟶
    Sing (toTop.{u}.obj (Henry.SemiSimplexCategory.mk k)) where
  app j := TypeCat.ofHom fun σ => ULift.up (dprismCellMap σ.down)
  naturality j j' θ := by
    ext σ
    change ULift.up (dprismCellMap
        ⟨σ.down.1 ∘ θ.unop.1.toOrderHom,
          σ.down.2.1.comp (SemiSimplexCategory.strictMono θ.unop),
          (dprismComplex k).down (by
            intro a ha
            simp only [Finset.mem_image, Finset.mem_univ, true_and,
              Function.comp_apply] at ha ⊢
            obtain ⟨i, rfl⟩ := ha
            exact ⟨_, rfl⟩) σ.down.2.2⟩) =
      ULift.up (toTop.{u}.map θ.unop ≫ dprismCellMap σ.down)
    apply congrArg ULift.up
    exact dprismCellMap_face θ.unop σ.down _ rfl

/-- The singular cell maps commute with the cosimplicial face maps. -/
theorem dprismCellSingular_naturality {k l : ℕ}
    (θ : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk l) :
    dprismCos.{u}.map θ ≫ dprismCellSingular l =
      dprismCellSingular k ≫
        (Presheaf.restrictedULiftYoneda.{u} toTop.{u}).map (toTop.{u}.map θ) := by
  apply NatTrans.ext
  funext n
  ext σ
  let ht := SemiSimplexCategory.strictMono θ
  let s : (dprismComplex k).Simplex n.unop.obj.len := σ.down
  let τ : (dprismComplex l).Simplex n.unop.obj.len :=
    ((dprismHom ht).toSemiSSet.app (op n.unop)
      (ULift.up.{u, 0} s)).down
  have hτ : τ.1 = PV.map θ.1.toOrderHom ∘ s.1 := rfl
  change ULift.up (dprismCellMap τ) =
    ULift.up (dprismCellMap s ≫ toTop.{u}.map θ)
  apply congrArg ULift.up
  exact (dprismCellMap_postcompose θ.1.toOrderHom ht s τ hτ).symm

/-- The map on realizations adjoint to the singular cell maps. -/
noncomputable def dprismCellProjection (k : ℕ) :
    realization.obj (dprismCos.{u}.obj (Henry.SemiSimplexCategory.mk k)) ⟶
      toTop.{u}.obj (Henry.SemiSimplexCategory.mk k) :=
  ((realAdj.{u}.homEquiv (dprismCos.{u}.obj (Henry.SemiSimplexCategory.mk k)) _).symm
    (dprismCellSingular k))

/-- The adjoint maps on simplex realizations commute with face maps. -/
theorem dprismCellProjection_naturality {k l : ℕ}
    (θ : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk l) :
    realization.map (dprismCos.{u}.map θ) ≫ dprismCellProjection l =
      dprismCellProjection k ≫ toTop.{u}.map θ := by
  apply (realAdj.{u}.homEquiv _ _).injective
  change (realAdj.{u}.homEquiv (dprismCos.{u}.obj (Henry.SemiSimplexCategory.mk k))
      (toTop.{u}.obj (Henry.SemiSimplexCategory.mk l)))
      (realization.map (dprismCos.{u}.map θ) ≫
        (realAdj.{u}.homEquiv (dprismCos.{u}.obj (Henry.SemiSimplexCategory.mk l))
          (toTop.{u}.obj (Henry.SemiSimplexCategory.mk l))).symm (dprismCellSingular l)) =
    (realAdj.{u}.homEquiv (dprismCos.{u}.obj (Henry.SemiSimplexCategory.mk k))
      (toTop.{u}.obj (Henry.SemiSimplexCategory.mk l)))
      ((realAdj.{u}.homEquiv (dprismCos.{u}.obj (Henry.SemiSimplexCategory.mk k))
          (toTop.{u}.obj (Henry.SemiSimplexCategory.mk k))).symm (dprismCellSingular k) ≫
        toTop.{u}.map θ)
  delta realization
  rw [(realAdj.{u}).homEquiv_naturality_left,
    (realAdj.{u}).homEquiv_naturality_right,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact dprismCellSingular_naturality θ

/-- The canonical identification of a semi-simplex object with the standard object of its length.
-/
theorem semiSimplexMkEq (j : Henry.SemiSimplexCategory) :
    Henry.SemiSimplexCategory.mk j.obj.len = j := by
  apply WideSubcategory.ext
  exact SimplexCategory.mk_len j.obj

/-- The canonical equality acts by the identity when the object is already standard. -/
theorem semiSimplexMkEqToHom (k : ℕ) :
    eqToHom (semiSimplexMkEq (Henry.SemiSimplexCategory.mk k)) = 𝟙 _ := by
  apply WideSubcategory.hom_ext
  rfl

/-- The adjoint cell projection transported to an arbitrary semi-simplex object. -/
noncomputable def dprismCellProjectionAt (j : Henry.SemiSimplexCategory) :
    realization.obj (dprismCos.{u}.obj j) ⟶ toTop.{u}.obj j :=
  dprismCellProjection j.obj.len ≫
    toTop.{u}.map (eqToHom (semiSimplexMkEq j))

@[simp]
theorem dprismCellProjectionAt_mk (k : ℕ) :
    dprismCellProjectionAt (Henry.SemiSimplexCategory.mk k) = dprismCellProjection k := by
  unfold dprismCellProjectionAt
  simp only [SimplexCategory.len_mk, semiSimplexMkEqToHom]
  rw [HomotopyHypothesis.Henry.SemiSSet.toTop.map_id, Category.comp_id]

/-- The affine maps on derived simplex realizations form a natural transformation. -/
noncomputable def dprismCosProjection : dprismCos.{u} ⋙ realization ⟶ toTop.{u} where
  app j := dprismCellProjectionAt j
  naturality j j' θ := by
    cases j with
    | mk jObj =>
      cases jObj with
      | mk k =>
        cases j' with
        | mk j'Obj =>
          cases j'Obj with
          | mk l =>
            simpa using
              dprismCellProjection_naturality θ

end HomotopyHypothesis.Approximation.DerivedPrismTop
