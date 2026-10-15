import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.DerivedPrismTop.CellSingular
import HomotopyHypothesis.Approximation.DerivedPrismTop.LastVertex
import HomotopyHypothesis.Approximation.DerivedPrismProjection.DerivedEndIso
import HomotopyHypothesis.Approximation.DerivedPrismProjection.ProjectionTop
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Dprism
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.DprismCos
set_option maxHeartbeats 200000

/-!
# The straight-line homotopy on the derived cylinder
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.DerivedPrismHomotopy

open HomotopyHypothesis.Approximation.Topological HomotopyHypothesis.Approximation.DerivedPrismTop
  HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet
  Convexity

noncomputable def pathSpaceFunctor : TopCat.{u} ⥤ TopCat.{u} where
  obj X := TopCat.of C(unitInterval, X)
  map f := TopCat.ofHom ⟨fun p => f.hom.comp p, ContinuousMap.continuous_postcomp f.hom⟩
  map_id X := by
    ext f t
    rfl
  map_comp f g := by
    ext h t
    rfl

noncomputable def simplexStraightLine (k : ℕ) (t : unitInterval)
    (p q : Convexity.StdSimplex ℝ (Fin (k + 1))) :
    Convexity.StdSimplex ℝ (Fin (k + 1)) :=
  convexCombPair ((unitInterval.symm t : unitInterval) : ℝ) (t : ℝ)
    (unitInterval.nonneg (unitInterval.symm t)) (unitInterval.nonneg t) (by simp) p q

@[simp] private theorem simplexStraightLine_zero (k : ℕ)
    (p q : Convexity.StdSimplex ℝ (Fin (k + 1))) :
    simplexStraightLine k 0 p q = p := by
  simp [simplexStraightLine]

@[simp] private theorem simplexStraightLine_one (k : ℕ)
    (p q : Convexity.StdSimplex ℝ (Fin (k + 1))) :
    simplexStraightLine k 1 p q = q := by
  simp [simplexStraightLine]

set_option maxHeartbeats 200000 in
private theorem simplexStraightLine_continuous (k : ℕ) :
    Continuous (fun z : unitInterval ×
      (Convexity.StdSimplex ℝ (Fin (k + 1)) × Convexity.StdSimplex ℝ (Fin (k + 1))) =>
      simplexStraightLine k z.1 z.2.1 z.2.2) := by
  rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ
    (Fin (k + 1))).continuous_iff]
  apply continuous_pi
  intro i
  simp only [Function.comp_apply, simplexStraightLine,
    Convexity.StdSimplex.weights_convexCombPair]
  simp only [unitInterval.coe_symm_eq, Finsupp.coe_add, Finsupp.coe_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  fun_prop

attribute [local irreducible] simplexStraightLine in
/-- Straight-line interpolation of two continuous maps into a lifted standard simplex. -/
noncomputable def simplexStraightHomotopy {X : Type u} [TopologicalSpace X] (k : ℕ)
    (p q : C(X, ULift.{u} (Convexity.StdSimplex ℝ (Fin (k + 1))))) :
    ContinuousMap.Homotopy p q where
  toFun z := ULift.up (simplexStraightLine k z.1 (p z.2).down (q z.2).down)
  continuous_toFun := by
    have hp : Continuous (fun x : X => (p x).down) := continuous_uliftDown.comp p.continuous
    have hq : Continuous (fun x : X => (q x).down) := continuous_uliftDown.comp q.continuous
    have hF : Continuous (fun z : unitInterval × X => (z.1, ((p z.2).down, (q z.2).down))) :=
      continuous_fst.prodMk ((hp.comp continuous_snd).prodMk (hq.comp continuous_snd))
    exact continuous_uliftUp.comp ((simplexStraightLine_continuous k).comp hF)
  map_zero_left x := by simp only [simplexStraightLine_zero, ULift.up_down]
  map_one_left x := by simp only [simplexStraightLine_one, ULift.up_down]

/-- The straight-line homotopy on a standard derived-cylinder cell. -/
noncomputable def dprismCellStraightHomotopyStd (k : ℕ) :
    ContinuousMap.Homotopy (dprismLastVertexCellProjection.{u} k).hom
      (dprismCellProjection.{u} k).hom :=
  simplexStraightHomotopy k (dprismLastVertexCellProjection.{u} k).hom
    (dprismCellProjection.{u} k).hom

private theorem dprismCellStraightHomotopyStd_naturality {k l : ℕ}
    (θ : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk l)
    (t : unitInterval)
    (x : realization.{u}.obj (dprismCos.{u}.obj (Henry.SemiSimplexCategory.mk k))) :
    (dprismCellStraightHomotopyStd.{u} l).toContinuousMap (t,
        (realization.{u}.map (dprismCos.{u}.map θ)).hom x) =
      (toTop.{u}.map θ).hom ((dprismCellStraightHomotopyStd.{u} k).toContinuousMap (t, x)) := by
  have hp := congrArg (fun f => f.hom x)
    (dprismLastVertexCellProjection_naturality θ)
  have hq := congrArg (fun f => f.hom x) (dprismCellProjection_naturality θ)
  have hp' : ((dprismLastVertexCellProjection.{u} l).hom
        ((realization.{u}.map (dprismCos.{u}.map θ)).hom x)).down =
      Convexity.StdSimplex.map (R := ℝ) θ.1.toOrderHom
        ((dprismLastVertexCellProjection.{u} k).hom x).down :=
    congrArg ULift.down hp
  have hq' : ((dprismCellProjection.{u} l).hom
        ((realization.{u}.map (dprismCos.{u}.map θ)).hom x)).down =
      Convexity.StdSimplex.map (R := ℝ) θ.1.toOrderHom
        ((dprismCellProjection.{u} k).hom x).down :=
    congrArg ULift.down hq
  apply congrArg ULift.up
  change simplexStraightLine l t
      ((dprismLastVertexCellProjection.{u} l).hom
        ((realization.{u}.map (dprismCos.{u}.map θ)).hom x)).down
      ((dprismCellProjection.{u} l).hom
        ((realization.{u}.map (dprismCos.{u}.map θ)).hom x)).down =
    Convexity.StdSimplex.map (R := ℝ) θ.1.toOrderHom
      (simplexStraightLine k t
        ((dprismLastVertexCellProjection.{u} k).hom x).down
        ((dprismCellProjection.{u} k).hom x).down)
  rw [hp', hq', simplexStraightLine]
  exact (Convexity.StdSimplex.isAffineMap_map (R := ℝ) θ.1.toOrderHom).map_convexCombPair
    (unitInterval.nonneg (unitInterval.symm t)) (unitInterval.nonneg t) (by simp) _ _ |>.symm

/-- The straight-line paths on the cells form a natural transformation. -/
noncomputable def dprismCellStraightPath :
    dprismCos.{u} ⋙ realization.{u} ⟶ toTop.{u} ⋙ pathSpaceFunctor.{u} where
  app j := TopCat.ofHom <| ContinuousMap.curry
    ((dprismCellStraightHomotopyStd.{u} j.obj.len).toContinuousMap.comp ContinuousMap.prodSwap)
  naturality j j' θ := by
    cases j with
    | mk jObj =>
      cases jObj with
      | mk k =>
        cases j' with
        | mk j'Obj =>
          cases j'Obj with
          | mk l =>
            apply TopCat.hom_ext
            apply ContinuousMap.ext
            intro x
            apply ContinuousMap.ext
            intro t
            exact dprismCellStraightHomotopyStd_naturality.{u} θ t x

end HomotopyHypothesis.Approximation.DerivedPrismHomotopy
