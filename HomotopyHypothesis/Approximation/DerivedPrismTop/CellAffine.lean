import Mathlib.Geometry.Convex.ConvexSpace.ModuleTopology
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Topological.Projection
/-!
# Affine maps from simplices by vertex positions

An assignment of a point of a target simplex to each vertex determines a continuous affine map
from the source simplex.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.DerivedPrismTop

open HomotopyHypothesis.Henry.SemiSSet

private theorem continuous_affineMapMk_fin (k m : ℕ)
    (p : Fin (k + 1) → Convexity.StdSimplex ℝ (Fin (m + 1))) :
    Continuous (Convexity.StdSimplex.affineMapMk (R := ℝ) p) := by
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (m + 1))).continuous_iff.mpr
  change Continuous (fun x : Convexity.StdSimplex ℝ (Fin (k + 1)) =>
    fun j => (Convexity.StdSimplex.affineMapMk (R := ℝ) p x).weights j)
  apply continuous_pi
  intro j
  change Continuous fun x : Convexity.StdSimplex ℝ (Fin (k + 1)) =>
    (x.iConvexComb p).weights j
  have hformula (x : Convexity.StdSimplex ℝ (Fin (k + 1))) :
      (x.iConvexComb p).weights j =
        ∑ i : Fin (k + 1), x.weights i * (p i).weights j := by
    rw [show (x.iConvexComb p).weights =
        x.weights.sum (fun i r => r • (p i).weights) from by
          simp [Convexity.iConvexComb, Convexity.StdSimplex.weights_sConvexComb,
            Finsupp.sum_mapDomain_index, add_smul]]
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [show (fun x : Convexity.StdSimplex ℝ (Fin (k + 1)) =>
      (x.iConvexComb p).weights j) =
      fun x => ∑ i : Fin (k + 1), x.weights i * (p i).weights j from funext hformula]
  fun_prop

/-- The affine map of topological simplices determined by its vertex positions. -/
noncomputable def simplexMapOfPoints (k m : ℕ)
    (p : Fin (k + 1) → Convexity.StdSimplex ℝ (Fin (m + 1))) :
    toTop.{u}.obj (HomotopyHypothesis.Henry.SemiSimplexCategory.mk k) ⟶
      toTop.{u}.obj (HomotopyHypothesis.Henry.SemiSimplexCategory.mk m) :=
  TopCat.uliftFunctor.{u}.map <| TopCat.ofHom ⟨
    Convexity.StdSimplex.affineMapMk (R := ℝ) p,
    continuous_affineMapMk_fin k m p⟩

/-- The affine map of vertex positions commutes with a face map when the positions are pulled back
along that face map. -/
theorem simplexMapOfPoints_naturality {k l m : ℕ}
    (θ : HomotopyHypothesis.Henry.SemiSimplexCategory.mk k ⟶
      HomotopyHypothesis.Henry.SemiSimplexCategory.mk l)
    (p : Fin (l + 1) → Convexity.StdSimplex ℝ (Fin (m + 1))) :
    toTop.{u}.map θ ≫ simplexMapOfPoints l m p =
      simplexMapOfPoints k m (p ∘ θ.1.toOrderHom) := by
  rw [HomotopyHypothesis.Approximation.Topological.toTop_map_eq_affineMap]
  ext x
  obtain ⟨x⟩ := x
  change ULift.up
      ((Convexity.StdSimplex.affineMapMk (R := ℝ) p)
        (Convexity.StdSimplex.map (R := ℝ) θ.1.toOrderHom x)) =
    ULift.up ((Convexity.StdSimplex.affineMapMk (R := ℝ)
      (p ∘ θ.1.toOrderHom)) x)
  apply congrArg ULift.up
  have hmap :
      (Convexity.StdSimplex.affineMapMk (R := ℝ) p).comp
          (Convexity.StdSimplex.affineMap (R := ℝ) θ.1.toOrderHom) =
        Convexity.StdSimplex.affineMapMk (R := ℝ) (p ∘ θ.1.toOrderHom) := by
    apply Convexity.StdSimplex.affineMap_ext
    intro i
    simp
  exact congrArg (fun f => f x) hmap

/-- Postcomposition by a simplex vertex map applies that map to each assigned point. -/
theorem simplexMapOfPoints_comp_affineMap {n k l : ℕ}
    (p : Fin (n + 1) → Convexity.StdSimplex ℝ (Fin (k + 1)))
    (t : Fin (k + 1) → Fin (l + 1)) :
    simplexMapOfPoints n k p ≫ HomotopyHypothesis.Approximation.Topological.affineMap t =
      simplexMapOfPoints n l (fun i => (p i).map t) := by
  ext x
  obtain ⟨x⟩ := x
  change ULift.up
      ((Convexity.StdSimplex.map (R := ℝ) t)
        ((Convexity.StdSimplex.affineMapMk (R := ℝ) p) x)) =
    ULift.up ((Convexity.StdSimplex.affineMapMk (R := ℝ)
      (fun i => (p i).map t)) x)
  apply congrArg ULift.up
  exact congrArg (fun f => f x)
    (Convexity.StdSimplex.comp_affineMapMk (Convexity.StdSimplex.affineMap (R := ℝ) t) p)

end HomotopyHypothesis.Approximation.DerivedPrismTop
