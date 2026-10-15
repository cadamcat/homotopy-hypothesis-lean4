import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.CollarMap
import HomotopyHypothesis.Approximation.Zeeman.CollarNeighborhood
import HomotopyHypothesis.Approximation.Zeeman.CollarPreimage
import HomotopyHypothesis.Approximation.Zeeman.CollarStar
import HomotopyHypothesis.Approximation.Zeeman.CollarSubcomplex
import HomotopyHypothesis.Approximation.Zeeman.CollarVertices
import HomotopyHypothesis.Approximation.Zeeman.DistributionInjectivity
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.RestrictedAffinity
import HomotopyHypothesis.Approximation.Zeeman.RetainedFull
import HomotopyHypothesis.Approximation.Zeeman.RetainedRealization
import HomotopyHypothesis.Approximation.Zeeman.ScalarMesh
import HomotopyHypothesis.Approximation.Zeeman.SimplexSupport
import HomotopyHypothesis.Approximation.Zeeman.VertexDistributions
/-!
# Affinity of a map on the collar

A scalar function affine on target simplices remains affine under a
simplicial map. On a collar simplex, the collar vertex map factors through
a simplex of the full retained subcomplex. A continuous map simplicial
on that subcomplex therefore has affine target coordinates on the collar.
-/

universe u

open CategoryTheory Opposite Convexity

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- Simplicial maps preserve simplexwise scalar affinity under pullback. -/
theorem isSimplexwiseScalarAffine_comp_isSimplicial {W M : SemiSSet.{u}}
    (F : realization.obj W ⟶ realization.obj M) (hF : IsSimplicial F)
    (C : realization.obj M → ℝ) (hC : IsSimplexwiseScalarAffine C) :
    IsSimplexwiseScalarAffine (C ∘ F.hom) := by
  obtain ⟨φ, hφ⟩ := hF
  intro n y
  obtain ⟨m, x, v, _, he⟩ := hφ n (uliftYonedaEquiv.symm y)
  have hlocal : simplexScalarFunction (C ∘ F.hom) y =
      simplexScalarFunction C (uliftYonedaEquiv x) ∘ StdSimplex.map v := by
    funext t
    have hp := congrArg (fun e => e.hom (ULift.up t)) he
    change F.hom ((simplexChar (uliftYonedaEquiv.symm y)).hom (ULift.up t)) =
      (simplexChar x).hom (ULift.up (StdSimplex.map v t)) at hp
    change C (F.hom ((simplexChar (uliftYonedaEquiv.symm y)).hom (ULift.up t))) =
      C ((simplexChar (uliftYonedaEquiv.symm (uliftYonedaEquiv x))).hom
        (ULift.up (StdSimplex.map v t)))
    rw [Equiv.symm_apply_apply]
    exact congrArg C hp
  rw [hlocal]
  exact (hC m (uliftYonedaEquiv x)).comp (StdSimplex.affineMap v).isAffineMap

/-- A collar simplex maps by a vertex map into one simplex of the full retained subcomplex. -/
theorem exists_relativeCollarMap_simplex_factorization {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L : Subfunctor K) (hL : IsFullSubcomplex L) {n : ℕ}
    (q : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (hq : q ∈ (relativeCollarSubcomplex K L).obj (op (Henry.SemiSimplexCategory.mk n))) :
    ∃ (m : ℕ) (x : L.toFunctor.obj (op (Henry.SemiSimplexCategory.mk m)))
      (v : Fin (n + 1) → Fin (m + 1)),
      simplexChar (uliftYonedaEquiv.symm q) ≫ relativeCollarMap hK L =
        vertexMap v ≫ simplexChar (uliftYonedaEquiv.symm x) ≫ realization.map L.ι := by
  classical
  let b := StdSimplex.barycenter (K := ℝ) (M := Fin (n + 1))
  let z₀ := (simplexChar (uliftYonedaEquiv.symm q)).hom (ULift.up b)
  have hzN := simplexChar_mem_range_realization (relativeCollarSubcomplex K L) q hq (ULift.up b)
  have hzL : (relativeCollarMap hK L).hom z₀ ∈ Set.range (realization.map L.ι).hom :=
    (Set.ext_iff.mp (relativeCollarSubcomplex_range_eq_preimage hK L hL) z₀).mp hzN
  obtain ⟨z, hz⟩ := hzL
  obtain ⟨m, x, p, _, rfl⟩ := exists_simplexChar_nonzero_rep z
  have hpK : (simplexChar (uliftYonedaEquiv.symm x.val)).hom (ULift.up p) =
      (relativeCollarMap hK L).hom z₀ :=
    (congrArg (fun e => e.hom (ULift.up p)) (simplexChar_postcomp x L.ι)).symm.trans hz
  have hd : StdSimplex.map (vertex x.val) p =
      StdSimplex.map (fun i => relativeCollarVertex (q.val i)) b := by
    rw [← vertexDistributionMap_simplex_apply x.val p, hpK]
    exact relativeCollarMap_vertexDistribution_simplex hK q b
  have hb (i : Fin (n + 1)) : b.weights i ≠ 0 := by
    rw [StdSimplex.weights_barycenter_apply, Fintype.card_fin]
    exact inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
  have hi (i : Fin (n + 1)) : ∃ j, vertex x.val j = relativeCollarVertex (q.val i) := by
    have hne := stdSimplex_map_weights_ne_zero_of_ne_zero
      (fun j => relativeCollarVertex (q.val j)) b i (hb i)
    rw [← hd, StdSimplex.weights_map] at hne
    exact Finsupp.mem_range_of_mapDomain_ne_zero hne
  choose v hv using hi
  refine ⟨m, x, v, ?_⟩
  rw [simplexChar_postcomp]
  apply ConcreteCategory.hom_ext
  intro t
  apply vertexDistributionMap_injective hK
  change (vertexDistributionMap K).hom ((relativeCollarMap hK L).hom
      ((simplexChar (uliftYonedaEquiv.symm q)).hom t)) =
    (vertexDistributionMap K).hom ((simplexChar (uliftYonedaEquiv.symm x.val)).hom
      (ULift.up (StdSimplex.map v t.down)))
  exact (relativeCollarMap_vertexDistribution_simplex hK q t.down).trans
    (((congrArg (fun a => StdSimplex.map a t.down) (funext hv)).symm.trans
      (StdSimplex.map_comp t.down v (vertex x.val))).trans
        (vertexDistributionMap_simplex_apply x.val (StdSimplex.map v t.down)).symm)

/-- A map simplicial on full L has affine target coordinates after composing with the collar. -/
theorem isSimplexwiseScalarAffineOn_collar_comp {K M : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L : Subfunctor K) (hfull : IsFullSubcomplex L)
    (f : realization.obj K ⟶ realization.obj M)
    (hL : IsSimplicial (realization.map L.ι ≫ f))
    (a : M.obj (op (Henry.SemiSimplexCategory.mk 0))) :
    IsSimplexwiseScalarAffineOn (relativeCollarSubcomplex K L)
      (vertexCoordinate M a ∘ (relativeCollarMap hK L ≫ f).hom) := by
  have hscalar := isSimplexwiseScalarAffine_comp_isSimplicial
    (realization.map L.ι ≫ f) hL (vertexCoordinate M a)
    (vertexCoordinate_isSimplexwiseScalarAffine M a)
  intro n q hq
  obtain ⟨m, x, v, he⟩ := exists_relativeCollarMap_simplex_factorization hK L hfull q hq
  have hlocal : simplexScalarFunction
      (vertexCoordinate M a ∘ (relativeCollarMap hK L ≫ f).hom) q =
      simplexScalarFunction (vertexCoordinate M a ∘ (realization.map L.ι ≫ f).hom) x ∘
        StdSimplex.map v := by
    funext t
    have hp := congrArg (fun e => e.hom (ULift.up t)) he
    change (relativeCollarMap hK L).hom
        ((simplexChar (uliftYonedaEquiv.symm q)).hom (ULift.up t)) =
      (realization.map L.ι).hom ((simplexChar (uliftYonedaEquiv.symm x)).hom
        (ULift.up (StdSimplex.map v t))) at hp
    exact congrArg (fun z => vertexCoordinate M a (f.hom z)) hp
  rw [hlocal]
  exact (hscalar m x).comp (StdSimplex.affineMap v).isAffineMap

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.isSimplexwiseScalarAffine_comp_isSimplicial
#print axioms HomotopyHypothesis.Approximation.Zeeman.exists_relativeCollarMap_simplex_factorization
#print axioms HomotopyHypothesis.Approximation.Zeeman.isSimplexwiseScalarAffineOn_collar_comp
