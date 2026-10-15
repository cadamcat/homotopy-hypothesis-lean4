import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.BarycentricPeelingStatement
import HomotopyHypothesis.Approximation.Zeeman.BoundarySupport
import HomotopyHypothesis.Approximation.Zeeman.Carriers
import HomotopyHypothesis.Approximation.Zeeman.DistributionInjectivity
import HomotopyHypothesis.Approximation.Zeeman.LocalAffine
import HomotopyHypothesis.Approximation.Zeeman.LocalEmbedding
import HomotopyHypothesis.Approximation.Zeeman.Positions
import HomotopyHypothesis.Approximation.Zeeman.RealizationTopology
import HomotopyHypothesis.Approximation.Zeeman.RelativeCones
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.RelativeDistributions
import HomotopyHypothesis.Approximation.Zeeman.RelativeRealization
import HomotopyHypothesis.Approximation.Zeeman.RetainedRealization
import HomotopyHypothesis.Approximation.Zeeman.VertexDistributions
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# Coverage by relative derived simplices

Barycentric peeling and induction on the original dimension cover each
simplex by relative derived simplices. The representatives remain in the
original carrier, so proper faces can be coned to an exterior barycentre.
-/

universe u

open CategoryTheory Opposite Convexity

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- A subdivision vertex carried by a proper face precedes the exterior carrier. -/
theorem precedes_exterior_of_carried_properFace {K : SemiSSet.{u}} {L : Subfunctor K}
    {n m : ℕ} (y : K.obj (op (Henry.SemiSimplexCategory.mk n)))
    (hy : y ∉ L.obj (op (Henry.SemiSimplexCategory.mk n)))
    (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk n) (hm : m < n)
    (v : RelativeVertex K L) (hv : RelativeVertex.CarriedBy v (K.map θ.op y)) :
    RelativeVertex.Precedes v (.inr ⟨⟨n, y⟩, hy⟩) := by
  have hc := carriedBy_of_face θ rfl hv
  cases v with
  | inl w => exact hc
  | inr s =>
    obtain ⟨η, _⟩ := hv
    have hd := Fintype.card_le_of_injective η.hom.toOrderHom
      (SimplexCategory.mono_iff_injective.mp η.property)
    simp only [Fintype.card_fin] at hd
    change s.val.1 < n ∧ _
    exact ⟨by omega, hc⟩

/-- The affine distribution of a cone is a convex combination of its apex and base. -/
theorem relativeDistributionAffineMap_cone {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (s : {s : Simplex K // s.2 ∉ L.obj (op (Henry.SemiSimplexCategory.mk s.1))})
    (hs : ∀ i, RelativeVertex.Precedes (a.val i) (.inr s))
    (t : StdSimplex ℝ (Fin (n + 1))) (c : ℝ) (hc : 0 ≤ c) (hc' : c ≤ 1) :
    relativeDistributionAffineMap (relativeCone a s hs)
      (convexCombPair c (1 - c) hc (sub_nonneg.mpr hc') (by ring)
        (StdSimplex.single (Fin.last (n + 1))) (StdSimplex.map Fin.castSucc t)) =
      convexCombPair c (1 - c) hc (sub_nonneg.mpr hc') (by ring)
        (relativeVertexDistribution (.inr s)) (relativeDistributionAffineMap a t) := by
  rw [(relativeDistributionAffineMap (relativeCone a s hs)).isAffineMap.map_convexCombPair]
  have hbase := DFunLike.congr_fun
    (relativeDistributionAffineMap_face (relativeCone a s hs) (initialFace (Nat.le_succ n))) t
  rw [relativeCone_prefix] at hbase
  change relativeDistributionAffineMap (relativeCone a s hs)
    (StdSimplex.map Fin.castSucc t) = relativeDistributionAffineMap a t at hbase
  rw [hbase]
  congr 1
  simp only [relativeDistributionAffineMap, StdSimplex.affineMapMk_single]
  exact congrArg relativeVertexDistribution
    (@Fin.snoc_last (n + 1) (fun _ => RelativeVertex K L) (Sum.inr s) a.val)

/-- The retained simplex has exactly its original vertex distribution. -/
theorem relativeDistributionAffineMap_retained {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L : Subfunctor K) {n : ℕ}
    (y : L.toFunctor.obj (op (Henry.SemiSimplexCategory.mk n)))
    (t : StdSimplex ℝ (Fin (n + 1))) :
    relativeDistributionAffineMap
      ((relativeDerivedInclusion hK L).app (op (Henry.SemiSimplexCategory.mk n)) y) t =
        StdSimplex.map (vertex y.val) t := by
  have h := relativeAffineMapInCarrier_distribution
    ((relativeDerivedInclusion hK L).app (op (Henry.SemiSimplexCategory.mk n)) y)
    ⟨n, y.val⟩ (retainedTuple_carried hK L y)
  rw [retainedAffineMap_eq_id, ConvexSpace.AffineMap.comp_id] at h
  exact (DFunLike.congr_fun h t).symm

/-- Barycentric peeling covers every original point by a carried relative derived simplex. -/
theorem exists_relativeDistribution_rep (H : BarycentricPeelingStatement)
    {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex) (L : Subfunctor K)
    {n : ℕ} (y : K.obj (op (Henry.SemiSimplexCategory.mk n)))
    (t : StdSimplex ℝ (Fin (n + 1))) :
    ∃ (k : ℕ) (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk k)))
      (p : StdSimplex ℝ (Fin (k + 1))),
      (∀ i, RelativeVertex.CarriedBy (a.val i) y) ∧
        relativeDistributionAffineMap a p = StdSimplex.map (vertex y) t := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hy : y ∈ L.obj (op (Henry.SemiSimplexCategory.mk n))
    · let x : L.toFunctor.obj (op (Henry.SemiSimplexCategory.mk n)) := ⟨y, hy⟩
      exact ⟨n, (relativeDerivedInclusion hK L).app _ x, t,
        retainedTuple_carried hK L x, relativeDistributionAffineMap_retained hK L x t⟩
    · let s : {s : Simplex K // s.2 ∉ L.obj (op (Henry.SemiSimplexCategory.mk s.1))} :=
        ⟨⟨n, y⟩, hy⟩
      rcases H n t with ht | ⟨c, q, i, hc, hc', hqi, ht⟩
      · refine ⟨0, relativeExteriorVertex s, StdSimplex.single 0, ?_, ?_⟩
        · intro j
          change ∃ θ : Henry.SemiSimplexCategory.mk n ⟶ Henry.SemiSimplexCategory.mk n,
            K.map θ.op y = y
          exact ⟨𝟙 _, by simp⟩
        · simp only [relativeDistributionAffineMap, StdSimplex.affineMapMk_single]
          exact congrArg (StdSimplex.map (vertex y)) ht.symm
      · obtain ⟨m, θ, p, hm, hp, _⟩ := exists_nonzero_proper_face q ⟨i, hqi⟩
        obtain ⟨k, a, r, ha, hr⟩ := ih m hm (K.map θ.op y) p
        have hs (j : Fin (k + 1)) : RelativeVertex.Precedes (a.val j) (.inr s) :=
          precedes_exterior_of_carried_properFace y hy θ hm (a.val j) (ha j)
        let z := relativeCone a s hs
        let w := convexCombPair c (1 - c) hc (sub_nonneg.mpr hc'.le) (by ring)
          (StdSimplex.single (Fin.last (k + 1))) (StdSimplex.map Fin.castSucc r)
        refine ⟨k + 1, z, w, ?_, ?_⟩
        · intro j
          induction j using Fin.lastCases with
          | last =>
            change RelativeVertex.CarriedBy
              (@Fin.snoc (k + 1) (fun _ => RelativeVertex K L) a.val
                (Sum.inr s) (Fin.last (k + 1))) y
            rw [Fin.snoc_last]
            change ∃ θ : Henry.SemiSimplexCategory.mk n ⟶ Henry.SemiSimplexCategory.mk n,
              K.map θ.op y = y
            exact ⟨𝟙 _, by simp⟩
          | cast j =>
            change RelativeVertex.CarriedBy
              (@Fin.snoc (k + 1) (fun _ => RelativeVertex K L) a.val
                (Sum.inr s) j.castSucc) y
            rw [Fin.snoc_castSucc]
            exact carriedBy_of_face θ rfl (ha j)
        · have hdist : StdSimplex.map (vertex (K.map θ.op y)) p =
              StdSimplex.map (vertex y) q := by
            rw [← hp, ← StdSimplex.map_comp]
            congr 1
            funext j
            exact vertex_map θ y j
          have hcomb : t = convexCombPair c (1 - c) hc
              (sub_nonneg.mpr hc'.le) (by ring)
              (StdSimplex.barycenter (K := ℝ) (M := Fin (n + 1))) q := by
            apply StdSimplex.ext
            apply Finsupp.ext
            intro j
            simpa only [StdSimplex.weights_convexCombPair, Finsupp.add_apply,
              Finsupp.smul_apply, smul_eq_mul] using ht j
          change relativeDistributionAffineMap (relativeCone a s hs)
            (convexCombPair c (1 - c) hc (sub_nonneg.mpr hc'.le) (by ring)
              (StdSimplex.single (Fin.last (k + 1))) (StdSimplex.map Fin.castSucc r)) = _
          rw [relativeDistributionAffineMap_cone a s hs r c hc hc'.le, hr, hdist, hcomb,
            (StdSimplex.isAffineMap_map ℝ (vertex y)).map_convexCombPair]
          rfl

/-- Coverage of distributions implies surjectivity of the relative realization map. -/
theorem relativeRealizationMap_surjective_of_peeling (H : BarycentricPeelingStatement)
    {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex) (L : Subfunctor K) :
    Function.Surjective (relativeRealizationMap hK L).hom := by
  intro z
  obtain ⟨n, y, t, rfl⟩ := exists_simplexChar_rep z
  change ULift.{u} (StdSimplex ℝ (Fin (n + 1))) at t
  rcases t with ⟨t⟩
  obtain ⟨k, a, p, _, hp⟩ := exists_relativeDistribution_rep H hK L
    (uliftYonedaEquiv y) t
  refine ⟨(simplexChar (uliftYonedaEquiv.symm a)).hom (ULift.up p), ?_⟩
  apply vertexDistributionMap_injective hK
  rw [relativeRealizationMap_distribution_simplex_apply, hp]
  have h := congrArg (fun f => f.hom (ULift.up t))
    (simplexChar_vertexDistributionMap (uliftYonedaEquiv y))
  simp only [Equiv.symm_apply_apply] at h
  exact h.symm

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.exists_relativeDistribution_rep
#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeRealizationMap_surjective_of_peeling
