import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.Carriers
import HomotopyHypothesis.Approximation.Zeeman.FiniteAverageContractionStatement
import HomotopyHypothesis.Approximation.Zeeman.InducedSubdivision
import HomotopyHypothesis.Approximation.Zeeman.LeastCarrier
import HomotopyHypothesis.Approximation.Zeeman.LocalAffine
import HomotopyHypothesis.Approximation.Zeeman.Positions
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.RelativeRealization
import HomotopyHypothesis.Approximation.Zeeman.ScalarContraction
import HomotopyHypothesis.Approximation.Zeeman.VertexDistributions
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# Scalar mesh bounds near an exterior subcomplex

A scalar function affine on each original simplex stays affine after
subdivision. For simplices meeting an induced subcomplex disjoint from
the retained one, its scalar diameter contracts by the uniform dimension
factor. Original vertex coordinates supply affine functions with initial
diameter at most one.
-/

universe u

open CategoryTheory Opposite Convexity

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- Pull a scalar function back along the characteristic map of a simplex. -/
noncomputable def simplexScalarFunction {K : SemiSSet.{u}} {n : ℕ}
    (F : realization.obj K → ℝ) (s : K.obj (op (Henry.SemiSimplexCategory.mk n))) :
    StdSimplex ℝ (Fin (n + 1)) → ℝ :=
  fun t => F ((simplexChar (uliftYonedaEquiv.symm s)).hom (ULift.up t))

/-- A scalar function on realization is affine on every simplex. -/
def IsSimplexwiseScalarAffine {K : SemiSSet.{u}} (F : realization.obj K → ℝ) : Prop :=
  ∀ (n : ℕ) (s : K.obj (op (Henry.SemiSimplexCategory.mk n))),
    IsAffineMap ℝ (simplexScalarFunction F s)

/-- Bundle the affine pullback along one characteristic map. -/
noncomputable def simplexScalarAffineMap {K : SemiSSet.{u}} {n : ℕ}
    (F : realization.obj K → ℝ) (hF : IsSimplexwiseScalarAffine F)
    (s : K.obj (op (Henry.SemiSimplexCategory.mk n))) :
    ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1))) ℝ where
  toFun := simplexScalarFunction F s
  isAffineMap_toFun := hF n s

/-- Linear simplex factorizations preserve simplexwise scalar affinity. -/
theorem isSimplexwiseScalarAffine_subdivision {K : SemiSSet.{u}} {L : Subfunctor K}
    (S : RelSubdivision K L) (F : realization.obj K → ℝ)
    (hF : IsSimplexwiseScalarAffine F) :
    IsSimplexwiseScalarAffine (F ∘ S.h.hom.hom) := by
  intro n s
  obtain ⟨m, x, e, he, hx⟩ := S.linear n (uliftYonedaEquiv.symm s)
  have hlocal : simplexScalarFunction (F ∘ S.h.hom.hom) s =
      simplexScalarFunction F (uliftYonedaEquiv x) ∘
        (fun t : StdSimplex ℝ (Fin (n + 1)) => (e.hom (ULift.up t)).down) := by
    funext t
    have hp := congrArg (fun c => c.hom (ULift.up t)) hx
    change S.h.hom.hom ((simplexChar (uliftYonedaEquiv.symm s)).hom (ULift.up t)) =
      (simplexChar x).hom (e.hom (ULift.up t)) at hp
    change F (S.h.hom.hom ((simplexChar (uliftYonedaEquiv.symm s)).hom (ULift.up t))) =
      F ((simplexChar (uliftYonedaEquiv.symm (uliftYonedaEquiv x))).hom
        (ULift.up (e.hom (ULift.up t)).down))
    rw [Equiv.symm_apply_apply, ULift.up_down]
    exact congrArg F hp
  rw [hlocal]
  exact (hF m (uliftYonedaEquiv x)).comp he.1

/-- A derived simplex's scalar pullback is computed in its least original carrier. -/
theorem simplexScalarFunction_relativeRealizationMap {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n : ℕ}
    (F : realization.obj K → ℝ)
    (q : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n))) :
    simplexScalarFunction (F ∘ (relativeRealizationMap hK L).hom) q =
      simplexScalarFunction F (leastRelativeCarrier hK q).2 ∘ relativeLocalAffineMap hK q := by
  funext t
  exact congrArg F (congrArg (fun c => c.hom (ULift.up t))
    (relativeRealizationMap_simplex hK q))

/-- Relative derived subdivision preserves simplexwise scalar affinity. -/
theorem isSimplexwiseScalarAffine_relativeRealizationMap {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L : Subfunctor K) (F : realization.obj K → ℝ)
    (hF : IsSimplexwiseScalarAffine F) :
    IsSimplexwiseScalarAffine (F ∘ (relativeRealizationMap hK L).hom) := by
  intro n q
  rw [simplexScalarFunction_relativeRealizationMap]
  exact (hF _ (leastRelativeCarrier hK q).2).comp (relativeLocalAffineMap hK q).isAffineMap

/-- A fixed original vertex coordinate on realization. -/
noncomputable def vertexCoordinate (K : SemiSSet.{u})
    (w : K.obj (op (Henry.SemiSimplexCategory.mk 0))) (z : realization.obj K) : ℝ :=
  ((vertexDistributionMap K).hom z).weights w

/-- Original vertex coordinates are affine on each simplex. -/
theorem vertexCoordinate_isSimplexwiseScalarAffine (K : SemiSSet.{u})
    (w : K.obj (op (Henry.SemiSimplexCategory.mk 0))) :
    IsSimplexwiseScalarAffine (vertexCoordinate K w) := by
  intro n s
  have he : simplexScalarFunction (vertexCoordinate K w) s =
      (fun t : StdSimplex ℝ (Fin (n + 1)) => (StdSimplex.map (vertex s) t).weights w) := by
    funext t
    exact congrArg (fun r => r.weights w) (vertexDistributionMap_simplex_apply s t)
  rw [he]
  exact (IsAffineMap.linearMap (Finsupp.lapply w :
    (K.obj (op (Henry.SemiSimplexCategory.mk 0)) →₀ ℝ) →ₗ[ℝ] ℝ)).comp
      ((StdSimplex.isAffineMap_weights ℝ _).comp
        (StdSimplex.affineMap (R := ℝ) (vertex s)).isAffineMap)

/-- A scalar diameter bound on every simplex having a vertex in a subcomplex. -/
def ScalarStarDiameterBound {K : SemiSSet.{u}} (A : Subfunctor K)
    (F : realization.obj K → ℝ) (c : ℝ) : Prop :=
  ∀ (n : ℕ) (s : K.obj (op (Henry.SemiSimplexCategory.mk n))),
    (∃ i, vertex s i ∈ A.obj (op (Henry.SemiSimplexCategory.mk 0))) →
      ∀ (x y : StdSimplex ℝ (Fin (n + 1))),
        |simplexScalarFunction F s x - simplexScalarFunction F s y| ≤ c

/-- Each original vertex coordinate starts with scalar diameter at most one. -/
theorem vertexCoordinate_starDiameterBound (K : SemiSSet.{u}) (A : Subfunctor K)
    (w : K.obj (op (Henry.SemiSimplexCategory.mk 0))) :
    ScalarStarDiameterBound A (vertexCoordinate K w) 1 := by
  intro n s _ x y
  have hbound (z : realization.obj K) : 0 ≤ vertexCoordinate K w z ∧
      vertexCoordinate K w z ≤ 1 :=
    ⟨((vertexDistributionMap K).hom z).nonneg w,
      ((vertexDistributionMap K).hom z).weights_apply_le_one w⟩
  have hx := hbound ((simplexChar (uliftYonedaEquiv.symm s)).hom (ULift.up x))
  have hy := hbound ((simplexChar (uliftYonedaEquiv.symm s)).hom (ULift.up y))
  change |vertexCoordinate K w _ - vertexCoordinate K w _| ≤ 1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A derived simplex meeting an induced subcomplex has a carrier meeting the original one. -/
theorem leastRelativeCarrier_meets_of_inducedStar {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L A : Subfunctor K) {n : ℕ}
    (q : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (hq : ∃ i, vertex q i ∈ (inducedRelativeSubdivision hK L A).obj
      (op (Henry.SemiSimplexCategory.mk 0))) :
    ∃ i, vertex (leastRelativeCarrier hK q).2 i ∈
      A.obj (op (Henry.SemiSimplexCategory.mk 0)) := by
  obtain ⟨j, hj⟩ := hq
  have hsource := (inducedRelativeSubdivision_vertex_mem_iff hK L A q j).mp hj
  let s := leastRelativeCarrier hK q
  let θ := carriedFaceMap s.2 (q.val j) ((leastRelativeCarrier_spec hK q).1 j)
  refine ⟨θ.hom.toOrderHom 0, ?_⟩
  have hvertex : vertex s.2 (θ.hom.toOrderHom 0) = vertex (q.val j).sourceSimplex.2 0 :=
    (vertex_map θ s.2 0).symm.trans
      (congrArg (fun z => vertex z 0) (carriedFaceMap_spec s.2 (q.val j)
        ((leastRelativeCarrier_spec hK q).1 j)))
  rw [hvertex]
  exact A.map (vertexInclusion 0).op hsource

/-- A dimension bound gives a uniform scalar contraction near the exterior subcomplex. -/
theorem scalarStarDiameterBound_relativeRealizationMap
    (havg : FiniteAverageContractionStatement) {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L A : Subfunctor K) (hAL : A ⊓ L = ⊥)
    (F : realization.obj K → ℝ) (hF : IsSimplexwiseScalarAffine F) (c : ℝ)
    (hc : ScalarStarDiameterBound A F c) (D : ℕ)
    (hD : ∀ n, D < n → IsEmpty (K.obj (op (Henry.SemiSimplexCategory.mk n)))) :
    ScalarStarDiameterBound (inducedRelativeSubdivision hK L A)
      (F ∘ (relativeRealizationMap hK L).hom) ((D : ℝ) / ((D : ℝ) + 1) * c) := by
  intro n q hq x y
  let s := leastRelativeCarrier hK q
  let G := simplexScalarAffineMap F hF s.2
  have hmeet := leastRelativeCarrier_meets_of_inducedStar hK L A q hq
  have hdim : s.1 ≤ D := by
    by_contra hn
    have : IsEmpty (K.obj (op (Henry.SemiSimplexCategory.mk s.1))) :=
      hD s.1 (lt_of_not_ge hn)
    exact isEmptyElim s.2
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ
    (fun i : Fin (s.1 + 1) => G (StdSimplex.single i)) ⟨0, Finset.mem_univ _⟩
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin (s.1 + 1) => G (StdSimplex.single i)) ⟨0, Finset.mem_univ _⟩
  have hG (k : Fin (s.1 + 1)) : G (StdSimplex.single i) ≤ G (StdSimplex.single k) ∧
      G (StdSimplex.single k) ≤ G (StdSimplex.single j) :=
    ⟨hi k (Finset.mem_univ _), hj k (Finset.mem_univ _)⟩
  have hdiam : G (StdSimplex.single j) - G (StdSimplex.single i) ≤ c :=
    (le_abs_self _).trans (hc s.1 s.2 hmeet (StdSimplex.single j) (StdSimplex.single i))
  have hnonneg : 0 ≤ G (StdSimplex.single j) - G (StdSimplex.single i) :=
    sub_nonneg.mpr (hG j).1
  have hcontraction := relativeAffineMapInCarrier_scalar_contraction havg hK q
    (inducedRelativeSubdivision_star_no_retainedEntry hK L A hAL q hq) s.2
    (leastRelativeCarrier_spec hK q).1 G (G (StdSimplex.single i))
    (G (StdSimplex.single j)) hG x y
  rw [simplexScalarFunction_relativeRealizationMap]
  change |G (relativeLocalAffineMap hK q x) - G (relativeLocalAffineMap hK q y)| ≤ _
  exact hcontraction.trans ((mul_le_mul_of_nonneg_right
    (dimensionContraction_mono hdim) hnonneg).trans
      (mul_le_mul_of_nonneg_left hdiam (div_nonneg (Nat.cast_nonneg D) (by positivity))))

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.isSimplexwiseScalarAffine_subdivision
#print axioms HomotopyHypothesis.Approximation.Zeeman.vertexCoordinate_isSimplexwiseScalarAffine
#print axioms HomotopyHypothesis.Approximation.Zeeman.scalarStarDiameterBound_relativeRealizationMap
