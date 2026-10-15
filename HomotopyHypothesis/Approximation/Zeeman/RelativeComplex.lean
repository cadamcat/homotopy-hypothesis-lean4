import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.RelativeDistributions
import HomotopyHypothesis.Approximation.Zeeman.RelativeHomeomorphism
import HomotopyHypothesis.Approximation.Zeeman.RelativeInjectivity
import HomotopyHypothesis.Approximation.Zeeman.RelativeRealization
import HomotopyHypothesis.Approximation.Zeeman.TriangularAffine
import HomotopyHypothesis.Approximation.Zeeman.VertexDistributions
/-!
# The relative derived object is a simplicial complex

Original vertex distributions distinguish the vertices of each derived
simplex. Equal sets of derived vertices give equal uniform mixtures, and
uniqueness of nonzero relative representatives identifies the simplices.
Thus relative derived subdivision can be iterated among finite complexes.
-/

universe u v

open CategoryTheory Opposite Convexity

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- Equal sets of distinct affine vertices have equal uniform mixtures. -/
theorem affineMapMk_barycenter_eq_of_range_eq {n : ℕ} {M : Type v}
    (p q : Fin (n + 1) → StdSimplex ℝ M) (hp : Function.Injective p)
    (hq : Function.Injective q) (h : Set.range p = Set.range q) :
    StdSimplex.affineMapMk (R := ℝ) p (StdSimplex.barycenter (K := ℝ)) =
      StdSimplex.affineMapMk (R := ℝ) q (StdSimplex.barycenter (K := ℝ)) := by
  classical
  have hex (i : Fin (n + 1)) : ∃ j, q j = p i := by
    apply (show p i ∈ Set.range q from h ▸ ⟨i, rfl⟩)
  let f : Fin (n + 1) → Fin (n + 1) := fun i => (hex i).choose
  have hf (i : Fin (n + 1)) : q (f i) = p i := (hex i).choose_spec
  have hfinj : Function.Injective f := by
    intro i j hij
    apply hp
    exact (hf i).symm.trans ((congrArg q hij).trans (hf j))
  have hfsurj : Function.Surjective f := by
    intro j
    obtain ⟨i, hi⟩ := (show q j ∈ Set.range p from h.symm ▸ ⟨j, rfl⟩)
    exact ⟨i, hq ((hf i).trans hi)⟩
  let e : Fin (n + 1) ≃ Fin (n + 1) := Equiv.ofBijective f ⟨hfinj, hfsurj⟩
  apply StdSimplex.ext
  apply Finsupp.ext
  intro w
  rw [affineMapMk_weights_apply, affineMapMk_weights_apply]
  simp only [StdSimplex.weights_barycenter_apply, Fintype.card_fin]
  calc
    (∑ i : Fin (n + 1), ((n + 1 : ℕ) : ℝ)⁻¹ * (p i).weights w) =
        ∑ i : Fin (n + 1), ((n + 1 : ℕ) : ℝ)⁻¹ * (q (e i)).weights w := by
          apply Finset.sum_congr rfl
          intro i _
          rw [show q (e i) = p i from hf i]
    _ = _ := e.sum_comp (fun i => ((n + 1 : ℕ) : ℝ)⁻¹ * (q i).weights w)

/-- The original distribution at a derived vertex is its source barycentre. -/
theorem relativeRealizationMap_distribution_vertex {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (i : Fin (n + 1)) :
    (vertexDistributionMap K).hom ((relativeRealizationMap hK L).hom
      ((simplexChar (uliftYonedaEquiv.symm a)).hom (simplexVertex i))) =
        relativeVertexDistribution (a.val i) := by
  change (vertexDistributionMap K).hom ((relativeRealizationMap hK L).hom
    ((simplexChar (uliftYonedaEquiv.symm a)).hom (ULift.up (StdSimplex.single i)))) = _
  erw [relativeRealizationMap_distribution_simplex_apply]
  exact StdSimplex.affineMapMk_single _ i

/-- The original distributions of the vertices of a derived simplex are distinct. -/
theorem relativeTuple_vertexDistribution_injective {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n))) :
    Function.Injective (fun i => relativeVertexDistribution (a.val i)) := by
  intro i j hij
  apply StdSimplex.single_injective (R := ℝ)
  apply relativeDistributionAffineMap_injective hK a
  simpa only [relativeDistributionAffineMap, StdSimplex.affineMapMk_single] using hij

/-- Relative derived subdivision of an ordered complex is an ordered complex. -/
theorem relativeDerived_isSimplicialComplex {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L : Subfunctor K) :
    (relativeDerived K L).IsSimplicialComplex := by
  let d := fun z => (vertexDistributionMap K).hom ((relativeRealizationMap hK L).hom z)
  have hd {n : ℕ} (σ : Henry.SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk n) ⟶
      relativeDerived K L) (i : Fin (n + 1)) :
      d ((simplexChar σ).hom (simplexVertex i)) =
        relativeVertexDistribution ((uliftYonedaEquiv σ).val i) := by
    simpa only [Equiv.symm_apply_apply] using
      relativeRealizationMap_distribution_vertex hK (uliftYonedaEquiv σ) i
  constructor
  · intro n σ i j hij
    apply relativeTuple_vertexDistribution_injective hK (uliftYonedaEquiv σ)
    simpa only [hd] using congrArg d hij
  · intro n σ τ hστ
    have hr : Set.range (fun i => relativeVertexDistribution ((uliftYonedaEquiv σ).val i)) =
        Set.range (fun i => relativeVertexDistribution ((uliftYonedaEquiv τ).val i)) := by
      ext z
      constructor
      · rintro ⟨i, rfl⟩
        obtain ⟨j, hj⟩ := (show (simplexChar σ).hom (simplexVertex i) ∈
          Set.range (fun j => (simplexChar τ).hom (simplexVertex j)) from hστ ▸ ⟨i, rfl⟩)
        exact ⟨j, (hd τ j).symm.trans ((congrArg d hj).trans (hd σ i))⟩
      · rintro ⟨i, rfl⟩
        obtain ⟨j, hj⟩ := (show (simplexChar τ).hom (simplexVertex i) ∈
          Set.range (fun j => (simplexChar σ).hom (simplexVertex j)) from hστ.symm ▸ ⟨i, rfl⟩)
        exact ⟨j, (hd σ j).symm.trans ((congrArg d hj).trans (hd τ i))⟩
    have hm := affineMapMk_barycenter_eq_of_range_eq _ _
      (relativeTuple_vertexDistribution_injective hK (uliftYonedaEquiv σ))
      (relativeTuple_vertexDistribution_injective hK (uliftYonedaEquiv τ)) hr
    have hn (i : Fin (n + 1)) : (StdSimplex.barycenter (K := ℝ)).weights i ≠ 0 := by
      rw [StdSimplex.weights_barycenter_apply, Fintype.card_fin]
      exact inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
    obtain ⟨_, he⟩ := relativeTuple_eq_of_distribution_eq hK
      (uliftYonedaEquiv σ) (uliftYonedaEquiv τ) _ _ hn hn hm
    exact uliftYonedaEquiv.injective (eq_of_heq he)

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.affineMapMk_barycenter_eq_of_range_eq
#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeDerived_isSimplicialComplex
