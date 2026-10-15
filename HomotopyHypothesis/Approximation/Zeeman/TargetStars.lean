import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.CoordinateMesh
import HomotopyHypothesis.Approximation.Zeeman.ExteriorIteration
import HomotopyHypothesis.Approximation.Zeeman.FullSubcomplexRealization
import HomotopyHypothesis.Approximation.Zeeman.LeastCarrier
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.SimplexSupport
import HomotopyHypothesis.Approximation.Zeeman.SubdivisionIteration
import HomotopyHypothesis.Approximation.Zeeman.VertexDistributions
/-!
# Vertex stars and their pullback cover

Nonzero vertex coordinates define the open vertex stars of a realization.
An intersection of such stars supplies a common simplex containing all the
specified vertices. The exterior subdivision tower eventually refines the
pullback of this cover along any continuous map.
-/

universe u v

open CategoryTheory Opposite Convexity

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- The open star of a raw vertex, described by its nonzero coordinate. -/
def vertexOpenStar (K : SemiSSet.{u})
    (w : K.obj (op (Henry.SemiSimplexCategory.mk 0))) : Set (realization.obj K) :=
  {z | ((vertexDistributionMap K).hom z).weights w ≠ 0}

/-- Each vertex star is open. -/
theorem isOpen_vertexOpenStar (K : SemiSSet.{u})
    (w : K.obj (op (Henry.SemiSimplexCategory.mk 0))) : IsOpen (vertexOpenStar K w) :=
  isOpen_ne.preimage (continuous_vertexDistribution_weight K w)

/-- Every realization point belongs to a vertex star. -/
theorem vertexOpenStar_cover (K : SemiSSet.{u}) (z : realization.obj K) :
    ∃ w, z ∈ vertexOpenStar K w := by
  obtain ⟨w, hw⟩ := ((vertexDistributionMap K).hom z).support_weights_nonempty
  exact ⟨w, Finsupp.mem_support_iff.mp hw⟩

/-- A simplex point is in a vertex star exactly when an incident weight is nonzero. -/
theorem mem_vertexOpenStar_simplex_iff {K : SemiSSet.{u}} {n : ℕ}
    (x : K.obj (op (Henry.SemiSimplexCategory.mk n)))
    (p : StdSimplex ℝ (Fin (n + 1)))
    (w : K.obj (op (Henry.SemiSimplexCategory.mk 0))) :
    (simplexChar (uliftYonedaEquiv.symm x)).hom (ULift.up p) ∈ vertexOpenStar K w ↔
      ∃ i, vertex x i = w ∧ p.weights i ≠ 0 := by
  classical
  change ((vertexDistributionMap K).hom
    ((simplexChar (uliftYonedaEquiv.symm x)).hom (ULift.up p))).weights w ≠ 0 ↔ _
  rw [vertexDistributionMap_simplex_apply, StdSimplex.weights_map,
    ← Finsupp.mem_support_iff, Finsupp.support_mapDomain_of_nonneg p.nonneg,
    Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, rfl, Finsupp.mem_support_iff.mp hi⟩
  · rintro ⟨i, rfl, hi⟩
    exact ⟨i, Finsupp.mem_support_iff.mpr hi, rfl⟩

/-- A realized vertex belongs to precisely its own vertex star. -/
theorem mem_vertexOpenStar_vertex_iff {K : SemiSSet.{u}}
    (w a : K.obj (op (Henry.SemiSimplexCategory.mk 0))) :
    (simplexChar (uliftYonedaEquiv.symm w)).hom (simplexVertex (n := 0) 0) ∈
      vertexOpenStar K a ↔ w = a := by
  refine (mem_vertexOpenStar_simplex_iff w (StdSimplex.single (0 : Fin 1)) a).trans ?_
  constructor
  · rintro ⟨i, hi, _⟩
    have hi0 : i = 0 := by
      apply Fin.ext
      omega
    simpa only [hi0, vertex_zero] using hi
  · intro h
    exact ⟨0, (vertex_zero w).trans h, by simp⟩

/-- Vertices whose open stars contain one point lie in a common simplex carrying that point. -/
theorem exists_simplex_of_vertexOpenStar_intersection {K : SemiSSet.{u}} {I : Type v}
    (q : I → K.obj (op (Henry.SemiSimplexCategory.mk 0))) (z : realization.obj K)
    (hz : ∀ i, z ∈ vertexOpenStar K (q i)) :
    ∃ (n : ℕ) (x : K.obj (op (Henry.SemiSimplexCategory.mk n)))
      (p : StdSimplex ℝ (Fin (n + 1))) (a : I → Fin (n + 1)),
      (∀ i, vertex x (a i) = q i) ∧ (∀ j, p.weights j ≠ 0) ∧
        (simplexChar (uliftYonedaEquiv.symm x)).hom (ULift.up p) = z := by
  classical
  obtain ⟨n, x, p, hp, rfl⟩ := exists_simplexChar_nonzero_rep z
  have hi (i : I) : ∃ j, vertex x j = q i := by
    obtain ⟨j, hj, _⟩ := (mem_vertexOpenStar_simplex_iff x p (q i)).mp (hz i)
    exact ⟨j, hj⟩
  choose a ha using hi
  exact ⟨n, x, p, a, ha, hp, rfl⟩

/-- Exterior closed stars eventually map into individual target vertex stars. -/
theorem exists_exterior_targetStar_refinement {K M : SemiSSet.{u}}
    [Fintype (K.obj (op (Henry.SemiSimplexCategory.mk 0)))]
    (hK : K.IsFinite) (hKs : K.IsSimplicialComplex) (L A : Subfunctor K)
    (hAL : A ⊓ L = ⊥) (D : ℕ)
    (hD : ∀ n, D < n → IsEmpty (K.obj (op (Henry.SemiSimplexCategory.mk n))))
    (F : realization.obj K ⟶ realization.obj M) :
    ∃ R : ℕ, ∀ r, R ≤ r →
      ∀ w : (derivedSubdivisionIterate hK hKs L r).Y'.obj
        (op (Henry.SemiSimplexCategory.mk 0)),
      w ∈ (iteratedInducedSubdivision hK hKs L A r).obj
        (op (Henry.SemiSimplexCategory.mk 0)) →
      ∃ a, ∀ n, ∀ q : (derivedSubdivisionIterate hK hKs L r).Y'.obj
        (op (Henry.SemiSimplexCategory.mk n)), ∀ j : Fin (n + 1), vertex q j = w →
        ∀ t : StdSimplex ℝ (Fin (n + 1)),
          F.hom ((derivedSubdivisionIterate hK hKs L r).h.hom.hom
            ((simplexChar (uliftYonedaEquiv.symm q)).hom (ULift.up t))) ∈ vertexOpenStar M a :=
  exists_exterior_closedStar_cover_refinement hK hKs L A hAL D hD
    (fun a => F.hom ⁻¹' vertexOpenStar M a)
    (fun a => (isOpen_vertexOpenStar M a).preimage F.hom.continuous)
    (fun z => vertexOpenStar_cover M (F.hom z))

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.exists_simplex_of_vertexOpenStar_intersection
#print axioms HomotopyHypothesis.Approximation.Zeeman.exists_exterior_targetStar_refinement
