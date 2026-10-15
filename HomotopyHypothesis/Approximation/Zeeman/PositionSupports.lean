import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.Carriers
import HomotopyHypothesis.Approximation.Zeeman.LeastCarrier
import HomotopyHypothesis.Approximation.Zeeman.LocalAffine
import HomotopyHypothesis.Approximation.Zeeman.Positions
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.TriangularAffine
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# Coordinate supports of relative barycentric positions

The nonzero coordinates of a subdivision vertex's position are precisely
the vertices of its original source face. A vertex of each source face
outside all preceding source faces therefore gives triangular coordinates.
-/

universe u

open CategoryTheory Opposite Convexity

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- The injective image of a standard barycentre has nonzero weights exactly in the image. -/
theorem map_barycenter_weights_ne_zero_iff {d m : ℕ}
    (θ : Fin (d + 1) → Fin (m + 1)) (hθ : Function.Injective θ) (q : Fin (m + 1)) :
    (StdSimplex.map (R := ℝ) θ
      (StdSimplex.barycenter (K := ℝ) (M := Fin (d + 1)))).weights q ≠ 0 ↔
        q ∈ Set.range θ := by
  rw [StdSimplex.weights_map]
  constructor
  · exact Finsupp.mem_range_of_mapDomain_ne_zero
  · rintro ⟨i, rfl⟩
    rw [Finsupp.mapDomain_apply_of_injective hθ, StdSimplex.weights_barycenter_apply,
      Fintype.card_fin]
    exact inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero d))

/-- A position's nonzero coordinates correspond exactly to raw vertices of its source face. -/
theorem relativeVertexPosition_weights_ne_zero_iff {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {m : ℕ}
    (y : K.obj (op (Henry.SemiSimplexCategory.mk m))) (v : RelativeVertex K L)
    (hv : RelativeVertex.CarriedBy v y) (q : Fin (m + 1)) :
    (relativeVertexPosition y v hv).weights q ≠ 0 ↔
      vertex y q ∈ Set.range (vertex v.sourceSimplex.2) := by
  have hinj : Function.Injective (carriedFaceMap y v hv).hom.toOrderHom :=
    SimplexCategory.mono_iff_injective.mp (carriedFaceMap y v hv).property
  rw [relativeVertexPosition, map_barycenter_weights_ne_zero_iff _ hinj]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    have hp := vertex_map (carriedFaceMap y v hv) y i
    rw [carriedFaceMap_spec] at hp
    exact hp.trans (congrArg (vertex y) hi)
  · rintro ⟨i, hi⟩
    refine ⟨i, vertex_injective hK y ?_⟩
    have hp := vertex_map (carriedFaceMap y v hv) y i
    rw [carriedFaceMap_spec] at hp
    exact hp.symm.trans hi

/-- A position has zero weight outside its source face's vertex support. -/
theorem relativeVertexPosition_weights_eq_zero_iff {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {m : ℕ}
    (y : K.obj (op (Henry.SemiSimplexCategory.mk m))) (v : RelativeVertex K L)
    (hv : RelativeVertex.CarriedBy v y) (q : Fin (m + 1)) :
    (relativeVertexPosition y v hv).weights q = 0 ↔
      vertex y q ∉ Set.range (vertex v.sourceSimplex.2) := by
  simpa only [ne_eq, not_not] using
    not_congr (relativeVertexPosition_weights_ne_zero_iff hK y v hv q)

/-- New source vertices supply the triangular coordinates needed for local affine injectivity. -/
theorem relativeLocalAffineMap_injective_of_new_source_vertices {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (hv : ∀ i, ∃ w : K.obj (op (Henry.SemiSimplexCategory.mk 0)),
      w ∈ Set.range (vertex (a.val i).sourceSimplex.2) ∧
        ∀ j, j < i → w ∉ Set.range (vertex (a.val j).sourceSimplex.2)) :
    Function.Injective (relativeLocalAffineMap hK a) := by
  let s := leastRelativeCarrier hK a
  let hs := (leastRelativeCarrier_spec hK a).1
  change Function.Injective (StdSimplex.affineMapMk (R := ℝ)
    (fun i => relativeVertexPosition s.2 (a.val i) (hs i)))
  apply affineMapMk_injective_of_triangular
  intro i
  obtain ⟨w, ⟨k, hk⟩, hprev⟩ := hv i
  let q := (carriedFaceMap s.2 (a.val i) (hs i)).hom.toOrderHom k
  have hq : vertex s.2 q = w := by
    have hp := vertex_map (carriedFaceMap s.2 (a.val i) (hs i)) s.2 k
    rw [carriedFaceMap_spec] at hp
    exact hp.symm.trans hk
  refine ⟨q, ?_, ?_⟩
  · apply (relativeVertexPosition_weights_ne_zero_iff hK s.2 (a.val i) (hs i) q).mpr
    rw [hq]
    exact ⟨k, hk⟩
  · intro j hji
    apply (relativeVertexPosition_weights_eq_zero_iff hK s.2 (a.val j) (hs j) q).mpr
    rw [hq]
    exact hprev j hji

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeVertexPosition_weights_ne_zero_iff
#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeLocalAffineMap_injective_of_new_source_vertices
