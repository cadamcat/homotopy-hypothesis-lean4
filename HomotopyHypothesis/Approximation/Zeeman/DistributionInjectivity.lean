import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.Faces
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.SimplexSupport
import HomotopyHypothesis.Approximation.Zeeman.VertexDistributions
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# Vertex distributions distinguish points of a simplicial complex

A simplex representative with nonzero weights has distribution support
equal to its raw vertex support. Equal distributions therefore identify
the representing simplices and their barycentric points.
-/

universe u v

open CategoryTheory Opposite Convexity

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- An injective image of a distribution with nonzero weights has exactly the given support. -/
theorem map_weights_ne_zero_iff {A : Type v} {B : Type u}
    (f : A → B) (hf : Function.Injective f)
    (p : StdSimplex ℝ A) (hp : ∀ i, p.weights i ≠ 0) (w : B) :
    (StdSimplex.map f p).weights w ≠ 0 ↔ w ∈ Set.range f := by
  rw [StdSimplex.weights_map]
  constructor
  · exact Finsupp.mem_range_of_mapDomain_ne_zero
  · rintro ⟨i, rfl⟩
    rw [Finsupp.mapDomain_apply_of_injective hf]
    exact hp i

/-- The vertex-distribution map of a simplicial complex is injective. -/
theorem vertexDistributionMap_injective {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex) :
    Function.Injective (vertexDistributionMap K).hom := by
  intro z w hzw
  obtain ⟨n, x, p, hp, rfl⟩ := exists_simplexChar_nonzero_rep z
  obtain ⟨m, y, q, hq, rfl⟩ := exists_simplexChar_nonzero_rep w
  rw [vertexDistributionMap_simplex_apply, vertexDistributionMap_simplex_apply] at hzw
  have hr : Set.range (vertex x) = Set.range (vertex y) := by
    ext v
    rw [← map_weights_ne_zero_iff (vertex x) (vertex_injective hK x) p hp,
      ← map_weights_ne_zero_iff (vertex y) (vertex_injective hK y) q hq, hzw]
  obtain ⟨θ, hθ⟩ := exists_faceMap_of_vertex_range_subset hK x y hr.subset
  obtain ⟨η, hη⟩ := exists_faceMap_of_vertex_range_subset hK y x hr.symm.subset
  have hnm := Fintype.card_le_of_injective θ.hom.toOrderHom
    (SimplexCategory.mono_iff_injective.mp θ.property)
  have hmn := Fintype.card_le_of_injective η.hom.toOrderHom
    (SimplexCategory.mono_iff_injective.mp η.property)
  simp only [Fintype.card_fin] at hnm hmn
  have hdim : n = m := by omega
  subst m
  have hxy := simplex_eq_of_vertex_range_eq hK hr
  clear hθ hη
  subst y
  have hpq : p = q := by
    apply StdSimplex.ext
    apply Finsupp.ext
    intro i
    have hi := congrArg (fun t => t.weights (vertex x i)) hzw
    simpa only [StdSimplex.weights_map,
      Finsupp.mapDomain_apply_of_injective (vertex_injective hK x)] using hi
  rw [hpq]

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.vertexDistributionMap_injective
