import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.Carriers
import HomotopyHypothesis.Approximation.Zeeman.CollarMap
import HomotopyHypothesis.Approximation.Zeeman.CollarVertices
import HomotopyHypothesis.Approximation.Zeeman.FullSubcomplexRealization
import HomotopyHypothesis.Approximation.Zeeman.LeastCarrier
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.RetainedFull
import HomotopyHypothesis.Approximation.Zeeman.SimplexSupport
import HomotopyHypothesis.Approximation.Zeeman.VertexDistributions
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# The neighborhood mapped into the retained subcomplex

For a full retained subcomplex, the collar vertex map sends the union of
its open vertex stars into its realization. The proof computes the image
distribution directly from the chosen source vertices.
-/

universe u

open CategoryTheory Opposite Convexity

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- The collar image distribution is the distribution on the chosen source vertices. -/
theorem relativeCollarMap_vertexDistribution_simplex {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (p : StdSimplex ℝ (Fin (n + 1))) :
    (vertexDistributionMap K).hom ((relativeCollarMap hK L).hom
      ((simplexChar (uliftYonedaEquiv.symm a)).hom (ULift.up p))) =
        StdSimplex.map (fun i => relativeCollarVertex (a.val i)) p := by
  let s := leastRelativeCarrier hK a
  let f : Fin (n + 1) → Fin (s.1 + 1) := fun i => relativeCollarVertexIndex s.2 (a.val i)
    ((leastRelativeCarrier_spec hK a).1 i)
  have hc := congrArg (fun e => e.hom (ULift.up p)) (relativeCollarMap_simplex hK a)
  change (relativeCollarMap hK L).hom
      ((simplexChar (uliftYonedaEquiv.symm a)).hom (ULift.up p)) =
    (simplexChar (uliftYonedaEquiv.symm s.2)).hom (ULift.up (StdSimplex.map f p)) at hc
  rw [hc]
  exact (vertexDistributionMap_simplex_apply s.2 (StdSimplex.map f p)).trans
    ((StdSimplex.map_comp p f (vertex s.2)).symm.trans
      (congrArg (fun v => StdSimplex.map v p)
        (funext fun i => relativeCollarVertexIndex_spec s.2 (a.val i) _)))

/-- A derived simplex with a retained vertex maps into a full retained subcomplex. -/
theorem relativeCollarMap_mem_of_retainedEntry {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L : Subfunctor K) (hL : IsFullSubcomplex L) {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (ha : ∃ i v, a.val i = Sum.inl v) (p : StdSimplex ℝ (Fin (n + 1))) :
    (relativeCollarMap hK L).hom
      ((simplexChar (uliftYonedaEquiv.symm a)).hom (ULift.up p)) ∈
        Set.range (realization.map L.ι).hom := by
  apply mem_range_realization_of_vertexDistribution_support hK L hL
  intro v hv
  rw [relativeCollarMap_vertexDistribution_simplex, StdSimplex.weights_map] at hv
  obtain ⟨i, rfl⟩ := Finsupp.mem_range_of_mapDomain_ne_zero hv
  exact relativeCollarVertex_mem_of_retainedEntry a ha i

/-- The collar maps the retained open star into the realization of a full subcomplex. -/
theorem relativeCollarMap_mapsTo_openStar {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L : Subfunctor K) (hL : IsFullSubcomplex L) :
    Set.MapsTo (relativeCollarMap hK L).hom
      (subcomplexOpenStar (Subfunctor.range (relativeDerivedInclusion hK L)))
      (Set.range (realization.map L.ι).hom) := by
  intro z hz
  obtain ⟨n, a, p, _, rfl⟩ := exists_simplexChar_nonzero_rep z
  obtain ⟨v, hv⟩ := hz
  rw [vertexDistributionMap_simplex_apply, StdSimplex.weights_map] at hv
  obtain ⟨i, hi⟩ := Finsupp.mem_range_of_mapDomain_ne_zero hv
  have hiL : vertex a i ∈ (Subfunctor.range (relativeDerivedInclusion hK L)).obj
      (op (Henry.SemiSimplexCategory.mk 0)) := hi.symm ▸ v.property
  have ha := (relativeDerived_vertex_mem_range_iff hK L a i).mp hiL
  exact relativeCollarMap_mem_of_retainedEntry hK L hL a ⟨i, ha⟩ p

/-- The collar map takes an open neighborhood of the retained realization into it. -/
theorem relativeCollarMap_exists_openNeighborhood {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L : Subfunctor K) (hL : IsFullSubcomplex L) :
    ∃ U : Set (realization.obj (relativeDerived K L)), IsOpen U ∧
      Set.range (realization.map (relativeDerivedInclusion hK L)).hom ⊆ U ∧
        Set.MapsTo (relativeCollarMap hK L).hom U (Set.range (realization.map L.ι).hom) := by
  refine ⟨subcomplexOpenStar (Subfunctor.range (relativeDerivedInclusion hK L)),
    isOpen_subcomplexOpenStar _, ?_, relativeCollarMap_mapsTo_openStar hK L hL⟩
  intro z hz
  apply range_realization_subset_subcomplexOpenStar (Subfunctor.range (relativeDerivedInclusion hK L))
  obtain ⟨w, rfl⟩ := hz
  refine ⟨(realization.map (Subfunctor.toRange (relativeDerivedInclusion hK L))).hom w, ?_⟩
  have hc : realization.map (Subfunctor.toRange (relativeDerivedInclusion hK L)) ≫
      realization.map (Subfunctor.range (relativeDerivedInclusion hK L)).ι =
    realization.map (relativeDerivedInclusion hK L) := by
    rw [← CategoryTheory.Functor.map_comp, Subfunctor.toRange_ι]
  exact congrArg (fun e => e.hom w) hc

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeCollarMap_vertexDistribution_simplex
#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeCollarMap_exists_openNeighborhood
