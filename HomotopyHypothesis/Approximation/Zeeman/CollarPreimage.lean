import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Realization.ComplexTopology.ComplexRealizationTopology
import HomotopyHypothesis.Approximation.Zeeman.CollarMap
import HomotopyHypothesis.Approximation.Zeeman.CollarNeighborhood
import HomotopyHypothesis.Approximation.Zeeman.CollarStar
import HomotopyHypothesis.Approximation.Zeeman.CollarSubcomplex
import HomotopyHypothesis.Approximation.Zeeman.CollarVertices
import HomotopyHypothesis.Approximation.Zeeman.FullSubcomplexRealization
import HomotopyHypothesis.Approximation.Zeeman.RealizationTopology
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.RetainedFull
import HomotopyHypothesis.Approximation.Zeeman.RetainedRealization
import HomotopyHypothesis.Approximation.Zeeman.SimplexSupport
import HomotopyHypothesis.Approximation.Zeeman.VertexDistributions
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# Realization of the collar and exterior subcomplexes

The collar subcomplex realizes to the preimage of the full retained
subcomplex under the collar map. The collar and its exterior complement
cover the realization; the exterior complement misses the retained
realization. In a finite complex both subcomplex realizations are closed.
-/

universe u

open CategoryTheory Opposite Convexity

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- A point of a simplex belonging to a subcomplex lies in its realized image. -/
theorem simplexChar_mem_range_realization {W : SemiSSet.{u}} (A : Subfunctor W) {n : ℕ}
    (a : W.obj (op (Henry.SemiSimplexCategory.mk n)))
    (ha : a ∈ A.obj (op (Henry.SemiSimplexCategory.mk n)))
    (t : toTop.obj (Henry.SemiSimplexCategory.mk n)) :
    (simplexChar (uliftYonedaEquiv.symm a)).hom t ∈ Set.range (realization.map A.ι).hom := by
  refine ⟨(simplexChar (uliftYonedaEquiv.symm
    (⟨a, ha⟩ : A.toFunctor.obj (op (Henry.SemiSimplexCategory.mk n))))).hom t, ?_⟩
  exact congrArg (fun e => e.hom t)
    (simplexChar_postcomp
      (⟨a, ha⟩ : A.toFunctor.obj (op (Henry.SemiSimplexCategory.mk n))) A.ι)

/-- A covering by subcomplexes gives a covering of the realization. -/
theorem realization_ranges_cover_of_sup_eq_top {W : SemiSSet.{u}}
    (A B : Subfunctor W) (hAB : A ⊔ B = ⊤) :
    Set.range (realization.map A.ι).hom ∪ Set.range (realization.map B.ι).hom = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  obtain ⟨n, y, t, rfl⟩ := exists_simplexChar_rep z
  have ha : uliftYonedaEquiv y ∈ (A ⊔ B).obj (op (Henry.SemiSimplexCategory.mk n)) := by
    rw [hAB]
    trivial
  rcases ha with ha | hb
  · exact Or.inl (by simpa only [Equiv.symm_apply_apply] using
      simplexChar_mem_range_realization A (uliftYonedaEquiv y) ha t)
  · exact Or.inr (by simpa only [Equiv.symm_apply_apply] using
      simplexChar_mem_range_realization B (uliftYonedaEquiv y) hb t)

/-- Disjoint subcomplexes have disjoint realized images. -/
theorem realization_ranges_disjoint_of_inf_eq_bot {W : SemiSSet.{u}}
    (A B : Subfunctor W) (hAB : A ⊓ B = ⊥) :
    Disjoint (Set.range (realization.map A.ι).hom) (Set.range (realization.map B.ι).hom) := by
  apply Set.disjoint_left.mpr
  intro z ha hb
  obtain ⟨v, hv⟩ := ((vertexDistributionMap W).hom z).support_weights_nonempty
  have hne := Finsupp.mem_support_iff.mp hv
  have hmem : v ∈ (A ⊓ B).obj (op (Henry.SemiSimplexCategory.mk 0)) :=
    ⟨vertexDistribution_support_subset_of_mem_range A ha v hne,
      vertexDistribution_support_subset_of_mem_range B hb v hne⟩
  rw [hAB] at hmem
  exact hmem

/-- The realized image of a subcomplex of a finite complex is closed. -/
theorem isClosed_realization_range {W : SemiSSet.{u}} (hW : W.IsFinite)
    (hWs : W.IsSimplicialComplex) (A : Subfunctor W) :
    IsClosed (Set.range (realization.map A.ι).hom) := by
  letI : CompactSpace (realization.obj A.toFunctor) :=
    compactSpace_realization_of_isFinite (subfunctor_isFinite hW A)
  letI : T2Space (realization.obj W) :=
    (Realization.ComplexTopology.complexRealizationTopologyStatement_proof W hW hWs).1
  exact (isCompact_range (realization.map A.ι).hom.continuous).isClosed

/-- The collar subcomplex realizes to the collar map's preimage of full L. -/
theorem relativeCollarSubcomplex_range_eq_preimage {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L : Subfunctor K) (hL : IsFullSubcomplex L) :
    Set.range (realization.map (relativeCollarSubcomplex K L).ι).hom =
      (relativeCollarMap hK L).hom ⁻¹' Set.range (realization.map L.ι).hom := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨n, x, p, _, rfl⟩ := exists_simplexChar_nonzero_rep w
    have hinc := congrArg (fun e => e.hom (ULift.up p))
      (simplexChar_postcomp x (relativeCollarSubcomplex K L).ι)
    change (realization.map (relativeCollarSubcomplex K L).ι).hom
        ((simplexChar (uliftYonedaEquiv.symm x)).hom (ULift.up p)) =
      (simplexChar (uliftYonedaEquiv.symm x.val)).hom (ULift.up p) at hinc
    change (relativeCollarMap hK L).hom _ ∈ Set.range (realization.map L.ι).hom
    rw [hinc]
    apply mem_range_realization_of_vertexDistribution_support hK L hL
    intro v hv
    rw [relativeCollarMap_vertexDistribution_simplex, StdSimplex.weights_map] at hv
    obtain ⟨i, rfl⟩ := Finsupp.mem_range_of_mapDomain_ne_zero hv
    exact x.property i
  · intro hz
    obtain ⟨n, a, p, hp, rfl⟩ := exists_simplexChar_nonzero_rep z
    have ha : a ∈ (relativeCollarSubcomplex K L).obj (op (Henry.SemiSimplexCategory.mk n)) := by
      intro i
      apply vertexDistribution_support_subset_of_mem_range L hz
      rw [relativeCollarMap_vertexDistribution_simplex]
      exact stdSimplex_map_weights_ne_zero_of_ne_zero _ p i (hp i)
    exact simplexChar_mem_range_realization (relativeCollarSubcomplex K L) a ha (ULift.up p)

/-- The collar and exterior subcomplexes cover the derived realization. -/
theorem relativeCollarSubcomplexes_realization_cover {K : SemiSSet.{u}} (L : Subfunctor K) :
    Set.range (realization.map (relativeCollarSubcomplex K L).ι).hom ∪
      Set.range (realization.map (relativeCollarExterior K L).ι).hom = Set.univ :=
  realization_ranges_cover_of_sup_eq_top _ _ (relativeCollar_sup_exterior L)

/-- The realized exterior complement misses the retained realization. -/
theorem relativeCollarExterior_realization_disjoint_retained {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L : Subfunctor K) :
    Disjoint (Set.range (realization.map (relativeCollarExterior K L).ι).hom)
      (Set.range (realization.map (Subfunctor.range (relativeDerivedInclusion hK L)).ι).hom) :=
  realization_ranges_disjoint_of_inf_eq_bot _ _ (relativeCollarExterior_inf_retained hK L)

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeCollarSubcomplex_range_eq_preimage
#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeCollarSubcomplexes_realization_cover
#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeCollarExterior_realization_disjoint_retained
#print axioms HomotopyHypothesis.Approximation.Zeeman.isClosed_realization_range
