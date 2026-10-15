import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.Carriers
import HomotopyHypothesis.Approximation.Zeeman.CollarSubcomplex
import HomotopyHypothesis.Approximation.Zeeman.CollarVertices
import HomotopyHypothesis.Approximation.Zeeman.LeastCarrier
import HomotopyHypothesis.Approximation.Zeeman.LocalAffine
import HomotopyHypothesis.Approximation.Zeeman.Positions
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.RelativeSupports
import HomotopyHypothesis.Approximation.Zeeman.RetainedFull
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# Subdivisions induced on subcomplexes

A derived simplex belongs to the subdivision induced on a subcomplex when
its least original carrier belongs to that subcomplex. This condition is
preserved by faces. If the original subcomplex is disjoint from the retained
one, every derived simplex meeting its induced subdivision has no retained
entries.
-/

universe u

open CategoryTheory Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- The subdivision induced on a subcomplex, specified by least original carriers. -/
noncomputable def inducedRelativeSubdivision {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L A : Subfunctor K) : Subfunctor (relativeDerived K L) where
  obj X a := (leastRelativeCarrier hK a).2 ∈ A.obj
    (op (Henry.SemiSimplexCategory.mk (leastRelativeCarrier hK a).1))
  map f := by
    intro a ha
    change (leastRelativeCarrier hK ((relativeDerived K L).map f a)).2 ∈
      A.obj (op (Henry.SemiSimplexCategory.mk
        (leastRelativeCarrier hK ((relativeDerived K L).map f a)).1))
    exact (relativeCarrierFaceMap_spec hK a f.unop) ▸
      A.map (relativeCarrierFaceMap hK a f.unop).op ha

/-- Every source face of an induced simplex belongs to the original subcomplex. -/
theorem source_mem_of_inducedRelativeSubdivision {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L A : Subfunctor K) {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (ha : a ∈ (inducedRelativeSubdivision hK L A).obj (op (Henry.SemiSimplexCategory.mk n)))
    (i : Fin (n + 1)) :
    (a.val i).sourceSimplex.2 ∈ A.obj (op (Henry.SemiSimplexCategory.mk (a.val i).sourceSimplex.1)) :=
  (carriedFaceMap_spec (leastRelativeCarrier hK a).2 (a.val i)
    ((leastRelativeCarrier_spec hK a).1 i)) ▸
      A.map (carriedFaceMap (leastRelativeCarrier hK a).2 (a.val i)
        ((leastRelativeCarrier_spec hK a).1 i)).op ha

/-- The carrier of a derived vertex is its source face. -/
theorem leastRelativeCarrier_vertex {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (i : Fin (n + 1)) :
    leastRelativeCarrier hK (vertex a i) = (a.val i).sourceSimplex := by
  apply simplex_eq_of_vertex_range_eq_sigma hK
  ext w
  constructor
  · intro hw
    obtain ⟨j, hj⟩ := (relativeTuple_source_support_iff_carrier hK (vertex a i) w).mpr hw
    have hj0 : j = (0 : Fin 1) := by
      change (_ : Fin 1) = _
      exact Subsingleton.elim _ _
    subst j
    exact hj
  · intro hw
    exact (relativeTuple_source_support_iff_carrier hK (vertex a i) w).mp ⟨0, hw⟩

/-- A derived vertex belongs to the induced subdivision exactly when its source face does. -/
theorem inducedRelativeSubdivision_vertex_mem_iff {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L A : Subfunctor K) {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n))) (i : Fin (n + 1)) :
    vertex a i ∈ (inducedRelativeSubdivision hK L A).obj (op (Henry.SemiSimplexCategory.mk 0)) ↔
      (a.val i).sourceSimplex.2 ∈ A.obj
        (op (Henry.SemiSimplexCategory.mk (a.val i).sourceSimplex.1)) := by
  change (leastRelativeCarrier hK (vertex a i)).2 ∈
    A.obj (op (Henry.SemiSimplexCategory.mk (leastRelativeCarrier hK (vertex a i)).1)) ↔ _
  rw [leastRelativeCarrier_vertex]

/-- A source in a subcomplex disjoint from L prevents every retained entry. -/
theorem relativeTuple_no_retainedEntry_of_source_mem {K : SemiSSet.{u}}
    {L A : Subfunctor K} (hAL : A ⊓ L = ⊥) {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n))) (i : Fin (n + 1))
    (hi : (a.val i).sourceSimplex.2 ∈
      A.obj (op (Henry.SemiSimplexCategory.mk (a.val i).sourceSimplex.1))) :
    ∀ j, ¬ ∃ v, a.val j = Sum.inl v := by
  rintro j ⟨v, hv⟩
  obtain ⟨k, hk⟩ := relativeSource_meets_of_retainedEntry a ⟨j, v, hv⟩ i
  have hmem : vertex (a.val i).sourceSimplex.2 k ∈
      (A ⊓ L).obj (op (Henry.SemiSimplexCategory.mk 0)) :=
    ⟨A.map (vertexInclusion k).op hi, hk⟩
  rw [hAL] at hmem
  exact hmem

/-- Stars meeting an induced subdivision disjoint from L have no retained entries. -/
theorem inducedRelativeSubdivision_star_no_retainedEntry {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L A : Subfunctor K) (hAL : A ⊓ L = ⊥) {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (ha : ∃ i, vertex a i ∈ (inducedRelativeSubdivision hK L A).obj
      (op (Henry.SemiSimplexCategory.mk 0))) :
    ∀ j, ¬ ∃ v, a.val j = Sum.inl v := by
  obtain ⟨i, hi⟩ := ha
  exact relativeTuple_no_retainedEntry_of_source_mem hAL a i
    ((inducedRelativeSubdivision_vertex_mem_iff hK L A a i).mp hi)

/-- The induced subdivision remains disjoint from the retained image. -/
theorem inducedRelativeSubdivision_inf_retained {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L A : Subfunctor K) (hAL : A ⊓ L = ⊥) :
    inducedRelativeSubdivision hK L A ⊓ Subfunctor.range (relativeDerivedInclusion hK L) = ⊥ := by
  ext X a
  constructor
  · rintro ⟨ha, hret⟩
    exact relativeTuple_no_retainedEntry_of_source_mem hAL a 0
      (source_mem_of_inducedRelativeSubdivision hK L A a ha 0) 0
      ((relativeDerivedInclusion_mem_range_iff hK L a).mp hret 0)
  · intro h
    exact h.elim

/-- The induced subdivision of a finite complex is finite. -/
theorem inducedRelativeSubdivision_isFinite {K : SemiSSet.{u}} (hK : K.IsFinite)
    (hKs : K.IsSimplicialComplex) (L A : Subfunctor K) :
    Henry.SemiSSet.IsFinite (inducedRelativeSubdivision hKs L A).toFunctor :=
  subfunctor_isFinite (relativeDerived_isFinite hK L) _

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.leastRelativeCarrier_vertex
#print axioms HomotopyHypothesis.Approximation.Zeeman.inducedRelativeSubdivision_star_no_retainedEntry
#print axioms HomotopyHypothesis.Approximation.Zeeman.inducedRelativeSubdivision_inf_retained
