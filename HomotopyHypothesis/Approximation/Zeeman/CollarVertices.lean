import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.Carriers
import HomotopyHypothesis.Approximation.Zeeman.LeastCarrier
import HomotopyHypothesis.Approximation.Zeeman.Positions
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.RetainedFull
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# Vertex choices for a relative collar

Choose a vertex of each source simplex, preferring a vertex of the retained
subcomplex whenever one exists. On a derived simplex with a retained entry,
every source simplex has such a vertex. The chosen vertices lie in each
original carrier and commute with inclusions of carriers.
-/

universe u

open CategoryTheory Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- Choose a source vertex in the subcomplex whenever one exists. -/
noncomputable def subcomplexVertexChoice {K : SemiSSet.{u}} (L : Subfunctor K)
    (s : Simplex K) : Fin (s.1 + 1) := by
  classical
  exact if h : ∃ i, vertex s.2 i ∈ L.obj (op (Henry.SemiSimplexCategory.mk 0))
    then Classical.choose h else 0

/-- The preferred source vertex belongs to the subcomplex when the source meets it. -/
theorem subcomplexVertexChoice_mem {K : SemiSSet.{u}} (L : Subfunctor K)
    (s : Simplex K)
    (hs : ∃ i, vertex s.2 i ∈ L.obj (op (Henry.SemiSimplexCategory.mk 0))) :
    vertex s.2 (subcomplexVertexChoice L s) ∈
      L.obj (op (Henry.SemiSimplexCategory.mk 0)) := by
  classical
  simpa only [subcomplexVertexChoice, dite_eq_left hs] using Classical.choose_spec hs

/-- The original vertex chosen for a relative derived vertex. -/
noncomputable def relativeCollarVertex {K : SemiSSet.{u}} {L : Subfunctor K}
    (v : RelativeVertex K L) : K.obj (op (Henry.SemiSimplexCategory.mk 0)) :=
  vertex v.sourceSimplex.2 (subcomplexVertexChoice L v.sourceSimplex)

/-- Retained vertices are fixed by the collar vertex choice. -/
theorem relativeCollarVertex_retained {K : SemiSSet.{u}} {L : Subfunctor K}
    (v : L.toFunctor.obj (op (Henry.SemiSimplexCategory.mk 0))) :
    relativeCollarVertex (Sum.inl v : RelativeVertex K L) = v.val := by
  unfold relativeCollarVertex
  change vertex v.val (subcomplexVertexChoice L ⟨0, v.val⟩) = v.val
  have h : subcomplexVertexChoice L ⟨0, v.val⟩ = (0 : Fin 1) := by
    change (_ : Fin 1) = _
    exact Subsingleton.elim _ _
  rw [h]
  exact vertex_zero v.val

/-- The position of the chosen original vertex in a carrier. -/
noncomputable def relativeCollarVertexIndex {K : SemiSSet.{u}} {L : Subfunctor K} {m : ℕ}
    (y : K.obj (op (Henry.SemiSimplexCategory.mk m))) (v : RelativeVertex K L)
    (hv : RelativeVertex.CarriedBy v y) : Fin (m + 1) :=
  (carriedFaceMap y v hv).hom.toOrderHom (subcomplexVertexChoice L v.sourceSimplex)

/-- The chosen index represents the global choice of original vertex. -/
theorem relativeCollarVertexIndex_spec {K : SemiSSet.{u}} {L : Subfunctor K} {m : ℕ}
    (y : K.obj (op (Henry.SemiSimplexCategory.mk m))) (v : RelativeVertex K L)
    (hv : RelativeVertex.CarriedBy v y) :
    vertex y (relativeCollarVertexIndex y v hv) = relativeCollarVertex v := by
  unfold relativeCollarVertexIndex relativeCollarVertex
  rw [← vertex_map, carriedFaceMap_spec]

/-- Collar vertex indices commute with inclusions of carriers. -/
theorem relativeCollarVertexIndex_face {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {m k : ℕ}
    {y : K.obj (op (Henry.SemiSimplexCategory.mk m))}
    {z : K.obj (op (Henry.SemiSimplexCategory.mk k))}
    (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk k)
    (hθ : K.map θ.op z = y) (v : RelativeVertex K L)
    (hy : RelativeVertex.CarriedBy v y) (hz : RelativeVertex.CarriedBy v z) :
    relativeCollarVertexIndex z v hz =
      θ.hom.toOrderHom (relativeCollarVertexIndex y v hy) := by
  unfold relativeCollarVertexIndex
  rw [carriedFaceMap_comp hK θ hθ v hy hz]
  rfl

/-- On a retained tuple, the collar index is the original vertex index. -/
theorem relativeCollarVertexIndex_retained {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n : ℕ}
    (x : L.toFunctor.obj (op (Henry.SemiSimplexCategory.mk n))) (i : Fin (n + 1))
    (hi : RelativeVertex.CarriedBy (Sum.inl (vertex x i) : RelativeVertex K L) x.val) :
    relativeCollarVertexIndex x.val (.inl (vertex x i)) hi = i := by
  apply vertex_injective hK x.val
  rw [relativeCollarVertexIndex_spec, relativeCollarVertex_retained]
  rfl

/-- A retained entry in a derived simplex makes every source simplex meet the subcomplex. -/
theorem relativeSource_meets_of_retainedEntry {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (ha : ∃ j v, a.val j = Sum.inl v) (i : Fin (n + 1)) :
    ∃ k, vertex (a.val i).sourceSimplex.2 k ∈
      L.obj (op (Henry.SemiSimplexCategory.mk 0)) := by
  obtain ⟨j, v, hj⟩ := ha
  cases hi : a.val i with
  | inl w =>
    refine ⟨0, ?_⟩
    change vertex w.val 0 ∈ L.obj _
    rw [vertex_zero]
    exact w.property
  | inr s =>
    have hji : j < i := by
      rcases lt_trichotomy j i with h | h | h
      · exact h
      · have hn := hj.symm.trans (h ▸ hi)
        cases hn
      · have hn := a.property.2.1 i j h
        simp only [hi, hj, RelativeVertex.Precedes] at hn
    have h := a.property.2.1 j i hji
    rw [hj, hi] at h
    obtain ⟨θ, hθ⟩ := h
    refine ⟨θ.hom.toOrderHom 0, ?_⟩
    change vertex s.val.2 (θ.hom.toOrderHom 0) ∈ L.obj _
    rw [← vertex_map θ s.val.2, hθ, vertex_zero]
    exact v.property

/-- All chosen vertices of a derived simplex meeting the retained subcomplex lie in it. -/
theorem relativeCollarVertex_mem_of_retainedEntry {K : SemiSSet.{u}}
    {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (ha : ∃ j v, a.val j = Sum.inl v) (i : Fin (n + 1)) :
    relativeCollarVertex (a.val i) ∈ L.obj (op (Henry.SemiSimplexCategory.mk 0)) :=
  subcomplexVertexChoice_mem L _ (relativeSource_meets_of_retainedEntry a ha i)

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeCollarVertexIndex_face
#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeCollarVertex_mem_of_retainedEntry
