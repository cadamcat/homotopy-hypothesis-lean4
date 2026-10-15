import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.Carriers
import HomotopyHypothesis.Approximation.Zeeman.Faces
import HomotopyHypothesis.Approximation.Zeeman.LeastCarrier
import HomotopyHypothesis.Approximation.Zeeman.LocalAffine
import HomotopyHypothesis.Approximation.Zeeman.PositionSupports
import HomotopyHypothesis.Approximation.Zeeman.Positions
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# Linear embeddings of relative derived simplices

Every source face in an admissible tuple contributes a vertex absent from
all preceding source faces. These vertices give triangular coordinates for
the barycentric positions, proving that the local affine maps are embeddings.
-/

universe u

open CategoryTheory Opposite Convexity

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- The face inclusion of the first vertices of an ordinal. -/
def initialFace {m n : ℕ} (h : m ≤ n) :
    Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk n :=
  let e := Fin.castLEOrderEmb (Nat.add_le_add_right h 1)
  ⟨SimplexCategory.Hom.mk e.toOrderHom, by
    change Mono (show SimplexCategory.mk m ⟶ SimplexCategory.mk n from
      SimplexCategory.Hom.mk e.toOrderHom)
    rw [SimplexCategory.mono_iff_injective]
    exact e.injective⟩

/-- All source vertices of a carried subdivision vertex lie in its original carrier. -/
theorem source_vertex_range_subset_of_carried {K : SemiSSet.{u}} {L : Subfunctor K}
    {m : ℕ} (y : K.obj (op (Henry.SemiSimplexCategory.mk m))) (v : RelativeVertex K L)
    (hv : RelativeVertex.CarriedBy v y) :
    Set.range (vertex v.sourceSimplex.2) ⊆ Set.range (vertex y) := by
  rintro w ⟨i, hi⟩
  refine ⟨(carriedFaceMap y v hv).hom.toOrderHom i, ?_⟩
  have hp := vertex_map (carriedFaceMap y v hv) y i
  rw [carriedFaceMap_spec] at hp
  exact hp.symm.trans hi

/-- The last source face in an admissible tuple contributes a new original vertex. -/
theorem relativeTuple_last_new_source_vertex {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n))) :
    ∃ w : K.obj (op (Henry.SemiSimplexCategory.mk 0)),
      w ∈ Set.range (vertex (a.val (Fin.last n)).sourceSimplex.2) ∧
        ∀ j, j < Fin.last n → w ∉ Set.range (vertex (a.val j).sourceSimplex.2) := by
  cases hlast : a.val (Fin.last n) with
  | inl v =>
    refine ⟨v.val, ?_, ?_⟩
    · exact ⟨0, vertex_zero v.val⟩
    · intro j hj hw
      cases he : a.val j with
      | inl z =>
        rw [he] at hw
        change v.val ∈ Set.range (vertex z.val) at hw
        obtain ⟨q, hq⟩ := hw
        have hq0 : q = 0 := by
          apply Fin.ext
          omega
        rw [hq0, vertex_zero] at hq
        have hzv : z = v := Subtype.ext hq
        have heq : a.val j = a.val (Fin.last n) := by rw [he, hlast, hzv]
        exact (ne_of_lt hj) (a.property.1 heq)
      | inr t =>
        have hp := a.property.2.1 j (Fin.last n) hj
        simp only [he, hlast, RelativeVertex.Precedes] at hp
  | inr s =>
    cases n with
    | zero =>
      refine ⟨vertex s.val.2 0, ?_, ?_⟩
      · exact ⟨0, rfl⟩
      · intro j hj
        have hlastj : j = Fin.last 0 := by
          apply Fin.ext
          omega
        exact (ne_of_lt hj hlastj).elim
    | succ k =>
      let prev : Fin (k + 2) := (Fin.last k).castSucc
      have hprevlt : prev < Fin.last (k + 1) := Fin.castSucc_lt_last _
      cases hprev : a.val prev with
      | inr t =>
        have hp := a.property.2.1 prev (Fin.last (k + 1)) hprevlt
        simp only [hprev, hlast, RelativeVertex.Precedes] at hp
        have hns : ¬ Set.range (vertex s.val.2) ⊆ Set.range (vertex t.val.2) := by
          intro hsub
          obtain ⟨η, _⟩ := exists_faceMap_of_vertex_range_subset hK s.val.2 t.val.2 hsub
          have hc := Fintype.card_le_of_injective
            η.hom.toOrderHom (SimplexCategory.mono_iff_injective.mp η.property)
          simp only [Fintype.card_fin] at hc
          omega
        obtain ⟨w, hws, hwt⟩ := Set.not_subset.mp hns
        refine ⟨w, ?_, ?_⟩
        · exact hws
        · intro j hj hw
          have hjle : j ≤ prev := by
            change j.val ≤ k
            have h := hj
            change j.val < k + 1 at h
            omega
          have hcar : RelativeVertex.CarriedBy (a.val j) t.val.2 := by
            by_cases hjeq : j = prev
            · rw [hjeq, hprev]
              exact ⟨𝟙 _, by simp⟩
            · have hb := a.property.2.1 j prev (lt_of_le_of_ne hjle hjeq)
              cases he : a.val j with
              | inl z =>
                simpa only [he, hprev, RelativeVertex.Precedes, RelativeVertex.CarriedBy] using hb
              | inr z =>
                simp only [he, hprev, RelativeVertex.Precedes] at hb
                simpa only [he, RelativeVertex.CarriedBy] using hb.2
          exact hwt (source_vertex_range_subset_of_carried t.val.2 (a.val j) hcar hw)
      | inl v =>
        let θ : Henry.SemiSimplexCategory.mk k ⟶ Henry.SemiSimplexCategory.mk (k + 1) :=
          initialFace (Nat.le_succ k)
        let b := (relativeDerived K L).map θ.op a
        have hlastb : b.val (Fin.last k) = Sum.inl v := hprev
        let z : Fin (k + 1) → L.toFunctor.obj (op (Henry.SemiSimplexCategory.mk 0)) :=
          fun i => match b.val i with | .inl u => u | .inr _ => v
        have hz (i : Fin (k + 1)) : b.val i = .inl (z i) := by
          by_cases hi : i = Fin.last k
          · subst i
            simp only [z, hlastb]
          · have hp := b.property.2.1 i (Fin.last k)
              (lt_of_le_of_ne (Fin.le_last i) hi)
            cases he : b.val i with
            | inl u => simp only [z, he]
            | inr t => simp only [he, hlastb, RelativeVertex.Precedes] at hp
        obtain ⟨x, hx⟩ := b.property.2.2 k (𝟙 _) z hz
        have hns : ¬ Set.range (vertex s.val.2) ⊆ Set.range (vertex x.val) := by
          intro hsub
          obtain ⟨η, hη⟩ := exists_faceMap_of_vertex_range_subset hK s.val.2 x.val hsub
          exact s.property (hη ▸ L.map η.op x.property)
        obtain ⟨w, hws, hwx⟩ := Set.not_subset.mp hns
        refine ⟨w, ?_, ?_⟩
        · exact hws
        · intro j hj hw
          have hjlt : j.val < k + 1 := hj
          let j' : Fin (k + 1) := ⟨j.val, hjlt⟩
          have hjθ : θ.hom.toOrderHom j' = j := Fin.ext rfl
          have he : a.val j = .inl (z j') := by
            have he' := hz j'
            change a.val (θ.hom.toOrderHom j') = .inl (z j') at he'
            rwa [hjθ] at he'
          rw [he] at hw
          change w ∈ Set.range (vertex (z j').val) at hw
          obtain ⟨q, hq⟩ := hw
          have hq0 : q = 0 := by
            apply Fin.ext
            omega
          rw [hq0, vertex_zero] at hq
          apply hwx
          refine ⟨j', ?_⟩
          exact (congrArg Subtype.val (hx j')).trans hq

/-- Every source face in an admissible tuple contributes a vertex outside all preceding sources. -/
theorem relativeTuple_new_source_vertices {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n))) :
    ∀ i, ∃ w : K.obj (op (Henry.SemiSimplexCategory.mk 0)),
      w ∈ Set.range (vertex (a.val i).sourceSimplex.2) ∧
        ∀ j, j < i → w ∉ Set.range (vertex (a.val j).sourceSimplex.2) := by
  intro i
  let θ : Henry.SemiSimplexCategory.mk i.val ⟶ Henry.SemiSimplexCategory.mk n :=
    initialFace (Nat.le_of_lt_succ i.isLt)
  let b := (relativeDerived K L).map θ.op a
  obtain ⟨w, hw, hprev⟩ := relativeTuple_last_new_source_vertex hK b
  have hlast : θ.hom.toOrderHom (Fin.last i.val) = i := Fin.ext rfl
  change w ∈ Set.range (vertex (a.val (θ.hom.toOrderHom (Fin.last i.val))).sourceSimplex.2) at hw
  rw [hlast] at hw
  refine ⟨w, hw, ?_⟩
  intro j hj hwj
  let j' : Fin (i.val + 1) := ⟨j.val, Nat.lt_succ_of_le (Nat.le_of_lt hj)⟩
  have hjθ : θ.hom.toOrderHom j' = j := Fin.ext rfl
  apply hprev j' (show j' < Fin.last i.val from hj)
  change w ∈ Set.range (vertex (a.val (θ.hom.toOrderHom j')).sourceSimplex.2)
  rwa [hjθ]

/-- The local affine maps of relative derived simplices are injective. -/
theorem relativeLocalAffineMap_injective {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n))) :
    Function.Injective (relativeLocalAffineMap hK a) :=
  relativeLocalAffineMap_injective_of_new_source_vertices hK a
    (relativeTuple_new_source_vertices hK a)

/-- Each derived simplex maps into its original carrier by a linear embedding. -/
theorem relativeLocalTopMap_isLinearEmbedding {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n))) :
    IsLinearEmbedding (relativeLocalTopMap hK a) := by
  refine ⟨(relativeLocalAffineMap hK a).isAffineMap, ?_⟩
  intro x y hxy
  apply ULift.ext
  apply relativeLocalAffineMap_injective hK a
  exact congrArg ULift.down hxy

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeTuple_new_source_vertices
#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeLocalTopMap_isLinearEmbedding
