import Mathlib.Data.Finset.Sort
import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# Faces determined by vertex supports

In a simplicial complex, a simplex is a face of another simplex precisely
when its vertices are contained among the latter's vertices. The associated
injective monotone map is unique.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- A simplex in a simplicial complex is determined by its unordered vertex support. -/
theorem simplex_eq_of_vertex_range_eq {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    {n : ℕ} {x y : K.obj (op (Henry.SemiSimplexCategory.mk n))}
    (h : Set.range (vertex x) = Set.range (vertex y)) : x = y := by
  apply uliftYonedaEquiv.symm.injective
  apply hK.2 n
  simpa only [← Set.range_comp, Function.comp_def, simplexChar_vertex] using
    congrArg (Set.image (fun t =>
      (simplexChar (uliftYonedaEquiv.symm t)).hom (simplexVertex (n := 0) 0))) h

/-- A vertex-support inclusion determines a face map. -/
theorem exists_faceMap_of_vertex_range_subset {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    {n m : ℕ} (x : K.obj (op (Henry.SemiSimplexCategory.mk n)))
    (y : K.obj (op (Henry.SemiSimplexCategory.mk m)))
    (h : Set.range (vertex x) ⊆ Set.range (vertex y)) :
    ∃ θ : Henry.SemiSimplexCategory.mk n ⟶ Henry.SemiSimplexCategory.mk m,
      K.map θ.op y = x := by
  classical
  have hp (i : Fin (n + 1)) : ∃ j : Fin (m + 1), vertex y j = vertex x i :=
    h ⟨i, rfl⟩
  let f : Fin (n + 1) → Fin (m + 1) := fun i => Classical.choose (hp i)
  have hf (i : Fin (n + 1)) : vertex y (f i) = vertex x i :=
    Classical.choose_spec (hp i)
  have hinj : Function.Injective f := by
    intro i j hij
    apply vertex_injective hK x
    rw [← hf i, ← hf j, hij]
  let s : Finset (Fin (m + 1)) := Finset.univ.image f
  have hcard : s.card = n + 1 := by
    simp only [s, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  let e : Fin (n + 1) ↪o Fin (m + 1) := s.orderEmbOfFin hcard
  let θ : Henry.SemiSimplexCategory.mk n ⟶ Henry.SemiSimplexCategory.mk m :=
    ⟨SimplexCategory.Hom.mk e.toOrderHom, by
      change Mono (show SimplexCategory.mk n ⟶ SimplexCategory.mk m from
        SimplexCategory.Hom.mk e.toOrderHom)
      rw [SimplexCategory.mono_iff_injective]
      exact e.injective⟩
  have he : Set.range θ.hom.toOrderHom = Set.range f := by
    change Set.range (s.orderEmbOfFin hcard) = Set.range f
    rw [Finset.range_orderEmbOfFin]
    simp [s]
  refine ⟨θ, simplex_eq_of_vertex_range_eq hK ?_⟩
  calc
    Set.range (vertex (K.map θ.op y)) = Set.range (vertex y ∘ θ.hom.toOrderHom) := by
      congr 1
      funext i
      exact vertex_map θ y i
    _ = vertex y '' Set.range θ.hom.toOrderHom := Set.range_comp _ _
    _ = vertex y '' Set.range f := by rw [he]
    _ = Set.range (vertex y ∘ f) := (Set.range_comp _ _).symm
    _ = Set.range (vertex x) := by
      congr 1
      funext i
      exact hf i

/-- A fixed face inclusion into a simplex of a simplicial complex is unique. -/
theorem faceMap_unique {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex) {n m : ℕ}
    {x : K.obj (op (Henry.SemiSimplexCategory.mk n))}
    {y : K.obj (op (Henry.SemiSimplexCategory.mk m))}
    (θ η : Henry.SemiSimplexCategory.mk n ⟶ Henry.SemiSimplexCategory.mk m)
    (hθ : K.map θ.op y = x) (hη : K.map η.op y = x) : θ = η := by
  apply WideSubcategory.hom_ext
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro i
  apply vertex_injective hK y
  rw [← vertex_map θ y i, ← vertex_map η y i, hθ, hη]

/-- Vertex-support inclusion is equivalent to the existence of a unique face map. -/
theorem vertex_range_subset_iff_existsUnique_faceMap {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {n m : ℕ}
    (x : K.obj (op (Henry.SemiSimplexCategory.mk n)))
    (y : K.obj (op (Henry.SemiSimplexCategory.mk m))) :
    Set.range (vertex x) ⊆ Set.range (vertex y) ↔
      ∃! θ : Henry.SemiSimplexCategory.mk n ⟶ Henry.SemiSimplexCategory.mk m,
        K.map θ.op y = x := by
  constructor
  · intro h
    obtain ⟨θ, hθ⟩ := exists_faceMap_of_vertex_range_subset hK x y h
    refine ⟨θ, hθ, ?_⟩
    intro η hη
    exact faceMap_unique hK η θ hη hθ
  · rintro ⟨θ, hθ, _⟩ v ⟨i, hi⟩
    refine ⟨θ.hom.toOrderHom i, ?_⟩
    rw [← vertex_map θ y i, hθ]
    exact hi

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.vertex_range_subset_iff_existsUnique_faceMap
