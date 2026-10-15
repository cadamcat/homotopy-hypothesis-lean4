import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.DerivedSubdivision
import HomotopyHypothesis.Approximation.Zeeman.MixedOriginalPrefix
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.SubdivisionComposition
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# Fullness of the retained subcomplex

After a relative derived subdivision, a simplex belongs to the retained
subcomplex exactly when all its vertices do. The retained vertices of any
derived simplex form an initial face, or the empty set.
-/

universe u

open CategoryTheory Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- A full subcomplex contains every simplex whose vertices it contains. -/
def IsFullSubcomplex {K : SemiSSet.{u}} (L : Subfunctor K) : Prop :=
  ∀ (n : ℕ) (x : K.obj (op (Henry.SemiSimplexCategory.mk n))),
    (∀ i, vertex x i ∈ L.obj (op (Henry.SemiSimplexCategory.mk 0))) →
      x ∈ L.obj (op (Henry.SemiSimplexCategory.mk n))

/-- A derived simplex is in the retained image exactly when all its entries
are retained vertices. -/
theorem relativeDerivedInclusion_mem_range_iff {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L : Subfunctor K) {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n))) :
    a ∈ (Subfunctor.range (relativeDerivedInclusion hK L)).obj
      (op (Henry.SemiSimplexCategory.mk n)) ↔
        ∀ i, ∃ v, a.val i = Sum.inl v := by
  classical
  constructor
  · rintro ⟨x, rfl⟩ i
    exact ⟨vertex x i, rfl⟩
  · intro ha
    choose w hw using ha
    obtain ⟨x, hx⟩ := a.property.2.2 n (𝟙 _) w hw
    refine ⟨x, ?_⟩
    apply Subtype.ext
    funext i
    exact (congrArg Sum.inl (hx i)).trans (hw i).symm

/-- Membership of a vertex in the retained image detects its tuple entry. -/
theorem relativeDerived_vertex_mem_range_iff {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L : Subfunctor K) {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (i : Fin (n + 1)) :
    vertex a i ∈ (Subfunctor.range (relativeDerivedInclusion hK L)).obj
      (op (Henry.SemiSimplexCategory.mk 0)) ↔ ∃ v, a.val i = Sum.inl v := by
  rw [relativeDerivedInclusion_mem_range_iff]
  constructor
  · intro h
    exact h 0
  · rintro ⟨v, hv⟩ j
    exact ⟨v, hv⟩

/-- One relative derived subdivision makes the retained subcomplex full. -/
theorem relativeDerivedInclusion_isFull {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) (L : Subfunctor K) :
    IsFullSubcomplex (Subfunctor.range (relativeDerivedInclusion hK L)) := by
  intro n a ha
  apply (relativeDerivedInclusion_mem_range_iff hK L a).mpr
  intro i
  exact (relativeDerived_vertex_mem_range_iff hK L a i).mp (ha i)

/-- The retained image of the relative subdivision with its prism is full. -/
theorem derivedSubdivision_retained_isFull {K : SemiSSet.{u}}
    (hK : K.IsFinite) (hKs : K.IsSimplicialComplex) (L : Subfunctor K) :
    IsFullSubcomplex (Subfunctor.range (derivedSubdivision hK hKs L).j) :=
  relativeDerivedInclusion_isFull hKs L

/-- Retained entries in a derived simplex form a downward closed set. -/
theorem relativeRetained_downward_closed {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    {i j : Fin (n + 1)} (hij : i ≤ j)
    (hj : ∃ v, a.val j = Sum.inl v) : ∃ v, a.val i = Sum.inl v := by
  obtain ⟨v, hj⟩ := hj
  rcases lt_or_eq_of_le hij with hij | rfl
  · cases hi : a.val i with
    | inl w => exact ⟨w, rfl⟩
    | inr s =>
      have h := a.property.2.1 i j hij
      simp only [hi, hj, RelativeVertex.Precedes] at h
  · exact ⟨v, hj⟩

/-- The maximal retained face of a derived simplex with a retained vertex. -/
structure RelativeRetainedFace {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n))) where
  last : Fin (n + 1)
  face : L.toFunctor.obj (op (Henry.SemiSimplexCategory.mk last.val))
  vertices : ∀ i, a.val ((initialSegmentInclusion last).hom.toOrderHom i) =
    Sum.inl (vertex face i)
  maximal : ∀ i, (∃ v, a.val i = Sum.inl v) ↔ i ≤ last

/-- A nonempty intersection with the retained subcomplex has a maximal face. -/
theorem exists_relativeRetainedFace {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (ha : ∃ i v, a.val i = Sum.inl v) : Nonempty (RelativeRetainedFace a) := by
  classical
  let s : Finset (Fin (n + 1)) := Finset.univ.filter (fun i => ∃ v, a.val i = Sum.inl v)
  have hs : s.Nonempty := by
    obtain ⟨i, v, hi⟩ := ha
    exact ⟨i, by simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using ⟨v, hi⟩⟩
  let j := s.max' hs
  have hj : ∃ v, a.val j = Sum.inl v := (Finset.mem_filter.mp (s.max'_mem hs)).2
  have hmax (i : Fin (n + 1)) : (∃ v, a.val i = Sum.inl v) ↔ i ≤ j := by
    constructor
    · intro hi
      exact s.le_max' i (by simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using hi)
    · intro hi
      exact relativeRetained_downward_closed a hi hj
  have hw (i : Fin (j.val + 1)) :
      ∃ v, a.val ((initialSegmentInclusion j).hom.toOrderHom i) = Sum.inl v := by
    apply (hmax _).mpr
    change i.val ≤ j.val
    omega
  choose w hw using hw
  obtain ⟨x, hx⟩ := a.property.2.2 j.val (initialSegmentInclusion j) w hw
  exact ⟨⟨j, x, fun i => (hw i).trans (congrArg Sum.inl (hx i).symm), hmax⟩⟩

/-- A face is retained exactly when all its indices lie in the maximal retained face. -/
theorem RelativeRetainedFace.restriction_mem_iff {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n m : ℕ}
    {a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n))}
    (p : RelativeRetainedFace a)
    (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk n) :
    (relativeDerived K L).map θ.op a ∈
      (Subfunctor.range (relativeDerivedInclusion hK L)).obj
        (op (Henry.SemiSimplexCategory.mk m)) ↔
          ∀ i, θ.hom.toOrderHom i ≤ p.last := by
  rw [relativeDerivedInclusion_mem_range_iff]
  exact forall_congr' (fun i => p.maximal (θ.hom.toOrderHom i))

/-- The maximal retained initial face is the image of its simplex of the fixed subcomplex. -/
theorem RelativeRetainedFace.restriction_eq {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n : ℕ}
    {a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n))}
    (p : RelativeRetainedFace a) :
    (relativeDerived K L).map (initialSegmentInclusion p.last).op a =
      (relativeDerivedInclusion hK L).app _ p.face := by
  apply Subtype.ext
  funext i
  exact p.vertices i

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeDerivedInclusion_isFull
#print axioms HomotopyHypothesis.Approximation.Zeeman.derivedSubdivision_retained_isFull
#print axioms HomotopyHypothesis.Approximation.Zeeman.exists_relativeRetainedFace
#print axioms HomotopyHypothesis.Approximation.Zeeman.RelativeRetainedFace.restriction_eq
