import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.Carriers
import HomotopyHypothesis.Approximation.Zeeman.Faces
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# Least carriers of relative derived simplices

A relative derived simplex has a least original carrier. Its faces therefore
have unique face maps between their least original carriers.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- A zero-dimensional simplex is its own sole vertex. -/
theorem vertex_zero {K : SemiSSet.{u}}
    (x : K.obj (op (Henry.SemiSimplexCategory.mk 0))) : vertex x (0 : Fin 1) = x := by
  have hv : vertexInclusion (0 : Fin 1) = 𝟙 (Henry.SemiSimplexCategory.mk 0) := by
    apply WideSubcategory.hom_ext
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro i
    change (0 : Fin 1) = i
    exact Subsingleton.elim _ _
  unfold vertex
  rw [hv]
  simp

/-- A carrier that is a face of every other carrier, with the unique face map. -/
def IsLeastRelativeCarrier {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : Fin (n + 1) → RelativeVertex K L) (s : Simplex K) : Prop :=
  (∀ i, RelativeVertex.CarriedBy (a i) s.2) ∧
    ∀ t : Simplex K, (∀ i, RelativeVertex.CarriedBy (a i) t.2) →
      ∃! θ : Henry.SemiSimplexCategory.mk s.1 ⟶ Henry.SemiSimplexCategory.mk t.1,
        K.map θ.op t.2 = s.2

/-- Every admissible relative derived tuple in a simplicial complex has a least carrier. -/
theorem exists_leastRelativeCarrier {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} {n : ℕ} (a : Fin (n + 1) → RelativeVertex K L)
    (ha : RelativeAdmissible a) : ∃ s : Simplex K, IsLeastRelativeCarrier a s := by
  cases hlast : a (Fin.last n) with
  | inl v =>
    let w : Fin (n + 1) → L.toFunctor.obj (op (Henry.SemiSimplexCategory.mk 0)) :=
      fun i => match a i with | .inl u => u | .inr _ => v
    have hw (i : Fin (n + 1)) : a i = .inl (w i) := by
      by_cases hi : i = Fin.last n
      · subst i
        simp only [w, hlast]
      · have hb := ha.2.1 i (Fin.last n) (lt_of_le_of_ne (Fin.le_last i) hi)
        cases he : a i with
        | inl u => simp only [w, he]
        | inr s => simp only [he, hlast, RelativeVertex.Precedes] at hb
    obtain ⟨x, hx⟩ := ha.2.2 n (𝟙 _) w hw
    refine ⟨⟨n, x.val⟩, ?_, ?_⟩
    · intro i
      rw [hw i]
      change ∃ θ : Henry.SemiSimplexCategory.mk 0 ⟶ Henry.SemiSimplexCategory.mk n,
        K.map θ.op x.val = (w i).val
      exact ⟨vertexInclusion i, congrArg Subtype.val (hx i)⟩
    · intro t ht
      apply (vertex_range_subset_iff_existsUnique_faceMap hK x.val t.2).mp
      rintro p ⟨i, rfl⟩
      have hi := ht i
      rw [hw i] at hi
      obtain ⟨θ, hθ⟩ := hi
      refine ⟨θ.hom.toOrderHom (0 : Fin 1), ?_⟩
      have hp := vertex_map θ t.2 (0 : Fin 1)
      rw [hθ, vertex_zero] at hp
      exact hp.symm.trans (congrArg Subtype.val (hx i)).symm
  | inr s =>
    refine ⟨s.val, ?_, ?_⟩
    · intro i
      by_cases hi : i = Fin.last n
      · subst i
        rw [hlast]
        change ∃ θ : Henry.SemiSimplexCategory.mk s.val.1 ⟶
          Henry.SemiSimplexCategory.mk s.val.1, K.map θ.op s.val.2 = s.val.2
        exact ⟨𝟙 _, by simp⟩
      · have hb := ha.2.1 i (Fin.last n) (lt_of_le_of_ne (Fin.le_last i) hi)
        rw [hlast] at hb
        cases he : a i with
        | inl v =>
          simpa only [he, RelativeVertex.Precedes, RelativeVertex.CarriedBy] using hb
        | inr t =>
          simp only [he, RelativeVertex.Precedes] at hb
          simpa only [he, RelativeVertex.CarriedBy] using hb.2
    · intro t ht
      have hi := ht (Fin.last n)
      rw [hlast] at hi
      obtain ⟨θ, hθ⟩ := hi
      refine ⟨θ, hθ, ?_⟩
      intro η hη
      exact faceMap_unique hK η θ hη hθ

/-- Choose a carrier with the least-carrier specification. -/
noncomputable def leastRelativeCarrier {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n))) : Simplex K :=
  Classical.choose (exists_leastRelativeCarrier hK a.val a.property)

/-- The chosen carrier contains the tuple and is a face of every other carrier. -/
theorem leastRelativeCarrier_spec {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} {n : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n))) :
    IsLeastRelativeCarrier a.val (leastRelativeCarrier hK a) :=
  Classical.choose_spec (exists_leastRelativeCarrier hK a.val a.property)

/-- Restriction of a relative derived simplex induces the unique face map of least carriers. -/
theorem leastRelativeCarrier_faceMap {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} {n m : ℕ}
    (a : (relativeDerived K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk n) :
    ∃! η : Henry.SemiSimplexCategory.mk
        (leastRelativeCarrier hK ((relativeDerived K L).map θ.op a)).1 ⟶
      Henry.SemiSimplexCategory.mk (leastRelativeCarrier hK a).1,
      K.map η.op (leastRelativeCarrier hK a).2 =
        (leastRelativeCarrier hK ((relativeDerived K L).map θ.op a)).2 := by
  apply (leastRelativeCarrier_spec hK ((relativeDerived K L).map θ.op a)).2
    (leastRelativeCarrier hK a)
  intro i
  exact (leastRelativeCarrier_spec hK a).1 (θ.hom.toOrderHom i)

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.exists_leastRelativeCarrier
#print axioms HomotopyHypothesis.Approximation.Zeeman.leastRelativeCarrier_faceMap
