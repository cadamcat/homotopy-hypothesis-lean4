import Mathlib.Data.Finset.Max
import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.Faces
import HomotopyHypothesis.Approximation.Zeeman.MixedFlags
import HomotopyHypothesis.Approximation.Zeeman.MixedImage
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# Original prefixes of mixed flags

Original vertices form an initial segment of a mixed flag. When this segment
is nonempty, it is the vertex tuple of a unique original simplex. The mixed
flag belongs to the derived end exactly when this original simplex belongs
to the fixed subcomplex.
-/

universe u

open CategoryTheory Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- Include the initial segment ending at a specified vertex. -/
def initialSegmentInclusion {n : ℕ} (j : Fin (n + 1)) :
    Henry.SemiSimplexCategory.mk j.val ⟶ Henry.SemiSimplexCategory.mk n :=
  ⟨SimplexCategory.Hom.mk (Fin.castLEOrderEmb (Nat.succ_le_of_lt j.isLt)).toOrderHom, by
    change Mono (show SimplexCategory.mk j.val ⟶ SimplexCategory.mk n from
      SimplexCategory.Hom.mk (Fin.castLEOrderEmb (Nat.succ_le_of_lt j.isLt)).toOrderHom)
    rw [SimplexCategory.mono_iff_injective]
    exact (Fin.castLEOrderEmb (Nat.succ_le_of_lt j.isLt)).injective⟩

/-- The last vertex of the initial segment maps to its specified endpoint. -/
theorem initialSegmentInclusion_last {n : ℕ} (j : Fin (n + 1)) :
    (initialSegmentInclusion j).hom.toOrderHom (Fin.last j.val) = j := by
  apply Fin.ext
  rfl

/-- An original vertex cannot occur after an exterior vertex. -/
theorem mixedOriginal_downward_closed {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    {i j : Fin (n + 1)} (hij : i ≤ j)
    (hj : ∃ w, a.val j = .inl w) : ∃ w, a.val i = .inl w := by
  obtain ⟨w, hj⟩ := hj
  rcases lt_or_eq_of_le hij with hij | rfl
  · cases hi : a.val i with
    | inl v => exact ⟨v, rfl⟩
    | inr s =>
      have h := a.property.2.1 i j hij
      simp only [hi, hj, MixedVertex.Precedes] at h
  · exact ⟨w, hj⟩

/-- The maximal original initial segment and its original simplex. -/
structure MixedOriginalPrefix {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk n))) where
  last : Fin (n + 1)
  face : K.obj (op (Henry.SemiSimplexCategory.mk last.val))
  vertices : ∀ i, a.val ((initialSegmentInclusion last).hom.toOrderHom i) =
    .inl (vertex face i)
  maximal : ∀ i, (∃ w, a.val i = .inl w) ↔ i ≤ last

/-- A mixed flag with an original vertex has maximal original-prefix data. -/
theorem exists_mixedOriginalPrefix {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (ha : ∃ i w, a.val i = .inl w) : Nonempty (MixedOriginalPrefix a) := by
  classical
  let s : Finset (Fin (n + 1)) := Finset.univ.filter (fun i => ∃ w, a.val i = .inl w)
  have hs : s.Nonempty := by
    obtain ⟨i, w, hi⟩ := ha
    exact ⟨i, by simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨w, hi⟩⟩
  let j := s.max' hs
  have hj : ∃ w, a.val j = .inl w := (Finset.mem_filter.mp (s.max'_mem hs)).2
  have hmax (i : Fin (n + 1)) : (∃ w, a.val i = .inl w) ↔ i ≤ j := by
    constructor
    · intro hi
      exact s.le_max' i (by simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]; exact hi)
    · intro hi
      exact mixedOriginal_downward_closed a hi hj
  have hw (i : Fin (j.val + 1)) :
      ∃ w, a.val ((initialSegmentInclusion j).hom.toOrderHom i) = .inl w := by
    apply (hmax _).mpr
    change i.val ≤ j.val
    omega
  choose w hw using hw
  obtain ⟨x, hx⟩ := a.property.2.2 j.val (initialSegmentInclusion j) w hw
  refine ⟨⟨j, x, ?_, hmax⟩⟩
  intro i
  exact (hw i).trans (congrArg Sum.inl (hx i).symm)

/-- The endpoint of a maximal original prefix is an original vertex. -/
theorem MixedOriginalPrefix.last_original {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    {a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk n))}
    (p : MixedOriginalPrefix a) : ∃ w, a.val p.last = .inl w := by
  refine ⟨vertex p.face (Fin.last p.last.val), ?_⟩
  simpa only [initialSegmentInclusion_last] using p.vertices (Fin.last p.last.val)

/-- Maximal original-prefix data are unique for an original simplicial complex. -/
theorem mixedOriginalPrefix_unique {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} {n : ℕ}
    {a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk n))}
    (p q : MixedOriginalPrefix a) : p = q := by
  have hlast : p.last = q.last := le_antisymm
    ((q.maximal p.last).mp p.last_original) ((p.maximal q.last).mp q.last_original)
  cases p with
  | mk lp xp hp mp =>
    cases q with
    | mk lq xq hq mq =>
      change lp = lq at hlast
      subst lq
      have hx : xp = xq := by
        apply simplex_eq_of_vertex_eq hK
        funext i
        exact Sum.inl.inj ((hp i).symm.trans (hq i))
      subst xq
      rfl

/-- All original subtuples lie in the fixed subcomplex exactly when the maximal prefix does. -/
theorem mixedOriginalFacesIn_iff_prefix_mem {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} {n : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (p : MixedOriginalPrefix a) :
    MixedOriginalFacesIn a ↔ p.face ∈ L.obj (op (Henry.SemiSimplexCategory.mk p.last.val)) := by
  constructor
  · intro ha
    obtain ⟨x, hx⟩ := ha p.last.val (initialSegmentInclusion p.last) (vertex p.face) p.vertices
    have h : x.val = p.face := simplex_eq_of_vertex_eq hK (funext hx)
    exact h ▸ x.property
  · intro hp m θ w hw
    obtain ⟨y, hy⟩ := a.property.2.2 m θ w hw
    have hr : Set.range (vertex y) ⊆ Set.range (vertex p.face) := by
      rintro v ⟨i, rfl⟩
      have hi := (p.maximal (θ.hom.toOrderHom i)).mp ⟨w i, hw i⟩
      let j : Fin (p.last.val + 1) := ⟨(θ.hom.toOrderHom i).val, by
        have hle : (θ.hom.toOrderHom i).val ≤ p.last.val := hi
        omega⟩
      have hj : (initialSegmentInclusion p.last).hom.toOrderHom j = θ.hom.toOrderHom i := by
        apply Fin.ext
        rfl
      have hv : vertex p.face j = w i := Sum.inl.inj
        ((p.vertices j).symm.trans ((congrArg a.val hj).trans (hw i)))
      exact ⟨j, hv.trans (hy i).symm⟩
    obtain ⟨η, hη⟩ := exists_faceMap_of_vertex_range_subset hK y p.face hr
    have hyL : y ∈ L.obj (op (Henry.SemiSimplexCategory.mk m)) := hη ▸ L.map η.op hp
    exact ⟨⟨y, hyL⟩, hy⟩

/-- A flag with original-prefix data lies in the derived end exactly when its prefix lies in L. -/
theorem mixedDerived_mem_range_iff_prefix_mem {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} {n : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (p : MixedOriginalPrefix a) :
    a ∈ Set.range ((mixedDerivedInclusion L).app (op (Henry.SemiSimplexCategory.mk n))) ↔
      p.face ∈ L.obj (op (Henry.SemiSimplexCategory.mk p.last.val)) :=
  (mixedDerived_mem_range_iff a).trans (mixedOriginalFacesIn_iff_prefix_mem hK a p)

/-- A mixed flag outside the derived end has an original prefix outside the fixed subcomplex. -/
theorem exists_exterior_originalPrefix {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} {n : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (ha : a ∉ Set.range
      ((mixedDerivedInclusion L).app (op (Henry.SemiSimplexCategory.mk n)))) :
    ∃ p : MixedOriginalPrefix a,
      p.face ∉ L.obj (op (Henry.SemiSimplexCategory.mk p.last.val)) := by
  obtain ⟨p⟩ := exists_mixedOriginalPrefix a (exists_original_of_not_in_derived a ha)
  exact ⟨p, fun hp => ha ((mixedDerived_mem_range_iff_prefix_mem hK a p).mpr hp)⟩

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.mixedOriginalPrefix_unique
#print axioms HomotopyHypothesis.Approximation.Zeeman.exists_exterior_originalPrefix
