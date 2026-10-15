import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.Faces
import HomotopyHypothesis.Approximation.Zeeman.LeastCarrier
import HomotopyHypothesis.Approximation.Zeeman.MixedFlags
import HomotopyHypothesis.Approximation.Zeeman.MixedOriginalPrefix
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
import HomotopyHypothesis.Approximation.Zeeman.Vertices
/-!
# Incidence of an original prefix with exterior faces

Every exterior face of a mixed flag carries its whole original prefix.
Its dimension is therefore at least the prefix dimension, and equality
identifies it with that prefix face. The prefix barycentre, if present,
is consequently the first exterior entry.
-/

universe u

open CategoryTheory Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- Exterior entries lie strictly after the original prefix. -/
theorem mixedExterior_after_prefix {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (p : MixedOriginalPrefix a) (i : Fin (n + 1))
    (s : {s : Simplex K // s.2 ∉ L.obj (op (Henry.SemiSimplexCategory.mk s.1))})
    (hi : a.val i = .inr s) : p.last < i := by
  by_contra hn
  obtain ⟨w, hw⟩ := (p.maximal i).mpr (le_of_not_gt hn)
  simp only [hi, Sum.inr_ne_inl] at hw

/-- The original prefix has a unique face inclusion into each exterior source. -/
theorem mixedOriginalPrefix_faceMap_to_exterior {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (p : MixedOriginalPrefix a) (i : Fin (n + 1))
    (s : {s : Simplex K // s.2 ∉ L.obj (op (Henry.SemiSimplexCategory.mk s.1))})
    (hi : a.val i = .inr s) :
    ∃! θ : Henry.SemiSimplexCategory.mk p.last.val ⟶ Henry.SemiSimplexCategory.mk s.val.1,
      K.map θ.op s.val.2 = p.face := by
  apply (vertex_range_subset_iff_existsUnique_faceMap hK p.face s.val.2).mp
  rintro v ⟨j, rfl⟩
  have hpi := mixedExterior_after_prefix a p i s hi
  have hj : (initialSegmentInclusion p.last).hom.toOrderHom j ≤ p.last := by
    change j.val ≤ p.last.val
    omega
  have hb := a.property.2.1 _ i (lt_of_le_of_lt hj hpi)
  rw [p.vertices j, hi] at hb
  obtain ⟨θ, hθ⟩ := hb
  refine ⟨θ.hom.toOrderHom 0, ?_⟩
  exact (vertex_map θ s.val.2 0).symm.trans
    ((congrArg (fun x => vertex x 0) hθ).trans (vertex_zero (vertex p.face j)))

/-- Every exterior source has dimension at least the original-prefix dimension. -/
theorem mixedOriginalPrefix_dim_le_exterior {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (p : MixedOriginalPrefix a) (i : Fin (n + 1))
    (s : {s : Simplex K // s.2 ∉ L.obj (op (Henry.SemiSimplexCategory.mk s.1))})
    (hi : a.val i = .inr s) : p.last.val ≤ s.val.1 := by
  obtain ⟨θ, _, _⟩ := mixedOriginalPrefix_faceMap_to_exterior hK a p i s hi
  letI : Mono θ.hom := θ.property
  exact SimplexCategory.len_le_of_mono θ.hom

/-- Equality of exterior and prefix dimensions identifies their original simplices. -/
theorem mixedExterior_eq_prefix_of_dim_eq {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (p : MixedOriginalPrefix a) (i : Fin (n + 1))
    (s : {s : Simplex K // s.2 ∉ L.obj (op (Henry.SemiSimplexCategory.mk s.1))})
    (hi : a.val i = .inr s) (hd : s.val.1 = p.last.val) :
    s.val = (⟨p.last.val, p.face⟩ : Simplex K) := by
  rcases s with ⟨⟨m, x⟩, hxL⟩
  change m = p.last.val at hd
  subst m
  obtain ⟨θ, hθ, _⟩ := mixedOriginalPrefix_faceMap_to_exterior hK a p i ⟨⟨_, x⟩, hxL⟩ hi
  letI : Mono θ.hom := θ.property
  have hid : θ = 𝟙 _ := by
    apply WideSubcategory.hom_ext
    exact SimplexCategory.eq_id_of_mono θ.hom
  rw [hid] at hθ
  simp only [op_id, Functor.map_id_apply] at hθ
  exact congrArg (fun y => (⟨p.last.val, y⟩ : Simplex K)) hθ

/-- If the prefix barycentre is absent, every exterior source has strictly larger dimension. -/
theorem mixedOriginalPrefix_dim_lt_exterior_of_absent {K : SemiSSet.{u}}
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} {n : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (p : MixedOriginalPrefix a)
    (hp : p.face ∉ L.obj (op (Henry.SemiSimplexCategory.mk p.last.val)))
    (hv : (Sum.inr ⟨⟨p.last.val, p.face⟩, hp⟩ : MixedVertex K L) ∉ Set.range a.val)
    (i : Fin (n + 1))
    (s : {s : Simplex K // s.2 ∉ L.obj (op (Henry.SemiSimplexCategory.mk s.1))})
    (hi : a.val i = .inr s) : p.last.val < s.val.1 := by
  have hle := mixedOriginalPrefix_dim_le_exterior hK a p i s hi
  by_contra hn
  have heq : s.val.1 = p.last.val := by omega
  have hs : s = ⟨⟨p.last.val, p.face⟩, hp⟩ :=
    Subtype.ext (mixedExterior_eq_prefix_of_dim_eq hK a p i s hi heq)
  exact hv ⟨i, hi.trans (congrArg Sum.inr hs)⟩

/-- An occurring prefix barycentre is the first exterior entry. -/
theorem mixedPrefixBarycenter_index {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} {n : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk n)))
    (p : MixedOriginalPrefix a)
    (hp : p.face ∉ L.obj (op (Henry.SemiSimplexCategory.mk p.last.val)))
    (i : Fin (n + 1))
    (hi : a.val i = .inr ⟨⟨p.last.val, p.face⟩, hp⟩) :
    i.val = p.last.val + 1 := by
  have hpi := mixedExterior_after_prefix a p i _ hi
  by_contra hn
  have hlt : p.last.val + 1 < i.val := by
    have hlt : p.last.val < i.val := hpi
    omega
  let j : Fin (n + 1) := ⟨p.last.val + 1, lt_trans hlt i.isLt⟩
  cases hj : a.val j with
  | inl w =>
    have hjp := (p.maximal j).mp ⟨w, hj⟩
    have hval : j.val ≤ p.last.val := hjp
    dsimp only [j] at hval
    omega
  | inr s =>
    have hd := mixedOriginalPrefix_dim_le_exterior hK a p j s hj
    have hb := a.property.2.1 j i (by change j.val < i.val; exact hlt)
    simp only [hj, hi, MixedVertex.Precedes] at hb
    have hdim : s.val.1 < p.last.val := hb.1
    omega

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.mixedOriginalPrefix_faceMap_to_exterior
#print axioms HomotopyHypothesis.Approximation.Zeeman.mixedPrefixBarycenter_index
