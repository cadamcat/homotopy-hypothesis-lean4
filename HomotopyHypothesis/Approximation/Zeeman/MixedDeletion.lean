import Mathlib.Data.Fin.Tuple.Basic
import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.MixedFlags
import HomotopyHypothesis.Approximation.Zeeman.MixedOriginalPrefix
import HomotopyHypothesis.Approximation.Zeeman.MixedPrefixIncidence
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
/-!
# Deleting the prefix barycentre from a mixed flag

Face restriction omits an entry of a mixed tuple. Omitting an exterior
entry preserves the original prefix, and the omitted entry is absent from
the new tuple. When that entry is the prefix barycentre, reinserting it
at the new prefix's end recovers the original tuple.
-/

universe u

open CategoryTheory Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- The face inclusion omitting one vertex. -/
def faceOmitting {n : ℕ} (k : Fin (n + 2)) :
    Henry.SemiSimplexCategory.mk n ⟶ Henry.SemiSimplexCategory.mk (n + 1) :=
  ⟨SimplexCategory.δ k, by
    change Mono (SimplexCategory.δ k)
    rw [SimplexCategory.mono_iff_injective]
    exact (Fin.succAboveOrderEmb k).injective⟩

/-- Omit a vertex from a mixed flag by face restriction. -/
def mixedOmit {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk (n + 1))))
    (k : Fin (n + 2)) : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk n)) :=
  (mixedFlags K L).map (faceOmitting k).op a

/-- Face restriction removes the specified tuple entry. -/
theorem mixedOmit_val {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk (n + 1))))
    (k : Fin (n + 2)) : (mixedOmit a k).val = Fin.removeNth k a.val := rfl

/-- Reinserting the omitted entry recovers the original tuple. -/
theorem mixedOmit_reinsert {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk (n + 1))))
    (k : Fin (n + 2)) : Fin.insertNth k (a.val k) (mixedOmit a k).val = a.val :=
  Fin.insertNth_self_removeNth k a.val

/-- The omitted vertex is absent from the remaining flag. -/
theorem mixedOmit_missing {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk (n + 1))))
    (k : Fin (n + 2)) : a.val k ∉ Set.range (mixedOmit a k).val := by
  rintro ⟨i, hi⟩
  change a.val (k.succAbove i) = a.val k at hi
  exact Fin.succAbove_ne k i (a.property.1 hi)

/-- Omitting an entry after the original prefix preserves its maximal original-face data. -/
def mixedOmitOriginalPrefix {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk (n + 1))))
    (p : MixedOriginalPrefix a) (k : Fin (n + 2)) (hk : p.last < k) :
    MixedOriginalPrefix (mixedOmit a k) := by
  let j : Fin (n + 1) := ⟨p.last.val, by
    have hl : p.last.val < k.val := hk
    have hkn := k.isLt
    omega⟩
  refine ⟨j, p.face, ?_, ?_⟩
  · intro i
    have hi : ((initialSegmentInclusion j).hom.toOrderHom i).castSucc < k := by
      change i.val < k.val
      have hil := i.isLt
      have hl : p.last.val < k.val := hk
      change i.val < p.last.val + 1 at hil
      omega
    change a.val (k.succAbove ((initialSegmentInclusion j).hom.toOrderHom i)) =
      .inl (vertex p.face i)
    rw [Fin.succAbove_of_castSucc_lt _ _ hi]
    exact p.vertices i
  · intro i
    change (∃ w, a.val (k.succAbove i) = .inl w) ↔ i ≤ j
    rw [p.maximal]
    change (k.succAbove i).val ≤ p.last.val ↔ i.val ≤ p.last.val
    unfold Fin.succAbove
    split_ifs with h
    · rfl
    · have hnot : k ≤ i.castSucc := le_of_not_gt h
      have hl : p.last.val < k.val := hk
      change k.val ≤ i.val at hnot
      simp only [Fin.val_succ]
      omega

/-- The original-prefix dimension is unchanged after deleting an exterior entry. -/
theorem mixedOmitOriginalPrefix_last_val {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk (n + 1))))
    (p : MixedOriginalPrefix a) (k : Fin (n + 2)) (hk : p.last < k) :
    (mixedOmitOriginalPrefix a p k hk).last.val = p.last.val := rfl

/-- Deleting an exterior entry leaves the flag outside the derived end when its prefix is outside L. -/
theorem mixedOmit_not_in_derived {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} {n : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk (n + 1))))
    (p : MixedOriginalPrefix a) (k : Fin (n + 2)) (hk : p.last < k)
    (hp : p.face ∉ L.obj (op (Henry.SemiSimplexCategory.mk p.last.val))) :
    mixedOmit a k ∉ Set.range
      ((mixedDerivedInclusion L).app (op (Henry.SemiSimplexCategory.mk n))) := by
  intro ha
  exact hp ((mixedDerived_mem_range_iff_prefix_mem hK (mixedOmit a k)
    (mixedOmitOriginalPrefix a p k hk)).mp ha)

/-- The prefix barycentre is absent after deleting its occurrence. -/
theorem mixedOmit_prefixBarycenter_missing {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk (n + 1))))
    (p : MixedOriginalPrefix a)
    (hp : p.face ∉ L.obj (op (Henry.SemiSimplexCategory.mk p.last.val)))
    (k : Fin (n + 2)) (hk : a.val k = .inr ⟨⟨p.last.val, p.face⟩, hp⟩) :
    (Sum.inr ⟨⟨p.last.val, p.face⟩, hp⟩ : MixedVertex K L) ∉
      Set.range (mixedOmit a k).val := by
  rw [← hk]
  exact mixedOmit_missing a k

/-- Inserting the deleted prefix barycentre at the new prefix's end recovers the upper tuple. -/
theorem mixedOmit_prefixBarycenter_reinsert {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} {n : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk (n + 1))))
    (p : MixedOriginalPrefix a)
    (hp : p.face ∉ L.obj (op (Henry.SemiSimplexCategory.mk p.last.val)))
    (k : Fin (n + 2)) (hk : p.last < k)
    (hv : a.val k = .inr ⟨⟨p.last.val, p.face⟩, hp⟩) :
    Fin.insertNth (mixedOmitOriginalPrefix a p k hk).last.succ
      (Sum.inr ⟨⟨p.last.val, p.face⟩, hp⟩ : MixedVertex K L) (mixedOmit a k).val = a.val := by
  have hindex : (mixedOmitOriginalPrefix a p k hk).last.succ = k := by
    apply Fin.ext
    change p.last.val + 1 = k.val
    exact (mixedPrefixBarycenter_index hK a p hp k hv).symm
  rw [hindex, ← hv]
  exact mixedOmit_reinsert a k

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.mixedOmitOriginalPrefix
#print axioms HomotopyHypothesis.Approximation.Zeeman.mixedOmit_prefixBarycenter_reinsert
