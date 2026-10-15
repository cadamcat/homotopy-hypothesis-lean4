import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.MixedDeletion
import HomotopyHypothesis.Approximation.Zeeman.MixedFlags
import HomotopyHypothesis.Approximation.Zeeman.MixedOriginalPrefix
import HomotopyHypothesis.Approximation.Zeeman.MixedPairInsertionStatement
import HomotopyHypothesis.Approximation.Zeeman.MixedPrefixIncidence
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
/-!
# Pairs of mixed cells

A lower cell has an original prefix outside the fixed subcomplex and does
not contain that prefix's barycentre. Inserting the barycentre produces its
upper partner. Deletion recovers the lower cell, and every cell outside the
derived end belongs to one of these pairs.
-/

universe u

open CategoryTheory Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- A lower mixed cell lacks the barycentre of its exterior original prefix. -/
def IsMixedLower {K : SemiSSet.{u}} {L : Subfunctor K} {n : ℕ}
    (a : (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk n))) : Prop :=
  ∃ (p : MixedOriginalPrefix a)
    (hp : p.face ∉ L.obj (op (Henry.SemiSimplexCategory.mk p.last.val))),
    (Sum.inr ⟨⟨p.last.val, p.face⟩, hp⟩ : MixedVertex K L) ∉ Set.range a.val

/-- The dimension and tuple of each lower mixed cell. -/
abbrev MixedLowerCell (K : SemiSSet.{u}) (L : Subfunctor K) :=
  {s : Simplex (mixedFlags K L) // IsMixedLower s.2}

/-- There are finitely many lower cells over a finite original complex. -/
theorem mixedLowerCell_finite {K : SemiSSet.{u}} (hK : K.IsFinite) (L : Subfunctor K) :
    Finite (MixedLowerCell K L) := by
  haveI : Finite (Simplex (mixedFlags K L)) := simplex_finite (mixedFlags_isFinite hK L)
  infer_instance

/-- Choose the original prefix recorded by the lower-cell property. -/
noncomputable def MixedLowerCell.prefix {K : SemiSSet.{u}} {L : Subfunctor K}
    (c : MixedLowerCell K L) : MixedOriginalPrefix c.val.2 :=
  Classical.choose c.property

/-- The chosen lower-cell prefix lies outside the fixed subcomplex. -/
theorem MixedLowerCell.prefix_outside {K : SemiSSet.{u}} {L : Subfunctor K}
    (c : MixedLowerCell K L) :
    c.prefix.face ∉ L.obj (op (Henry.SemiSimplexCategory.mk c.prefix.last.val)) :=
  Classical.choose (Classical.choose_spec c.property)

/-- The barycentre paired with a lower cell. -/
noncomputable def MixedLowerCell.barycenter {K : SemiSSet.{u}} {L : Subfunctor K}
    (c : MixedLowerCell K L) : MixedVertex K L :=
  .inr ⟨⟨c.prefix.last.val, c.prefix.face⟩, c.prefix_outside⟩

/-- The paired barycentre is absent from its lower cell. -/
theorem MixedLowerCell.barycenter_absent {K : SemiSSet.{u}} {L : Subfunctor K}
    (c : MixedLowerCell K L) : c.barycenter ∉ Set.range c.val.2.val :=
  Classical.choose_spec (Classical.choose_spec c.property)

/-- Prefix choice agrees with every other maximal original prefix. -/
theorem MixedLowerCell.prefix_eq {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} (c : MixedLowerCell K L) (p : MixedOriginalPrefix c.val.2) :
    c.prefix = p := mixedOriginalPrefix_unique hK c.prefix p

/-- Insert the absent prefix barycentre to obtain the upper partner. -/
noncomputable def mixedUpper {K : SemiSSet.{u}} (hI : MixedPairInsertionStatement.{u})
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} (c : MixedLowerCell K L) :
    (mixedFlags K L).obj (op (Henry.SemiSimplexCategory.mk (c.val.1 + 1))) :=
  ⟨Fin.insertNth c.prefix.last.succ c.barycenter c.val.2.val,
    hI hK L c.val.1 c.val.2 c.prefix c.prefix_outside c.barycenter_absent⟩

/-- Insertion preserves the original prefix and its original face. -/
noncomputable def mixedUpperPrefix {K : SemiSSet.{u}} (hI : MixedPairInsertionStatement.{u})
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} (c : MixedLowerCell K L) :
    MixedOriginalPrefix (mixedUpper hI hK c) := by
  refine ⟨c.prefix.last.castSucc, c.prefix.face, ?_, ?_⟩
  · intro i
    have hi : ((initialSegmentInclusion c.prefix.last).hom.toOrderHom i).castSucc <
        c.prefix.last.succ := by
      change i.val < c.prefix.last.val + 1
      exact i.isLt
    have he : c.prefix.last.succ.succAbove
        ((initialSegmentInclusion c.prefix.last).hom.toOrderHom i) =
        (initialSegmentInclusion c.prefix.last.castSucc).hom.toOrderHom i := by
      rw [Fin.succAbove_of_castSucc_lt _ _ hi]
      rfl
    change Fin.insertNth (α := fun _ => MixedVertex K L)
      c.prefix.last.succ c.barycenter c.val.2.val
      ((initialSegmentInclusion c.prefix.last.castSucc).hom.toOrderHom i) = _
    rw [← he, Fin.insertNth_apply_succAbove]
    exact c.prefix.vertices i
  · intro i
    rcases Fin.eq_self_or_eq_succAbove c.prefix.last.succ i with rfl | ⟨j, rfl⟩
    · change (∃ w, Fin.insertNth (α := fun _ => MixedVertex K L)
        c.prefix.last.succ c.barycenter c.val.2.val
        c.prefix.last.succ = Sum.inl w) ↔ c.prefix.last.succ ≤ c.prefix.last.castSucc
      simp only [Fin.insertNth_apply_same, MixedLowerCell.barycenter, Sum.inr_ne_inl,
        exists_false, false_iff]
      change ¬ c.prefix.last.val + 1 ≤ c.prefix.last.val
      omega
    · change (∃ w, Fin.insertNth (α := fun _ => MixedVertex K L)
        c.prefix.last.succ c.barycenter c.val.2.val
        (c.prefix.last.succ.succAbove j) = Sum.inl w) ↔
          c.prefix.last.succ.succAbove j ≤ c.prefix.last.castSucc
      rw [Fin.insertNth_apply_succAbove, c.prefix.maximal]
      change j.val ≤ c.prefix.last.val ↔
        (c.prefix.last.succ.succAbove j).val ≤ c.prefix.last.val
      unfold Fin.succAbove
      split_ifs with hj
      · rfl
      · have hj' : c.prefix.last.val + 1 ≤ j.val := le_of_not_gt hj
        simp only [Fin.val_succ]
        omega

/-- The new upper cell contains the paired barycentre at the insertion index. -/
theorem mixedUpper_barycenter {K : SemiSSet.{u}} (hI : MixedPairInsertionStatement.{u})
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} (c : MixedLowerCell K L) :
    (mixedUpper hI hK c).val c.prefix.last.succ = c.barycenter :=
  Fin.insertNth_apply_same (α := fun _ => MixedVertex K L)
    c.prefix.last.succ c.barycenter c.val.2.val

/-- Deleting the inserted barycentre recovers the lower cell. -/
theorem mixedUpper_omit {K : SemiSSet.{u}} (hI : MixedPairInsertionStatement.{u})
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} (c : MixedLowerCell K L) :
    mixedOmit (mixedUpper hI hK c) c.prefix.last.succ = c.val.2 := by
  apply Subtype.ext
  exact Fin.removeNth_insertNth (α := fun _ => MixedVertex K L)
    c.prefix.last.succ c.barycenter c.val.2.val

/-- A lower cell lies outside the derived end. -/
theorem mixedLower_not_in_derived {K : SemiSSet.{u}} (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} (c : MixedLowerCell K L) :
    c.val.2 ∉ Set.range ((mixedDerivedInclusion L).app
      (op (Henry.SemiSimplexCategory.mk c.val.1))) := by
  intro hc
  exact c.prefix_outside ((mixedDerived_mem_range_iff_prefix_mem hK c.val.2 c.prefix).mp hc)

/-- An upper partner also lies outside the derived end. -/
theorem mixedUpper_not_in_derived {K : SemiSSet.{u}} (hI : MixedPairInsertionStatement.{u})
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} (c : MixedLowerCell K L) :
    mixedUpper hI hK c ∉ Set.range ((mixedDerivedInclusion L).app
      (op (Henry.SemiSimplexCategory.mk (c.val.1 + 1)))) := by
  intro hc
  exact c.prefix_outside ((mixedDerived_mem_range_iff_prefix_mem hK
    (mixedUpper hI hK c) (mixedUpperPrefix hI hK c)).mp hc)

/-- An upper partner cannot itself be a lower cell. -/
theorem mixedUpper_not_lower {K : SemiSSet.{u}} (hI : MixedPairInsertionStatement.{u})
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} (c : MixedLowerCell K L) :
    ¬ IsMixedLower (mixedUpper hI hK c) := by
  rintro ⟨p, hp, hv⟩
  have he := mixedOriginalPrefix_unique hK p (mixedUpperPrefix hI hK c)
  subst p
  exact hv ⟨c.prefix.last.succ, mixedUpper_barycenter hI hK c⟩

/-- The upper partner, with its dimension retained. -/
noncomputable def mixedUpperSimplex {K : SemiSSet.{u}} (hI : MixedPairInsertionStatement.{u})
    (hK : K.IsSimplicialComplex) {L : Subfunctor K} (c : MixedLowerCell K L) :
    Simplex (mixedFlags K L) := ⟨c.val.1 + 1, mixedUpper hI hK c⟩

/-- Every mixed simplex outside the derived end is a lower cell or an upper partner. -/
theorem mixedPair_classification {K : SemiSSet.{u}} (hI : MixedPairInsertionStatement.{u})
    (hK : K.IsSimplicialComplex) {L : Subfunctor K}
    (s : Simplex (mixedFlags K L))
    (hs : s.2 ∉ Set.range ((mixedDerivedInclusion L).app
      (op (Henry.SemiSimplexCategory.mk s.1)))) :
    ∃ c : MixedLowerCell K L, s = c.val ∨ s = mixedUpperSimplex hI hK c := by
  classical
  rcases s with ⟨n, a⟩
  by_cases ha : IsMixedLower a
  · exact ⟨⟨⟨n, a⟩, ha⟩, Or.inl rfl⟩
  obtain ⟨p, hp⟩ := exists_exterior_originalPrefix hK a hs
  have hv : (Sum.inr ⟨⟨p.last.val, p.face⟩, hp⟩ : MixedVertex K L) ∈
      Set.range a.val := by
    by_contra hv
    exact ha ⟨p, hp, hv⟩
  obtain ⟨k, hk⟩ := hv
  have hpk := mixedExterior_after_prefix a p k _ hk
  cases n with
  | zero =>
    have hp0 := p.last.isLt
    have hk0 := k.isLt
    change p.last.val < 1 at hp0
    change k.val < 1 at hk0
    change p.last.val < k.val at hpk
    omega
  | succ n =>
    let b := mixedOmit a k
    let q := mixedOmitOriginalPrefix a p k hpk
    have hq : q.face ∉ L.obj (op (Henry.SemiSimplexCategory.mk q.last.val)) := hp
    have hb : IsMixedLower b :=
      ⟨q, hq, mixedOmit_prefixBarycenter_missing a p hp k hk⟩
    let c : MixedLowerCell K L := ⟨⟨n, b⟩, hb⟩
    have hc : c.prefix = q := c.prefix_eq hK q
    have hlast : c.prefix.last.succ = q.last.succ := congrArg (fun r => r.last.succ) hc
    have hbary : c.barycenter = (Sum.inr ⟨⟨p.last.val, p.face⟩, hp⟩ : MixedVertex K L) := by
      apply congrArg Sum.inr
      apply Subtype.ext
      exact congrArg (fun r : MixedOriginalPrefix b => (⟨r.last.val, r.face⟩ : Simplex K)) hc
    have hu : mixedUpper hI hK c = a := by
      apply Subtype.ext
      change Fin.insertNth (α := fun _ => MixedVertex K L) c.prefix.last.succ
        c.barycenter (mixedOmit a k).val = a.val
      rw [hlast, hbary]
      exact mixedOmit_prefixBarycenter_reinsert hK a p hp k hpk hk
    exact ⟨c, Or.inr (congrArg (fun x => (⟨n + 1, x⟩ : Simplex (mixedFlags K L))) hu.symm)⟩

/-- Distinct lower cells have distinct upper partners. -/
theorem mixedUpperSimplex_injective {K : SemiSSet.{u}}
    (hI : MixedPairInsertionStatement.{u}) (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} : Function.Injective (mixedUpperSimplex hI hK (L := L)) := by
  intro c d h
  have hdim : c.val.1 = d.val.1 := Nat.succ.inj (congrArg Sigma.fst h)
  rcases c with ⟨⟨n, a⟩, ha⟩
  rcases d with ⟨⟨m, b⟩, hb⟩
  change n = m at hdim
  subst m
  let c : MixedLowerCell K L := ⟨⟨n, a⟩, ha⟩
  let d : MixedLowerCell K L := ⟨⟨n, b⟩, hb⟩
  have hu : mixedUpper hI hK c = mixedUpper hI hK d := eq_of_heq (Sigma.mk.inj h).2
  let p := mixedUpperPrefix hI hK c
  let q := mixedUpperPrefix hI hK d
  have hlast : c.prefix.last.castSucc = d.prefix.last.castSucc := by
    apply le_antisymm
    · exact (q.maximal p.last).mp (hu ▸ p.last_original)
    · exact (p.maximal q.last).mp (hu.symm ▸ q.last_original)
  have hk : c.prefix.last.succ = d.prefix.last.succ := by
    apply Fin.ext
    exact congrArg (fun i => i.val + 1) hlast
  have hab : a = b := calc
    a = mixedOmit (mixedUpper hI hK c) c.prefix.last.succ :=
      (mixedUpper_omit hI hK c).symm
    _ = mixedOmit (mixedUpper hI hK d) d.prefix.last.succ := by rw [hu, hk]
    _ = b := mixedUpper_omit hI hK d
  apply Subtype.ext
  exact congrArg (fun x => (⟨n, x⟩ : Simplex (mixedFlags K L))) hab

/-- No upper partner coincides with a lower cell, even across dimensions. -/
theorem mixedUpperSimplex_ne_lower {K : SemiSSet.{u}}
    (hI : MixedPairInsertionStatement.{u}) (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} (c d : MixedLowerCell K L) :
    mixedUpperSimplex hI hK c ≠ d.val := by
  intro h
  have hd : IsMixedLower (mixedUpperSimplex hI hK c).2 :=
    h.symm ▸ d.property
  exact mixedUpper_not_lower hI hK c hd

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.mixedUpper_omit
#print axioms HomotopyHypothesis.Approximation.Zeeman.mixedUpper_not_lower
#print axioms HomotopyHypothesis.Approximation.Zeeman.mixedPair_classification
#print axioms HomotopyHypothesis.Approximation.Zeeman.mixedUpperSimplex_injective
