import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Horn.Attachment.HornAttachmentStatementProof
import HomotopyHypothesis.Approximation.Zeeman.HornFaces
import HomotopyHypothesis.Approximation.Zeeman.MixedCells
import HomotopyHypothesis.Approximation.Zeeman.MixedDeletion
import HomotopyHypothesis.Approximation.Zeeman.MixedFaceOrder
import HomotopyHypothesis.Approximation.Zeeman.MixedFlags
import HomotopyHypothesis.Approximation.Zeeman.MixedOriginalPrefix
import HomotopyHypothesis.Approximation.Zeeman.MixedPairInsertionStatement
import HomotopyHypothesis.Approximation.Zeeman.MixedPairing
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
/-!
# Stages of the mixed relative collapse

A stage contains the derived end and all faces of the upper partners
already adjoined. Pairs are ordered first by original-prefix dimension
and then by lower-cell dimension. Adjoining a pair after every smaller
pair and before every larger pair meets its upper cell in exactly the
horn opposite the paired lower face.
-/

universe u

open CategoryTheory Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- Strict lexicographic order on the two dimensions of a mixed pair. -/
def MixedPairPrecedes {K : SemiSSet.{u}} {L : Subfunctor K}
    (c d : MixedLowerCell K L) : Prop :=
  c.prefix.last.val < d.prefix.last.val ∨
    (c.prefix.last.val = d.prefix.last.val ∧ c.val.1 < d.val.1)

/-- A pair occurring as a face is either the same pair or a strictly earlier pair. -/
theorem mixedPair_face_precedes_or_eq {K : SemiSSet.{u}}
    (hI : MixedPairInsertionStatement.{u}) (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} (c d : MixedLowerCell K L)
    (hf : (∃ θ : Henry.SemiSimplexCategory.mk c.val.1 ⟶
        Henry.SemiSimplexCategory.mk (d.val.1 + 1),
        (mixedFlags K L).map θ.op (mixedUpper hI hK d) = c.val.2) ∨
      (∃ θ : Henry.SemiSimplexCategory.mk (c.val.1 + 1) ⟶
        Henry.SemiSimplexCategory.mk (d.val.1 + 1),
        (mixedFlags K L).map θ.op (mixedUpper hI hK d) = mixedUpper hI hK c)) :
    MixedPairPrecedes c d ∨ c = d := by
  rcases mixedPair_face_order hI hK c d hf with hp | ⟨hp, hn, he⟩
  · exact Or.inl (Or.inl hp)
  · rcases lt_or_eq_of_le hn with hn | hn
    · exact Or.inl (Or.inr ⟨hp, hn⟩)
    · exact Or.inr (he hn)

/-- The derived end together with faces of the upper partners indexed by a set of pairs. -/
noncomputable def mixedStage {K : SemiSSet.{u}}
    (hI : MixedPairInsertionStatement.{u}) (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} (T : Set (MixedLowerCell K L)) : Subfunctor (mixedFlags K L) where
  obj X a := a ∈ (Subfunctor.range (mixedDerivedInclusion L)).obj X ∨
    ∃ c ∈ T, ∃ θ : X.unop ⟶ Henry.SemiSimplexCategory.mk (c.val.1 + 1),
      (mixedFlags K L).map θ.op (mixedUpper hI hK c) = a
  map f := by
    rintro a (ha | ⟨c, hc, θ, hθ⟩)
    · exact Or.inl ((Subfunctor.range (mixedDerivedInclusion L)).map f ha)
    · refine Or.inr ⟨c, hc, f.unop ≫ θ, ?_⟩
      rw [op_comp, Functor.map_comp]
      exact congrArg ((mixedFlags K L).map f) hθ

/-- Adding more pairs enlarges the stage. -/
theorem mixedStage_mono {K : SemiSSet.{u}}
    (hI : MixedPairInsertionStatement.{u}) (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} {T U : Set (MixedLowerCell K L)} (hTU : T ⊆ U) :
    mixedStage hI hK T ≤ mixedStage hI hK U := by
  intro X a ha
  rcases ha with ha | ⟨c, hc, θ, hθ⟩
  · exact Or.inl ha
  · exact Or.inr ⟨c, hTU hc, θ, hθ⟩

/-- The stage with no pairs is the derived end. -/
theorem mixedStage_empty {K : SemiSSet.{u}}
    (hI : MixedPairInsertionStatement.{u}) (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} :
    mixedStage hI hK (∅ : Set (MixedLowerCell K L)) =
      Subfunctor.range (mixedDerivedInclusion L) := by
  ext X a
  constructor
  · rintro (ha | ⟨c, hc, _, _⟩)
    · exact ha
    · exact hc.elim
  · exact Or.inl

/-- An adjoined pair contributes its upper member. -/
theorem mixedStage_upper_mem {K : SemiSSet.{u}}
    (hI : MixedPairInsertionStatement.{u}) (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} (T : Set (MixedLowerCell K L))
    (c : MixedLowerCell K L) (hc : c ∈ T) :
    mixedUpper hI hK c ∈ (mixedStage hI hK T).obj
      (op (Henry.SemiSimplexCategory.mk (c.val.1 + 1))) := by
  exact Or.inr ⟨c, hc, 𝟙 _, by simp⟩

/-- An adjoined pair also contributes its lower face. -/
theorem mixedStage_lower_mem {K : SemiSSet.{u}}
    (hI : MixedPairInsertionStatement.{u}) (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} (T : Set (MixedLowerCell K L))
    (c : MixedLowerCell K L) (hc : c ∈ T) :
    c.val.2 ∈ (mixedStage hI hK T).obj (op (Henry.SemiSimplexCategory.mk c.val.1)) := by
  exact Or.inr ⟨c, hc, faceOmitting c.prefix.last.succ, mixedUpper_omit hI hK c⟩

/-- Inserting a pair adjoins the range of its upper simplex. -/
theorem mixedStage_insert {K : SemiSSet.{u}}
    (hI : MixedPairInsertionStatement.{u}) (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} (T : Set (MixedLowerCell K L)) (c : MixedLowerCell K L) :
    mixedStage hI hK (Set.insert c T) = mixedStage hI hK T ⊔
      Subfunctor.range (uliftYonedaEquiv.symm (mixedUpper hI hK c)) := by
  ext X a
  constructor
  · rintro (ha | ⟨d, hd, θ, hθ⟩)
    · exact Or.inl (Or.inl ha)
    · rcases hd with rfl | hd
      · exact Or.inr ⟨ULift.up θ, hθ⟩
      · exact Or.inl (Or.inr ⟨d, hd, θ, hθ⟩)
  · rintro (ha | ⟨θ, hθ⟩)
    · rcases ha with ha | ⟨d, hd, θ, hθ⟩
      · exact Or.inl ha
      · exact Or.inr ⟨d, Or.inr hd, θ, hθ⟩
    · exact Or.inr ⟨c, Or.inl rfl, θ.down, hθ⟩

/-- A pair not yet adjoined has no lower member in a stage containing no later pairs. -/
theorem mixedStage_lower_not_mem {K : SemiSSet.{u}}
    (hI : MixedPairInsertionStatement.{u}) (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} (T : Set (MixedLowerCell K L)) (c : MixedLowerCell K L)
    (hc : c ∉ T) (hafter : ∀ d ∈ T, ¬ MixedPairPrecedes c d) :
    c.val.2 ∉ (mixedStage hI hK T).obj (op (Henry.SemiSimplexCategory.mk c.val.1)) := by
  rintro (ha | ⟨d, hd, θ, hθ⟩)
  · exact mixedLower_not_in_derived hK c ha
  · rcases mixedPair_face_precedes_or_eq hI hK c d (Or.inl ⟨θ, hθ⟩) with hp | he
    · exact hafter d hd hp
    · exact hc (he.symm ▸ hd)

/-- The upper member is absent under the same ordering conditions. -/
theorem mixedStage_upper_not_mem {K : SemiSSet.{u}}
    (hI : MixedPairInsertionStatement.{u}) (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} (T : Set (MixedLowerCell K L)) (c : MixedLowerCell K L)
    (hc : c ∉ T) (hafter : ∀ d ∈ T, ¬ MixedPairPrecedes c d) :
    mixedUpper hI hK c ∉ (mixedStage hI hK T).obj
      (op (Henry.SemiSimplexCategory.mk (c.val.1 + 1))) := by
  rintro (ha | ⟨d, hd, θ, hθ⟩)
  · exact mixedUpper_not_in_derived hI hK c ha
  · rcases mixedPair_face_precedes_or_eq hI hK c d (Or.inr ⟨θ, hθ⟩) with hp | he
    · exact hafter d hd hp
    · exact hc (he.symm ▸ hd)

/-- Every horn face is in a stage containing all earlier pairs. -/
theorem mixedHornFace_mem_stage {K : SemiSSet.{u}}
    (hI : MixedPairInsertionStatement.{u}) (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} (T : Set (MixedLowerCell K L)) (c : MixedLowerCell K L)
    (hbefore : ∀ d, MixedPairPrecedes d c → d ∈ T) {m : ℕ}
    (θ : Henry.SemiSimplexCategory.mk m ⟶ Henry.SemiSimplexCategory.mk (c.val.1 + 1))
    (hθ : ULift.up θ ∈ (horn.{u} (c.val.1 + 1) c.prefix.last.succ).obj
      (op (Henry.SemiSimplexCategory.mk m))) :
    (mixedFlags K L).map θ.op (mixedUpper hI hK c) ∈
      (mixedStage hI hK T).obj (op (Henry.SemiSimplexCategory.mk m)) := by
  classical
  let a := (mixedFlags K L).map θ.op (mixedUpper hI hK c)
  have hne := (mixedUpper_horn_face_iff hI hK c θ).mp hθ
  by_cases ha : a ∈ Set.range ((mixedDerivedInclusion L).app
      (op (Henry.SemiSimplexCategory.mk m)))
  · exact Or.inl ha
  obtain ⟨d, hd | hd⟩ := mixedPair_classification hI hK ⟨m, a⟩ ha
  · have hdim : m = d.val.1 := congrArg Sigma.fst hd
    subst m
    have he : (mixedFlags K L).map θ.op (mixedUpper hI hK c) = d.val.2 :=
      eq_of_heq (Sigma.mk.inj hd).2
    rcases mixedPair_face_precedes_or_eq hI hK d c (Or.inl ⟨θ, he⟩) with hp | heq
    · rw [he]
      exact mixedStage_lower_mem hI hK T d (hbefore d hp)
    · subst d
      exact False.elim (hne.2 hd)
  · have hdim : m = d.val.1 + 1 := congrArg Sigma.fst hd
    subst m
    have he : (mixedFlags K L).map θ.op (mixedUpper hI hK c) = mixedUpper hI hK d :=
      eq_of_heq (Sigma.mk.inj hd).2
    rcases mixedPair_face_precedes_or_eq hI hK d c (Or.inr ⟨θ, he⟩) with hp | heq
    · rw [he]
      exact mixedStage_upper_mem hI hK T d (hbefore d hp)
    · subst d
      exact False.elim (hne.1 hd)

/-- The preceding stage intersects the next upper simplex in exactly its attachment horn. -/
theorem mixedStage_horn_preimage {K : SemiSSet.{u}}
    (hI : MixedPairInsertionStatement.{u}) (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} (T : Set (MixedLowerCell K L)) (c : MixedLowerCell K L)
    (hc : c ∉ T) (hbefore : ∀ d, MixedPairPrecedes d c → d ∈ T)
    (hafter : ∀ d ∈ T, ¬ MixedPairPrecedes c d) :
    (mixedStage hI hK T).preimage (uliftYonedaEquiv.symm (mixedUpper hI hK c)) =
      horn (c.val.1 + 1) c.prefix.last.succ := by
  ext X θ
  change ((mixedFlags K L).map θ.down.op (mixedUpper hI hK c) ∈
    (mixedStage hI hK T).obj X) ↔ θ ∈ (horn (c.val.1 + 1) c.prefix.last.succ).obj X
  constructor
  · intro hmem
    apply (mixedUpper_horn_face_iff hI hK c θ.down).mpr
    constructor
    · intro he
      have hprop := congrArg (fun s : Simplex (mixedFlags K L) =>
        s.2 ∈ (mixedStage hI hK T).obj (op (Henry.SemiSimplexCategory.mk s.1))) he
      exact mixedStage_upper_not_mem hI hK T c hc hafter (Eq.mp hprop hmem)
    · intro he
      have hprop := congrArg (fun s : Simplex (mixedFlags K L) =>
        s.2 ∈ (mixedStage hI hK T).obj (op (Henry.SemiSimplexCategory.mk s.1))) he
      exact mixedStage_lower_not_mem hI hK T c hc hafter (Eq.mp hprop hmem)
  · exact mixedHornFace_mem_stage hI hK T c hbefore θ.down

/-- Adjoining the next upper simplex is an elementary anodyne attachment. -/
theorem mixedStage_attach_anodyne {K : SemiSSet.{u}}
    (hI : MixedPairInsertionStatement.{u}) (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} (T : Set (MixedLowerCell K L)) (c : MixedLowerCell K L)
    (hc : c ∉ T) (hbefore : ∀ d, MixedPairPrecedes d c → d ∈ T)
    (hafter : ∀ d ∈ T, ¬ MixedPairPrecedes c d) :
    anodyne (Subfunctor.homOfLe (show mixedStage hI hK T ≤ mixedStage hI hK T ⊔
      Subfunctor.range (uliftYonedaEquiv.symm (mixedUpper hI hK c)) from le_sup_left)) := by
  exact Horn.Attachment.hornAttachmentStatement_proof (mixedStage hI hK T)
    c.val.1 c.prefix.last.succ (uliftYonedaEquiv.symm (mixedUpper hI hK c))
    inferInstance (mixedStage_horn_preimage hI hK T c hc hbefore hafter)

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.mixedStage_horn_preimage
#print axioms HomotopyHypothesis.Approximation.Zeeman.mixedStage_attach_anodyne
