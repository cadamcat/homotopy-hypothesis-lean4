import Mathlib.Data.Prod.Lex
import Mathlib.Data.Finset.Card
import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Approximation.Zeeman.MixedFlags
import HomotopyHypothesis.Approximation.Zeeman.MixedOriginalPrefix
import HomotopyHypothesis.Approximation.Zeeman.MixedPairInsertionStatement
import HomotopyHypothesis.Approximation.Zeeman.MixedPairing
import HomotopyHypothesis.Approximation.Zeeman.MixedProjection
import HomotopyHypothesis.Approximation.Zeeman.MixedStages
import HomotopyHypothesis.Approximation.Zeeman.RelativeDerived
/-!
# Finite collapse of the mixed relative prism

The pairs of a finite mixed prism can be adjoined in order of their
original-prefix and lower-cell dimensions. Removing a pair of maximal
lexicographic key preserves closure under earlier pairs. Each insertion
is an elementary horn attachment, and all pairs together cover the prism.
-/

universe u

open CategoryTheory Opposite

namespace HomotopyHypothesis.Approximation.Zeeman

open Henry Henry.SemiSSet

/-- The two dimensions of a mixed pair, with lexicographic order. -/
noncomputable def mixedPairKey {K : SemiSSet.{u}} {L : Subfunctor K}
    (c : MixedLowerCell K L) : Lex (ℕ × ℕ) :=
  toLex (c.prefix.last.val, c.val.1)

/-- Strict precedence is exactly strict comparison of the pair keys. -/
theorem mixedPairPrecedes_iff_key_lt {K : SemiSSet.{u}} {L : Subfunctor K}
    (c d : MixedLowerCell K L) :
    MixedPairPrecedes c d ↔ mixedPairKey c < mixedPairKey d := by
  unfold MixedPairPrecedes mixedPairKey
  exact (Prod.Lex.toLex_lt_toLex
    (x := (c.prefix.last.val, c.val.1)) (y := (d.prefix.last.val, d.val.1))).symm

/-- No pair strictly precedes itself. -/
theorem mixedPairPrecedes_irrefl {K : SemiSSet.{u}} {L : Subfunctor K}
    (c : MixedLowerCell K L) : ¬ MixedPairPrecedes c c := by
  intro h
  exact lt_irrefl _ ((mixedPairPrecedes_iff_key_lt c c).mp h)

private theorem anodyne_comp {A B C : SemiSSet.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (hf : anodyne f) (hg : anodyne g) : anodyne (f ≫ g) := by
  unfold anodyne at hf hg ⊢
  exact (hornInclusions.pushouts ⊔ MorphismProperty.isomorphisms SemiSSet.{u}).multiplicativeClosure.comp_mem
    _ _ hf hg

private theorem anodyne_homOfLe_congr {F : SemiSSet.{u}} {A B A' B' : Subfunctor F}
    (hAB : A ≤ B) (hAB' : A' ≤ B') (hA : A = A') (hB : B = B')
    (h : anodyne (Subfunctor.homOfLe hAB)) : anodyne (Subfunctor.homOfLe hAB') := by
  subst A'
  subst B'
  exact h

/-- A finite set of pairs closed under earlier pairs is obtained by finitely many horn attachments. -/
theorem mixedStage_finite_anodyne {K : SemiSSet.{u}}
    (hI : MixedPairInsertionStatement.{u}) (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} (s : Finset (MixedLowerCell K L))
    (hs : ∀ c ∈ s, ∀ d, MixedPairPrecedes d c → d ∈ s) :
    anodyne (Subfunctor.homOfLe (show mixedStage hI hK (∅ : Set (MixedLowerCell K L)) ≤
      mixedStage hI hK (s : Set (MixedLowerCell K L)) from
        mixedStage_mono hI hK (Set.empty_subset _))) := by
  classical
  revert hs
  refine Finset.strongInductionOn s ?_
  intro s ih
  intro hs
  by_cases hempty : s = ∅
  · subst s
    have hid : anodyne (Subfunctor.homOfLe
        (le_refl (mixedStage hI hK (∅ : Set (MixedLowerCell K L))))) := by
      change anodyne (𝟙 _)
      exact .id _
    exact anodyne_homOfLe_congr _ _ rfl (by rw [Finset.coe_empty]) hid
  obtain ⟨c, hc, hmax⟩ := s.exists_max_image mixedPairKey
    (Finset.nonempty_iff_ne_empty.mpr hempty)
  have hafter (d) (hd : d ∈ s) : ¬ MixedPairPrecedes c d := by
    intro hcd
    exact (not_lt_of_ge (hmax d hd)) ((mixedPairPrecedes_iff_key_lt c d).mp hcd)
  have herase : ∀ d ∈ s.erase c, ∀ e, MixedPairPrecedes e d → e ∈ s.erase c := by
    intro d hd e hed
    refine Finset.mem_erase.mpr ⟨?_, hs d (Finset.mem_of_mem_erase hd) e hed⟩
    intro hec
    subst e
    exact hafter d (Finset.mem_of_mem_erase hd) hed
  have hbefore (d) (hdc : MixedPairPrecedes d c) : d ∈ s.erase c := by
    refine Finset.mem_erase.mpr ⟨?_, hs c hc d hdc⟩
    intro hec
    subst d
    exact mixedPairPrecedes_irrefl c hdc
  have hi := ih (s.erase c) (Finset.erase_ssubset hc) herase
  have hj := mixedStage_attach_anodyne hI hK
    (s.erase c : Set (MixedLowerCell K L)) c (by simp)
    hbefore (fun d hd => hafter d (Finset.mem_of_mem_erase hd))
  have hstage : mixedStage hI hK (s : Set (MixedLowerCell K L)) =
      mixedStage hI hK (s.erase c : Set (MixedLowerCell K L)) ⊔
        Subfunctor.range (uliftYonedaEquiv.symm (mixedUpper hI hK c)) := by
    have hinsert : Set.insert c (s.erase c : Set (MixedLowerCell K L)) =
        (s : Set (MixedLowerCell K L)) := by
      ext d
      constructor
      · rintro (rfl | hd)
        · exact hc
        · exact Finset.mem_of_mem_erase hd
      · intro hd
        by_cases hdc : d = c
        · exact Or.inl hdc
        · exact Or.inr (Finset.mem_erase.mpr ⟨hdc, hd⟩)
    rw [← hinsert, mixedStage_insert]
  let hle : mixedStage hI hK (s.erase c : Set (MixedLowerCell K L)) ≤
      mixedStage hI hK (s : Set (MixedLowerCell K L)) :=
    mixedStage_mono hI hK (show (s.erase c : Set (MixedLowerCell K L)) ⊆
      (s : Set (MixedLowerCell K L)) from fun _ hd => Finset.mem_of_mem_erase hd)
  have hj' : anodyne (Subfunctor.homOfLe hle) := by
    exact anodyne_homOfLe_congr _ hle rfl hstage.symm hj
  have hcomp : Subfunctor.homOfLe (show mixedStage hI hK (∅ : Set (MixedLowerCell K L)) ≤
      mixedStage hI hK (s.erase c : Set (MixedLowerCell K L)) from
        mixedStage_mono hI hK (Set.empty_subset _)) ≫ Subfunctor.homOfLe hle =
      Subfunctor.homOfLe (show mixedStage hI hK (∅ : Set (MixedLowerCell K L)) ≤
        mixedStage hI hK (s : Set (MixedLowerCell K L)) from
          mixedStage_mono hI hK (Set.empty_subset _)) := rfl
  rw [← hcomp]
  exact anodyne_comp _ _ hi hj'

/-- All mixed pairs together with the derived end cover the whole prism. -/
theorem mixedStage_univ {K : SemiSSet.{u}}
    (hI : MixedPairInsertionStatement.{u}) (hK : K.IsSimplicialComplex)
    {L : Subfunctor K} : mixedStage hI hK (Set.univ : Set (MixedLowerCell K L)) = ⊤ := by
  classical
  ext X a
  constructor
  · intro _
    trivial
  · intro _
    by_cases ha : a ∈ Set.range ((mixedDerivedInclusion L).app X)
    · exact Or.inl ha
    obtain ⟨c, he | he⟩ := mixedPair_classification hI hK ⟨X.unop.obj.len, a⟩ ha
    · exact Eq.mpr (congrArg (fun s : Simplex (mixedFlags K L) =>
        s.2 ∈ (mixedStage hI hK Set.univ).obj (op (Henry.SemiSimplexCategory.mk s.1))) he)
        (mixedStage_lower_mem hI hK Set.univ c (Set.mem_univ c))
    · exact Eq.mpr (congrArg (fun s : Simplex (mixedFlags K L) =>
        s.2 ∈ (mixedStage hI hK Set.univ).obj (op (Henry.SemiSimplexCategory.mk s.1))) he)
        (mixedStage_upper_mem hI hK Set.univ c (Set.mem_univ c))

/-- The mixed prism collapses onto its relative derived end for a finite complex. -/
theorem mixedDerivedInclusion_anodyne {K : SemiSSet.{u}}
    (hI : MixedPairInsertionStatement.{u}) (hK : K.IsFinite)
    (hKs : K.IsSimplicialComplex) (L : Subfunctor K) :
    anodyne (mixedDerivedInclusion L) := by
  classical
  haveI : Finite (MixedLowerCell K L) := mixedLowerCell_finite hK L
  letI : Fintype (MixedLowerCell K L) := Fintype.ofFinite _
  have hfinite := mixedStage_finite_anodyne hI hKs (Finset.univ : Finset (MixedLowerCell K L))
    (fun _ _ _ _ => Finset.mem_univ _)
  have hinc : anodyne (Subfunctor.homOfLe
      (show Subfunctor.range (mixedDerivedInclusion L) ≤ (⊤ : Subfunctor (mixedFlags K L))
        from le_top)) := by
    have htop : mixedStage hI hKs
        (↑(Finset.univ : Finset (MixedLowerCell K L)) : Set (MixedLowerCell K L)) = ⊤ := by
      rw [Finset.coe_univ, mixedStage_univ]
    exact anodyne_homOfLe_congr _ le_top (mixedStage_empty hI hKs) htop hfinite
  have hto : anodyne (Subfunctor.toRange (mixedDerivedInclusion L)) :=
    .of _ (Or.inr inferInstance)
  have htop : anodyne (Subfunctor.ι (⊤ : Subfunctor (mixedFlags K L))) :=
    .of _ (Or.inr inferInstance)
  have hcomp := anodyne_comp _ _ (anodyne_comp _ _ hto hinc) htop
  simpa only [Category.assoc, Subfunctor.homOfLe_ι, Subfunctor.toRange_ι] using hcomp

/-- The relative derived subdivision with its pinched collapsing mixed prism. -/
noncomputable def relativeDerivedSubdivision {K : SemiSSet.{u}}
    (hI : MixedPairInsertionStatement.{u}) (hK : K.IsFinite)
    (hKs : K.IsSimplicialComplex) (L : Subfunctor K) : RelSubdivision K L :=
  relativeDerivedSubdivisionOfCollapse hK hKs L (mixedDerivedInclusion_anodyne hI hK hKs L)

end HomotopyHypothesis.Approximation.Zeeman

#print axioms HomotopyHypothesis.Approximation.Zeeman.mixedStage_finite_anodyne
#print axioms HomotopyHypothesis.Approximation.Zeeman.mixedDerivedInclusion_anodyne
#print axioms HomotopyHypothesis.Approximation.Zeeman.relativeDerivedSubdivision
