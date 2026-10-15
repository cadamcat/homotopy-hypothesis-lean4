import HomotopyHypothesis.Approximation.Topological.Complex
import HomotopyHypothesis.Approximation.Topological.CylinderGlue
import HomotopyHypothesis.Approximation.Topological.DerivedCylinder.Code
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.DprismComplex
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Inst42
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.PV
import HomotopyHypothesis.Approximation.Topological.DerivedPrism.Rank
import HomotopyHypothesis.Approximation.Topological.DerivedPrismFunctor.Map

/-!
# `HomotopyHypothesis.Approximation.DerivedPrismNaturality.Proofs`, part 1

Lines 19–101 of `HomotopyHypothesis.Approximation.DerivedPrismNaturality.Proofs`, split so that the modules of the development form an acyclic import graph.
-/

universe u

open CategoryTheory Limits Opposite

namespace HomotopyHypothesis.Approximation.DerivedPrismNaturality

open HomotopyHypothesis.Henry HomotopyHypothesis.Henry.SemiSSet
open HomotopyHypothesis.Approximation.Topological

theorem map_strictMonoOn_proof {k l : ℕ} {t : Fin (k + 1) → Fin (l + 1)}
    (ht : StrictMono t) (A : Finset (PV k)) (hA : (dprismComplex k).S A) :
    StrictMonoOn (PV.map t) A := by
  intro a ha b hb hab
  cases a with
  | top i =>
    cases b with
    | top j =>
      change PV.rank (PV.top i) < PV.rank (PV.top j) at hab
      have hij : i < j := by
        simpa [PV.rank, Prod.Lex.toLex_lt_toLex] using hab
      change PV.rank (PV.top (t i)) < PV.rank (PV.top (t j))
      simpa [PV.rank, Prod.Lex.toLex_lt_toLex] using ht hij
    | mid S =>
      change PV.rank (PV.top (t i)) < PV.rank (PV.mid (S.image t))
      simp [PV.rank, Prod.Lex.toLex_lt_toLex]
  | mid S =>
    cases b with
    | top j =>
      change PV.rank (PV.mid S) < PV.rank (PV.top j) at hab
      simp [PV.rank, Prod.Lex.toLex_lt_toLex] at hab
    | mid S' =>
      have hne : S ≠ S' := by
        intro h
        subst S'
        exact (lt_irrefl _ hab)
      have hcard : S.card < S'.card := by
        rcases hA.2.1 S S' ha hb with hSS' | hS'S
        · exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hSS', hne⟩)
        · have hcard' : S'.card < S.card :=
            Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hS'S, hne.symm⟩)
          have hbad : (PV.mid S' : PV k) < PV.mid S := by
            change PV.rank _ < PV.rank _
            exact Prod.Lex.toLex_lt_toLex.2
              (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.2 (Or.inl hcard')⟩)
          exact (lt_asymm hab hbad).elim
      have hcard₁ := Finset.card_image_of_injective S ht.injective
      have hcard₂ := Finset.card_image_of_injective S' ht.injective
      have hcardImg : (S.image t).card < (S'.image t).card := by
        rw [hcard₁, hcard₂]
        exact hcard
      change PV.rank (PV.mid (S.image t)) < PV.rank (PV.mid (S'.image t))
      exact Prod.Lex.toLex_lt_toLex.2
        (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.2 (Or.inl hcardImg)⟩)

theorem map_S_proof {k l : ℕ} {t : Fin (k + 1) → Fin (l + 1)}
    (_ht : StrictMono t) (A : Finset (PV k)) (hA : (dprismComplex k).S A) :
    (dprismComplex l).S (A.image (PV.map t)) := by
  have preMid (S : Finset (Fin (l + 1))) (hS : PV.mid S ∈ A.image (PV.map t)) :
      ∃ T, PV.mid T ∈ A ∧ T.image t = S := by
    rcases Finset.mem_image.mp hS with ⟨a, ha, hEq⟩
    cases a with
    | top i => simp [PV.map] at hEq
    | mid T => exact ⟨T, ha, by simpa [PV.map] using hEq⟩
  have preTop (i : Fin (l + 1)) (hi : PV.top i ∈ A.image (PV.map t)) :
      ∃ j, PV.top j ∈ A ∧ t j = i := by
    rcases Finset.mem_image.mp hi with ⟨a, ha, hEq⟩
    cases a with
    | top j => exact ⟨j, ha, by simpa [PV.map] using hEq⟩
    | mid S => simp [PV.map] at hEq
  refine ⟨?_, ?_, ?_⟩
  · intro S hS
    obtain ⟨T, hT, rfl⟩ := preMid S hS
    rcases hA.1 T hT with ⟨i, hi⟩
    exact ⟨t i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
  · intro S S' hS hS'
    obtain ⟨T, hT, rfl⟩ := preMid S hS
    obtain ⟨T', hT', rfl⟩ := preMid S' hS'
    rcases hA.2.1 T T' hT hT' with hTT' | hT'T
    · left
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
      exact Finset.mem_image.mpr ⟨y, hTT' hy, rfl⟩
    · right
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
      exact Finset.mem_image.mpr ⟨y, hT'T hy, rfl⟩
  · intro i S hi hS
    obtain ⟨T, hT, rfl⟩ := preMid S hS
    obtain ⟨j, hj, htji⟩ := preTop i hi
    have hjT := hA.2.2 j T hj hT
    exact Finset.mem_image.mpr ⟨j, hjT, htji⟩
