import Mathlib.Data.Finset.Sort
import Mathlib.Tactic
import HomotopyHypothesis.Approximation.BarycentricCell.Coordinates
import HomotopyHypothesis.Approximation.BarycentricCell.Mixtures
import HomotopyHypothesis.Approximation.BarycentricCell.Peeling
import HomotopyHypothesis.Approximation.DerivedPrismTop.DerivedPositions
universe u

open Convexity

namespace HomotopyHypothesis.Approximation.BarycentricCell

open HomotopyHypothesis.Approximation.DerivedPrismTop

/-- A probability vector factors through the ordered set of its nonzero coordinates. -/
theorem exists_support_embedding {k : ℕ} (t : StdSimplex ℝ (Fin (k + 1))) :
    ∃ m : ℕ, ∃ e : Fin (m + 1) ↪o Fin (k + 1),
      ∃ p : StdSimplex ℝ (Fin (m + 1)),
        m + 1 = t.weights.support.card ∧ StdSimplex.map e p = t ∧
          Set.range e = (t.weights.support : Set (Fin (k + 1))) ∧
          ∀ i, p.weights i ≠ 0 := by
  classical
  let s := t.weights.support
  have hpos : 0 < s.card := Finset.card_pos.mpr t.support_weights_nonempty
  have hcard : s.card = (s.card - 1) + 1 := by omega
  let e : Fin ((s.card - 1) + 1) ↪o Fin (k + 1) := s.orderEmbOfFin hcard
  have he : Set.range e = (s : Set (Fin (k + 1))) := by
    simpa [e] using Finset.range_orderEmbOfFin s hcard
  obtain ⟨p, hp⟩ := (StdSimplex.mem_range_map_iff e t).mpr (by
    intro i hi
    by_contra hne
    apply hi
    rw [he]
    exact Finsupp.mem_support_iff.mpr hne)
  refine ⟨s.card - 1, e, p, ?_, hp, he, ?_⟩
  · exact hcard.symm
  intro i hi
  have hmem : e i ∈ s := s.orderEmbOfFin_mem hcard i
  have hne := Finsupp.mem_support_iff.mp hmem
  apply hne
  rw [← hp, StdSimplex.weights_map,
    Finsupp.mapDomain_apply_of_injective e.injective, hi]

set_option maxHeartbeats 1000000 in
/-- Every probability vector with positive coordinates is a mixture on a strict face chain. -/
theorem exists_faceChain_mixture_full :
    ∀ k : ℕ, ∀ t : StdSimplex ℝ (Fin (k + 1)),
      (∀ i, t.weights i ≠ 0) →
        ∃ n : ℕ, ∃ C : FaceChain k n, ∃ p : StdSimplex ℝ (Fin (n + 1)),
          (∀ i, p.weights i ≠ 0) ∧ C.mixture p = t := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro t ht
    rcases barycentricPeelingStatement_proof k t with htbar | ⟨c, q, i, hc, hc', hqi, hpeel⟩
    · let C : FaceChain k 0 := {
        faces := fun _ => Finset.univ
        nonempty := by intro j; simp
        strict := by
          intro i j hij
          have hEq : i = j := by
            apply Fin.ext
            omega
          subst j
          exact (False.elim ((lt_irrefl i) hij))
      }
      let p : StdSimplex ℝ (Fin 1) := StdSimplex.single (0 : Fin 1)
      have hmix : C.mixture p = StdSimplex.barycenter (K := ℝ) (M := Fin (k + 1)) := by
        change faceMixture (fun _ => Finset.univ) (fun _ => Finset.univ_nonempty) p = _
        rw [faceMixture, show p = StdSimplex.single (0 : Fin 1) from rfl,
          StdSimplex.affineMapMk_single, barycentricPoint_univ]
      refine ⟨0, C, p, ?_, ?_⟩
      · intro j
        have hj : j = (0 : Fin 1) := by
          apply Fin.ext
          omega
        rw [hj]
        simp [p]
      · exact hmix.trans htbar.symm
    · have htpos : 0 < t.weights i :=
        lt_of_le_of_ne (t.weights_nonneg i) (Ne.symm (ht i))
      have hbary : 0 <
          (StdSimplex.barycenter (K := ℝ) (M := Fin (k + 1))).weights i := by
        rw [StdSimplex.weights_barycenter_apply]
        positivity
      have hprod : 0 < c *
          (StdSimplex.barycenter (K := ℝ) (M := Fin (k + 1))).weights i := by
        have hiEq := hpeel i
        rw [hqi, mul_zero, add_zero] at hiEq
        rw [← hiEq]
        exact htpos
      have hcpos : 0 < c := by
        by_contra hnot
        have hcNonpos : c ≤ 0 := le_of_not_gt hnot
        have hnonpos := mul_nonpos_of_nonpos_of_nonneg hcNonpos hbary.le
        linarith
      obtain ⟨m, e, p, hmcard, hmap, hrange, hp⟩ := exists_support_embedding q
      have hiNotSupport : i ∉ q.weights.support := by
        rw [Finsupp.mem_support_iff]
        exact fun hne => hne hqi
      have hsub : q.weights.support ⊆ Finset.univ.erase i := by
        intro j hj
        apply Finset.mem_erase.mpr
        refine ⟨?_, Finset.mem_univ j⟩
        intro hji
        subst j
        exact hiNotSupport hj
      have hcardle : q.weights.support.card ≤ k := by
        calc
          q.weights.support.card ≤ (Finset.univ.erase i).card := Finset.card_le_card hsub
          _ = k := by simp
      have hm : m < k := by omega
      obtain ⟨n, C, r, hr, hCr⟩ := ih m hm p hp
      let D : FaceChain k n := C.mapVertices e e.injective
      have hDmix : D.mixture r = q := by
        rw [C.mapVertices_mixture, hCr, hmap]
      have hiNotRange : i ∉ Set.range e := by
        rw [hrange]
        exact hiNotSupport
      have hiNotLast : i ∉ D.faces (Fin.last n) := by
        intro himage
        rcases Finset.mem_image.mp himage with ⟨j, hj, hji⟩
        exact hiNotRange ⟨j, hji⟩
      have hproper : D.faces (Fin.last n) ⊂ Finset.univ :=
        (Finset.ssubset_iff_of_subset (Finset.subset_univ _)).2
          ⟨i, Finset.mem_univ _, hiNotLast⟩
      let Cfull : FaceChain k (n + 1) := D.appendFull hproper
      let pfull : StdSimplex ℝ (Fin (n + 2)) := appendWeight c hc hc' r
      have hpfull : ∀ j, pfull.weights j ≠ 0 :=
        appendWeight_ne_zero c hcpos hc' r hr
      have hprefix : Cfull.initialSegment = D := by
        apply FaceChain.eq_of_faces_eq
        intro j
        simp [Cfull, FaceChain.initialSegment, FaceChain.appendFull]
      have hprefixFaces : ∀ j, Cfull.faces j.castSucc = D.faces j := by
        intro j
        have hj := congrArg (fun X : FaceChain k n => X.faces j) hprefix
        exact hj
      have hfull : Cfull.faces (Fin.last (n + 1)) = Finset.univ := by
        simp [Cfull, FaceChain.appendFull]
      have hlast : pfull.weights (Fin.last (n + 1)) = c :=
        appendWeight_last c hc hc' r
      have hcnew : pfull.weights (Fin.last (n + 1)) < 1 := by
        rw [hlast]
        exact hc'
      have hnorm : normalizedPrefix pfull hcnew = r :=
        normalizedPrefix_appendWeight c hc hc' r
      have hbary :
          barycentricPoint (Cfull.faces (Fin.last (n + 1))) (Cfull.nonempty _) =
            StdSimplex.barycenter (K := ℝ) (M := Fin (k + 1)) := by
        apply StdSimplex.ext
        apply Finsupp.ext
        intro j
        rw [barycentricPoint_weight_apply, StdSimplex.weights_barycenter_apply]
        simp [hfull, Finset.card_univ, Fintype.card_fin]
      have hprefixMix :
          faceMixture (fun j => Cfull.faces j.castSucc) (fun j => Cfull.nonempty j.castSucc)
            (normalizedPrefix pfull hcnew) = D.mixture r := by
        change faceMixture (fun j => Cfull.faces j.castSucc)
            (fun j => Cfull.nonempty j.castSucc) (normalizedPrefix pfull hcnew) =
          faceMixture D.faces D.nonempty r
        apply StdSimplex.ext
        apply Finsupp.ext
        intro v
        rw [faceMixture_weight_apply, faceMixture_weight_apply, hnorm]
        simp_rw [hprefixFaces]
      have hsplit := faceMixture_prefix_split Cfull.faces Cfull.nonempty pfull hcnew
      have hfullmix : Cfull.mixture pfull =
          convexCombPair c (1 - c) hc (sub_pos.mpr hc').le (by ring)
            (StdSimplex.barycenter (K := ℝ) (M := Fin (k + 1))) q := by
        change faceMixture Cfull.faces Cfull.nonempty pfull = _
        calc
          _ = convexCombPair (pfull.weights (Fin.last (n + 1)))
              (1 - pfull.weights (Fin.last (n + 1))) (pfull.weights_nonneg _)
              (sub_pos.mpr hcnew).le (by ring)
              (barycentricPoint (Cfull.faces (Fin.last (n + 1))) (Cfull.nonempty _))
              (faceMixture (fun j => Cfull.faces j.castSucc)
                (fun j => Cfull.nonempty j.castSucc) (normalizedPrefix pfull hcnew)) := hsplit
          _ = _ := FaceChain.convexCombPair_ext (pfull.weights_nonneg _) hc
            hcnew hc' _ _ _ _ hlast hbary hprefixMix
          _ = _ := by rw [hDmix]
      have htconvex : t =
          convexCombPair c (1 - c) hc (sub_pos.mpr hc').le (by ring)
            (StdSimplex.barycenter (K := ℝ) (M := Fin (k + 1))) q := by
        apply StdSimplex.ext
        apply Finsupp.ext
        intro j
        simpa only [StdSimplex.weights_convexCombPair, Finsupp.add_apply,
          Finsupp.smul_apply, smul_eq_mul] using hpeel j
      refine ⟨n + 1, Cfull, pfull, hpfull, ?_⟩
      calc
        Cfull.mixture pfull = _ := hfullmix
        _ = t := htconvex.symm

theorem exists_faceChain_mixture {k : ℕ} (t : StdSimplex ℝ (Fin (k + 1))) :
    ∃ n : ℕ, ∃ C : FaceChain k n, ∃ p : StdSimplex ℝ (Fin (n + 1)),
      (∀ i, p.weights i ≠ 0) ∧ C.mixture p = t := by
  obtain ⟨m, e, p, hmcard, hmap, hrange, hp⟩ := exists_support_embedding t
  obtain ⟨n, C, r, hr, hCr⟩ := exists_faceChain_mixture_full m p hp
  let D : FaceChain k n := C.mapVertices e e.injective
  refine ⟨n, D, r, hr, ?_⟩
  calc
    D.mixture r = StdSimplex.map e (C.mixture r) := C.mapVertices_mixture e e.injective r
    _ = StdSimplex.map e p := by rw [hCr]
    _ = t := hmap

end HomotopyHypothesis.Approximation.BarycentricCell
