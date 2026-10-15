import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Approximation.FiniteSubcomplex.SequentialCompactSupport
import HomotopyHypothesis.Approximation.FiniteSubcomplex.TransfiniteMono
import HomotopyHypothesis.Approximation.CompactFactorization.SelectedPoints
universe u

open CategoryTheory Limits TopCat Topology

namespace HomotopyHypothesis.Approximation.CompactFactorization

open HomotopyHypothesis.Approximation.FiniteSubcomplex

variable {J : Type u} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
  {X Y : TopCat.{u}} {f : X ⟶ Y}
  (c : Henry.Top.relativeFiniteCellComplexes.TransfiniteCompositionOfShape J f)

/-- A compact image uses only finitely many successor stages of a transfinite cell presentation. -/
theorem finite_used_successorStages
    (hT1 : ∀ j : J, T1Space (c.F.obj j))
    {K : TopCat.{u}} [CompactSpace K] (g : K ⟶ Y) :
    {i : J | ∃ y : Y, y ∈ Set.range g.hom ∧
      y ∈ Set.range (c.incl.app (Order.succ i)).hom ∧
      y ∉ Set.range (c.incl.app i).hom}.Finite := by
  classical
  let U : Set J := {i | ∃ y : Y, y ∈ Set.range g.hom ∧
      y ∈ Set.range (c.incl.app (Order.succ i)).hom ∧
      y ∉ Set.range (c.incl.app i).hom}
  let p : U → Y := fun i => Classical.choose i.2
  have hp (i : U) : p i ∈ Set.range g.hom ∧
      p i ∈ Set.range (c.incl.app (Order.succ i.1)).hom ∧
      p i ∉ Set.range (c.incl.app i.1).hom := Classical.choose_spec i.2
  have hpstage (j : J) (i : U) (h : p i ∈ Set.range (c.incl.app j).hom) :
      i.1 < j := by
    by_contra hij
    exact (hp i).2.2 (stage_range_mono c (le_of_not_gt hij) h)
  have hpinj : Function.Injective p := by
    intro i j hij
    apply Subtype.ext
    rcases lt_trichotomy i.1 j.1 with hlt | heq | hgt
    · have hmem := stage_range_mono c (Order.succ_le_of_lt hlt) (hp i).2.1
      exact False.elim ((hp j).2.2 (hij ▸ hmem))
    · exact heq
    · have hmem := stage_range_mono c (Order.succ_le_of_lt hgt) (hp j).2.1
      exact False.elim ((hp i).2.2 (hij.symm ▸ hmem))
  let Q : Set Y := Set.range p
  have hbot : (c.incl.app ⊥).hom ⁻¹' Q = ∅ := by
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨i, hi⟩
    exact (not_lt_of_ge bot_le) (hpstage ⊥ i ⟨x, hi.symm⟩)
  have hnew (i : J) (_hi : ¬ IsMax i) :
      ((c.incl.app (Order.succ i)).hom ⁻¹' Q \
        Set.range (c.F.map (homOfLE (Order.le_succ i))).hom).Finite := by
    let e := (c.F.map (homOfLE (Order.le_succ i))).hom
    have hindex (x : c.F.obj (Order.succ i))
        (hx : x ∈ (c.incl.app (Order.succ i)).hom ⁻¹' Q \ Set.range e) :
        ∃ a : U, p a = (c.incl.app (Order.succ i)).hom x ∧ a.1 = i := by
      obtain ⟨a, ha⟩ := hx.1
      refine ⟨a, ha, ?_⟩
      have hai : a.1 ≤ i := Order.le_of_lt_succ
        (hpstage (Order.succ i) a ⟨x, ha.symm⟩)
      apply le_antisymm hai
      by_contra hia
      have halt : a.1 < i := lt_of_not_ge hia
      obtain ⟨z, hz⟩ := stage_range_mono c (Order.succ_le_of_lt halt) (hp a).2.1
      have heq : e z = x := transfiniteComposition_stage_injective c (Order.succ i)
        ((incl_map_apply c (Order.le_succ i) z).trans (hz.trans ha))
      exact hx.2 ⟨z, heq⟩
    apply Set.Subsingleton.finite
    intro x hx z hz
    obtain ⟨a, hax, hai⟩ := hindex x hx
    obtain ⟨b, hbz, hbi⟩ := hindex z hz
    have hab : a = b := Subtype.ext (hai.trans hbi.symm)
    exact transfiniteComposition_stage_injective c (Order.succ i)
      (hax.symm.trans ((congrArg p hab).trans hbz))
  have hQ := closedDiscrete_of_finite_stage_increments c hT1 Q
    (by rw [hbot]; exact Set.finite_empty) hnew
  have hQsub : Q ⊆ Set.range g.hom := by
    rintro y ⟨i, rfl⟩
    exact (hp i).1
  have hQcompact : IsCompact Q :=
    (isCompact_range g.hom.continuous).of_isClosed_subset hQ.1 hQsub
  have hQfinite : Q.Finite := hQcompact.finite hQ.2
  have hU : (Set.univ : Set U).Finite := by
    have hpre : p ⁻¹' Q = Set.univ := by ext i; simp [Q]
    rw [← hpre]
    exact hQfinite.preimage_embedding ⟨p, hpinj⟩
  exact Set.finite_coe_iff.mp (Set.finite_univ_iff.mp hU)

end HomotopyHypothesis.Approximation.CompactFactorization
