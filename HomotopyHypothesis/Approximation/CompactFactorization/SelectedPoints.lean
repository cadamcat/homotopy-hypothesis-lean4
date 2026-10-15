import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Approximation.FiniteSubcomplex.SequentialClosedEmbedding
import HomotopyHypothesis.Approximation.FiniteSubcomplex.TransfiniteMono
import HomotopyHypothesis.Approximation.CompactFactorization.TransfiniteStages
universe u

open CategoryTheory Limits TopCat Topology

namespace HomotopyHypothesis.Approximation.CompactFactorization

open HomotopyHypothesis.Approximation.FiniteSubcomplex

variable {J : Type u} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
  {X Y : TopCat.{u}} {f : X ⟶ Y}
  (c : Henry.Top.relativeFiniteCellComplexes.TransfiniteCompositionOfShape J f)

/-- The transition maps commute pointwise with the maps to the colimit. -/
theorem incl_map_apply {i j : J} (hij : i ≤ j) (x : c.F.obj i) :
    (c.incl.app j).hom ((c.F.map (homOfLE hij)).hom x) = (c.incl.app i).hom x :=
  congrArg (fun q : c.F.obj i ⟶ Y => q.hom x) (c.incl.naturality (homOfLE hij))

/-- A point represented at one stage is represented at every later stage. -/
theorem stage_range_mono {i j : J} (hij : i ≤ j) :
    Set.range (c.incl.app i).hom ⊆ Set.range (c.incl.app j).hom := by
  rintro y ⟨x, rfl⟩
  exact ⟨(c.F.map (homOfLE hij)).hom x, incl_map_apply c hij x⟩

/-- A selection with finitely many points at the bottom and finitely many new points at each
successor stage is closed and discrete in the transfinite colimit. -/
theorem closedDiscrete_of_finite_stage_increments
    (hT1 : ∀ j : J, T1Space (c.F.obj j)) (Q : Set Y)
    (hbot : ((c.incl.app ⊥).hom ⁻¹' Q).Finite)
    (hnew : ∀ i : J, ¬ IsMax i →
      ((c.incl.app (Order.succ i)).hom ⁻¹' Q \
        Set.range (c.F.map (homOfLE (Order.le_succ i))).hom).Finite) :
    IsClosed Q ∧ IsDiscrete Q := by
  classical
  have hstage : ∀ j : J,
      IsClosed ((c.incl.app j).hom ⁻¹' Q) ∧
        IsDiscrete ((c.incl.app j).hom ⁻¹' Q) := by
    intro j
    induction j using WellFoundedLT.induction with
    | ind j ih =>
      let : T1Space (c.F.obj j) := hT1 j
      by_cases hjbot : j = ⊥
      · subst j
        have h := closedDiscrete_union_finite_of_t1 isClosed_empty
          (Set.subsingleton_empty.isDiscrete) hbot
        simpa using h
      · by_cases hjlim : Order.IsSuccLimit j
        · let d := (Set.principalSegIio j).cocone c.F
          have hd : IsColimit d := c.F.isColimitOfIsWellOrderContinuous j hjlim
          have hdi : ∀ k : Set.Iio j, Function.Injective (d.ι.app k).hom := by
            intro k
            exact transfiniteComposition_stage_injective (c.iic j)
              (⟨k.1, k.2.le⟩ : Set.Iic j)
          apply transfinite_colimit_closedDiscrete_of_stagewise hd hdi
          intro k
          have hpre : (d.ι.app k).hom ⁻¹' ((c.incl.app j).hom ⁻¹' Q) =
              (c.incl.app k.1).hom ⁻¹' Q := by
            ext x
            change (c.incl.app j).hom ((c.F.map (homOfLE k.2.le)).hom x) ∈ Q ↔ _
            rw [incl_map_apply c k.2.le x]
            rfl
          rw [hpre]
          exact ih k.1 k.2
        · have hnotpre : ¬ Order.IsSuccPrelimit j := by
            intro hpre
            exact hjlim ((Order.isSuccLimit_iff_of_orderBot).2 ⟨hjbot, hpre⟩)
          obtain ⟨i, hiMax, hiSucc⟩ :=
            Order.not_isSuccPrelimit_iff_succ_eq.mp hnotpre
          have hij : i < j := by
            rw [← hiSucc]
            exact Order.lt_succ_of_not_isMax hiMax
          subst j
          let e := (c.F.map (homOfLE (Order.le_succ i))).hom
          have hprev := closedEmbedding_image_closedDiscrete
            (transfiniteComposition_successor_closedEmbedding c i hiMax)
            (ih i hij).1 (ih i hij).2
          have hdecomp : (c.incl.app (Order.succ i)).hom ⁻¹' Q =
              e '' ((c.incl.app i).hom ⁻¹' Q) ∪
                ((c.incl.app (Order.succ i)).hom ⁻¹' Q \ Set.range e) := by
            ext x
            constructor
            · intro hx
              by_cases he : x ∈ Set.range e
              · obtain ⟨z, rfl⟩ := he
                left
                refine ⟨z, ?_, rfl⟩
                change (c.incl.app i).hom z ∈ Q
                rw [← incl_map_apply c (Order.le_succ i) z]
                exact hx
              · exact Or.inr ⟨hx, he⟩
            · rintro (⟨z, hz, rfl⟩ | hx)
              · change (c.incl.app (Order.succ i)).hom (e z) ∈ Q
                rw [incl_map_apply c (Order.le_succ i) z]
                exact hz
              · exact hx.1
          rw [hdecomp]
          exact closedDiscrete_union_finite_of_t1 hprev.1 hprev.2 (hnew i hiMax)
  exact transfinite_colimit_closedDiscrete_of_stagewise c.isColimit
    (transfiniteComposition_stage_injective c) Q hstage

end HomotopyHypothesis.Approximation.CompactFactorization
