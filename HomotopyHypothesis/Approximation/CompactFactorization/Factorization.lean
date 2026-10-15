import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Approximation.FiniteSubcomplex.SequentialCompactSupport
import HomotopyHypothesis.Approximation.FiniteSubcomplex.TransfiniteMono
import HomotopyHypothesis.Approximation.CompactFactorization.CompactSupport
import HomotopyHypothesis.Approximation.CompactFactorization.SelectedPoints
import HomotopyHypothesis.Approximation.CompactFactorization.TransfiniteStages
universe u

open CategoryTheory Limits TopCat Topology

namespace HomotopyHypothesis.Approximation.CompactFactorization

open HomotopyHypothesis.Approximation.FiniteSubcomplex

/-- Compact images are contained in one stage of a transfinite relative finite-cell presentation
with T₁ stages. -/
theorem compact_range_subset_stage
    {J : Type u} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
    {X Y : TopCat.{u}} {f : X ⟶ Y}
    (c : Henry.Top.relativeFiniteCellComplexes.TransfiniteCompositionOfShape J f)
    (hT1 : ∀ j : J, T1Space (c.F.obj j))
    {K : TopCat.{u}} [CompactSpace K] (g : K ⟶ Y) :
    ∃ j : J, Set.range g.hom ⊆ Set.range (c.incl.app j).hom := by
  classical
  let U : Set J := {i | ∃ y : Y, y ∈ Set.range g.hom ∧
      y ∈ Set.range (c.incl.app (Order.succ i)).hom ∧
      y ∉ Set.range (c.incl.app i).hom}
  have hU : U.Finite := finite_used_successorStages c hT1 g
  let N : J := hU.toFinset.sup Order.succ
  have hsuc_bound (i : J) (hi : i ∈ U) : Order.succ i ≤ N :=
    Finset.le_sup (hU.mem_toFinset.mpr hi)
  have hbound : ∀ j : J, ∀ y : Y, y ∈ Set.range g.hom →
      y ∈ Set.range (c.incl.app j).hom → y ∈ Set.range (c.incl.app N).hom := by
    intro j
    induction j using WellFoundedLT.induction with
    | ind j ih =>
      intro y hyg hyj
      by_cases hjbot : j = ⊥
      · subst j
        exact stage_range_mono c bot_le hyj
      · by_cases hjlim : Order.IsSuccLimit j
        · obtain ⟨z, hz⟩ := hyj
          let d := (Set.principalSegIio j).cocone c.F
          have hd : IsColimit d := c.F.isColimitOfIsWellOrderContinuous j hjlim
          let dT := (forget TopCat).mapCocone d
          have hdT : IsColimit dT := isColimitOfPreserves (forget TopCat) hd
          obtain ⟨i, x, hx⟩ := Types.jointly_surjective_of_isColimit hdT z
          apply ih i.1 i.2 y hyg
          refine ⟨x, ?_⟩
          calc
            (c.incl.app i.1).hom x =
                (c.incl.app j).hom ((c.F.map (homOfLE i.2.le)).hom x) :=
              (incl_map_apply c i.2.le x).symm
            _ = (c.incl.app j).hom z := congrArg (c.incl.app j).hom hx
            _ = y := hz
        · have hnotpre : ¬ Order.IsSuccPrelimit j := by
            intro hpre
            exact hjlim ((Order.isSuccLimit_iff_of_orderBot).2 ⟨hjbot, hpre⟩)
          obtain ⟨i, hiMax, hiSucc⟩ :=
            Order.not_isSuccPrelimit_iff_succ_eq.mp hnotpre
          have hij : i < j := by
            rw [← hiSucc]
            exact Order.lt_succ_of_not_isMax hiMax
          subst j
          by_cases hyi : y ∈ Set.range (c.incl.app i).hom
          · exact ih i hij y hyg hyi
          · exact stage_range_mono c (hsuc_bound i ⟨y, hyg, hyj, hyi⟩) hyj
  refine ⟨N, ?_⟩
  intro y hyg
  let dT := (forget TopCat).mapCocone (Cocone.mk Y c.incl)
  have hdT : IsColimit dT := isColimitOfPreserves (forget TopCat) c.isColimit
  obtain ⟨j, x, hx⟩ := Types.jointly_surjective_of_isColimit hdT y
  exact hbound j y hyg ⟨x, hx⟩

/-- Maps from compact spaces into a transfinite relative finite-cell presentation with T₁
stages factor continuously through a stage. -/
theorem transfiniteComposition_factorization_of_compact
    {J : Type u} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
    {X Y : TopCat.{u}} {f : X ⟶ Y}
    (c : Henry.Top.relativeFiniteCellComplexes.TransfiniteCompositionOfShape J f)
    (hT1 : ∀ j : J, T1Space (c.F.obj j))
    {K : TopCat.{u}} [CompactSpace K] (g : K ⟶ Y) :
    ∃ (j : J) (g' : K ⟶ c.F.obj j), g' ≫ c.incl.app j = g := by
  obtain ⟨j, hj⟩ := compact_range_subset_stage c hT1 g
  obtain ⟨g', hg'⟩ := TopCat.factor_through_embedding_of_range_subset
    (transfiniteComposition_incl_closedEmbedding c j).isEmbedding hj
  exact ⟨j, g', hg'⟩

/-- Every finite cell complex is T₁. -/
theorem t1Space_of_isFiniteCellComplex {X : TopCat.{u}}
    (hX : Henry.Top.IsFiniteCellComplex X) : T1Space X := by
  have hEmpty : T1Space (⊥_ TopCat.{u}) :=
    (TopCat.homeoOfIso TopCat.initialIsoPEmpty).symm.t1Space
  exact relativeFiniteCellComplexes_preserves_t1 hX hEmpty

end HomotopyHypothesis.Approximation.CompactFactorization

namespace HomotopyHypothesis.Henry.Packages

/-- Compact maps into a transfinite cell presentation factor through a stage. -/
theorem exists_factorization_of_compactSpace_proof
    {J : Type u} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
    {X Y : TopCat.{u}} {f : X ⟶ Y}
    (c : Top.relativeFiniteCellComplexes.TransfiniteCompositionOfShape J f)
    (hX : Top.IsFiniteCellComplex X) :
    (∀ j : J, Function.Injective (c.incl.app j).hom) ∧
    ∀ (K : TopCat.{u}) [CompactSpace K] (g : K ⟶ Y),
      ∃ (j : J) (g' : K ⟶ c.F.obj j), g' ≫ c.incl.app j = g := by
  refine ⟨HomotopyHypothesis.Approximation.FiniteSubcomplex.transfiniteComposition_stage_injective c, ?_⟩
  intro K _ g
  exact HomotopyHypothesis.Approximation.CompactFactorization.transfiniteComposition_factorization_of_compact c
    (HomotopyHypothesis.Approximation.FiniteSubcomplex.transfiniteComposition_stages_t1 c
      (HomotopyHypothesis.Approximation.CompactFactorization.t1Space_of_isFiniteCellComplex hX)) g

#print axioms exists_factorization_of_compactSpace_proof

end HomotopyHypothesis.Henry.Packages
