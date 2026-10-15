import Mathlib.CategoryTheory.Types.Monomorphisms
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Defs.Induced
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Approximation.FiniteSubcomplex.PushoutEmbedding
import HomotopyHypothesis.Approximation.FiniteSubcomplex.SequentialClosedEmbedding
universe u v

open CategoryTheory Limits HomotopicalAlgebra TopCat Topology

namespace HomotopyHypothesis.Approximation.FiniteSubcomplex

/-- The standard disk-boundary inclusion is a closed embedding. -/
theorem diskBoundaryInclusion_isClosedEmbedding (n : ℕ) :
    IsClosedEmbedding (TopCat.diskBoundaryInclusion.{u} n).hom := by
  letI : CompactSpace (TopCat.diskBoundary.{u} n) := inferInstance
  letI : T2Space (EuclideanSpace ℝ (Fin n)) := inferInstance
  letI : T2Space ((TopCat.disk.{u} n : Type u)) := by
    change T2Space (ULift (↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)))
    infer_instance
  let f := TopCat.diskBoundaryInclusion.{u} n
  exact IsClosedEmbedding.of_continuous_injective_isClosedMap
    f.hom.continuous
    ((TopCat.mono_iff_injective f).mp inferInstance)
    f.hom.continuous.isClosedMap

private def topCatClosedEmbeddings : MorphismProperty TopCat.{u} :=
  fun _ _ f => IsClosedEmbedding f.hom

/-- Every relative finite-cell map in spaces is a closed embedding. -/
theorem relativeFiniteCellComplexes_le_closedEmbeddings :
    HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes.{u} ≤
      topCatClosedEmbeddings := by
  let P := topCatClosedEmbeddings
  letI : P.IsStableUnderCobaseChange :=
    { of_isPushout := fun {A A' B B' f g f' g'} sq hf => by
        change IsClosedEmbedding f.hom at hf
        exact pushout_isClosedEmbedding sq.flip hf }
  letI : P.IsMultiplicative :=
    { id_mem := fun X => IsClosedEmbedding.id
      comp_mem := fun f g hf hg => hg.comp hf }
  have hcell : HomotopyHypothesis.Henry.Top.cellBoundaries.{u} ≤ P := by
    rw [HomotopyHypothesis.Henry.Top.cellBoundaries,
      MorphismProperty.ofHoms_le_iff]
    intro n
    exact diskBoundaryInclusion_isClosedEmbedding n
  rw [HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes,
    MorphismProperty.multiplicativeClosure_le_iff]
  apply sup_le
  · exact MorphismProperty.pushouts_le_iff.mpr hcell
  · exact MorphismProperty.isomorphisms_le_of_containsIdentities _

/-- A relative finite-cell extension of a T₁ space is again T₁. -/
theorem relativeFiniteCellComplexes_preserves_t1
    {A B : TopCat.{u}} {f : A ⟶ B}
    (hf : HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes.{u} f)
    (hA : T1Space A) : T1Space B := by
  let P : MorphismProperty TopCat.{u} := fun X Y _ => T1Space X → T1Space Y
  letI : P.IsMultiplicative :=
    { id_mem := fun X h => h
      comp_mem := fun f g hf hg h => hg (hf h) }
  have hpush : HomotopyHypothesis.Henry.Top.cellBoundaries.{u}.pushouts ≤ P := by
    intro X Y q hq
    rcases hq with ⟨A, B, p, a, b, hp, sq⟩
    change T1Space X → T1Space Y
    intro hX
    rw [HomotopyHypothesis.Henry.Top.cellBoundaries,
      MorphismProperty.ofHoms_iff] at hp
    rcases hp with ⟨n, hp⟩
    have hA : A = TopCat.diskBoundary.{u} n := by
      simpa using congrArg Arrow.left hp
    have hB : B = TopCat.disk.{u} n := by
      simpa using congrArg Arrow.right hp
    subst A
    subst B
    have hp' : p = TopCat.diskBoundaryInclusion.{u} n :=
      (Arrow.mk_inj _ _).mp hp
    subst p
    letI : T2Space (TopCat.disk.{u} n : Type u) := by
      change T2Space (ULift (↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)))
      infer_instance
    letI : T1Space (TopCat.disk.{u} n : Type u) := inferInstance
    exact pushout_t1Space sq.flip (diskBoundaryInclusion_isClosedEmbedding n)
  have hiso : MorphismProperty.isomorphisms TopCat.{u} ≤ P := by
    intro X Y f hf
    change T1Space X → T1Space Y
    intro hX
    letI : IsIso f := hf
    letI : T1Space X := hX
    exact (TopCat.homeoOfIso (asIso f)).t1Space
  have hclosure :
      (HomotopyHypothesis.Henry.Top.cellBoundaries.{u}.pushouts ⊔
        MorphismProperty.isomorphisms TopCat.{u}).multiplicativeClosure ≤ P := by
    rw [MorphismProperty.multiplicativeClosure_le_iff]
    exact sup_le hpush hiso
  apply hclosure f
  · simpa [HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes] using hf
  · exact hA

private local instance mono_stableUnderCobaseChange :
    (MorphismProperty.monomorphisms TopCat.{u}).IsStableUnderCobaseChange where
  of_isPushout {A A' B B' f g f' g'} sq hf := by
    change Mono f at hf
    letI : Mono f := hf
    letI : Mono ((forget TopCat).map f) := Functor.map_mono (forget TopCat) f
    let t : PushoutCocone ((forget TopCat).map f) ((forget TopCat).map g) :=
      PushoutCocone.mk ((forget TopCat).map g') ((forget TopCat).map f') (by
        change (forget TopCat).map (f ≫ g') = (forget TopCat).map (g ≫ f')
        exact congrArg ((forget TopCat).map) sq.flip.w)
    have ht : IsColimit t := by
      simpa [t] using
        (isColimitPushoutCoconeMapOfIsColimit (forget TopCat) sq.flip.w
          sq.flip.isColimit)
    have hmono : Mono ((forget TopCat).map f') := by
      change Mono t.inr
      exact CategoryTheory.Limits.Types.pushoutCocone_inr_mono_of_isColimit ht
    exact Functor.mono_of_mono_map (forget TopCat) hmono

private theorem diskBoundaryInclusion_mono (n : ℕ) :
    Mono (TopCat.diskBoundaryInclusion.{u} n) := by
  infer_instance

theorem relativeFiniteCellComplexes_le_monomorphisms :
    HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes.{u} ≤
      MorphismProperty.monomorphisms TopCat.{u} := by
  have hcell : HomotopyHypothesis.Henry.Top.cellBoundaries.{u} ≤
      MorphismProperty.monomorphisms TopCat.{u} := by
    rw [HomotopyHypothesis.Henry.Top.cellBoundaries,
      MorphismProperty.ofHoms_le_iff]
    intro n
    exact diskBoundaryInclusion_mono n
  rw [HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes,
    MorphismProperty.multiplicativeClosure_le_iff]
  apply sup_le
  · exact MorphismProperty.pushouts_le_iff.mpr hcell
  · exact MorphismProperty.isomorphisms_le_of_containsIdentities _

theorem pushout_mono_of_mono {A A' B B' : TopCat.{u}}
    {f : A ⟶ A'} {g : A ⟶ B} {f' : A' ⟶ B'} {g' : B ⟶ B'}
    (sq : IsPushout f g f' g') [Mono f] : Mono g' := by
  have hf : MorphismProperty.monomorphisms TopCat.{u} f := by infer_instance
  change MorphismProperty.monomorphisms TopCat.{u} g'
  exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout sq.flip hf

theorem transfiniteComposition_stage_monomorphisms_of_mono
    {J : Type v} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
    {X Y : TopCat.{u}} {f : X ⟶ Y}
    (c : CategoryTheory.TransfiniteCompositionOfShape J f)
    (hstep : ∀ j : J, ¬ IsMax j →
      Mono (c.F.map (homOfLE (Order.le_succ j)))) :
    ∀ j : J, Mono (c.incl.app j) := by
  let h : MorphismProperty.TransfiniteCompositionOfShape
      ((MorphismProperty.monomorphisms (Type u)).inverseImage (forget TopCat)) J f :=
    { toTransfiniteCompositionOfShape := c
      map_mem := fun j hj => by
        letI : Mono (c.F.map (homOfLE (Order.le_succ j))) := hstep j hj
        exact Functor.map_mono (forget TopCat) _ }
  letI : PreservesWellOrderContinuousOfShape J (forget TopCat) :=
    ⟨fun j hj => by infer_instance⟩
  let h' := MorphismProperty.TransfiniteCompositionOfShape.map
    (F := forget TopCat) h
  intro j
  have hm : Mono ((forget TopCat).map (c.incl.app j)) := by
    simpa [h', h, MorphismProperty.TransfiniteCompositionOfShape.map,
      CategoryTheory.TransfiniteCompositionOfShape.map] using
      h'.mem_incl_app j
  exact Functor.mono_of_mono_map (forget TopCat) hm

theorem transfiniteComposition_stage_monomorphisms
    {J : Type u} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
    {X Y : TopCat.{u}} {f : X ⟶ Y}
    (c : HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes.TransfiniteCompositionOfShape
      J f) :
    ∀ j : J, Mono (c.incl.app j) := by
  apply transfiniteComposition_stage_monomorphisms_of_mono c.toTransfiniteCompositionOfShape
  intro j hj
  exact relativeFiniteCellComplexes_le_monomorphisms _
    (c.map_mem j hj)

theorem transfiniteComposition_stage_injective
    {J : Type u} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
    {X Y : TopCat.{u}} {f : X ⟶ Y}
    (c : HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes.TransfiniteCompositionOfShape
      J f) :
    ∀ j : J, Function.Injective (c.incl.app j).hom := by
  intro j
  exact (TopCat.mono_iff_injective (c.incl.app j)).mp
    (transfiniteComposition_stage_monomorphisms c j)

/-- Every stage of a transfinite relative finite-cell presentation beginning at a T₁ space is T₁. -/
theorem transfiniteComposition_stages_t1
    {J : Type u} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
    {X Y : TopCat.{u}} {f : X ⟶ Y}
    (c : HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes.TransfiniteCompositionOfShape
      J f)
    (hX : T1Space X) :
    ∀ j : J, T1Space (c.F.obj j) := by
  classical
  intro j
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    by_cases hjbot : j = ⊥
    · subst j
      letI : T1Space X := hX
      exact (TopCat.homeoOfIso c.isoBot).symm.t1Space
    · by_cases hjlim : Order.IsSuccLimit j
      · let d := (Set.principalSegIio j).cocone c.F
        have hd : IsColimit d := c.F.isColimitOfIsWellOrderContinuous j hjlim
        have hbound : ∀ i : Set.Iic j,
            Function.Injective ((c.iic j).incl.app i).hom :=
          transfiniteComposition_stage_injective (c.iic j)
        have hdi : ∀ i : Set.Iio j, Function.Injective (d.ι.app i).hom := by
          intro i
          let k : Set.Iic j := ⟨i.1, le_of_lt i.2⟩
          have hk := hbound k
          change Function.Injective (c.F.map (homOfLE i.2.le)).hom at hk
          change Function.Injective (c.F.map (homOfLE i.2.le)).hom
          exact hk
        exact transfinite_colimit_t1Space_of_stagewise hd hdi
          (fun i => ih i.1 i.2)
      · have hnotpre : ¬ Order.IsSuccPrelimit j := by
          intro hpre
          exact hjlim ((Order.isSuccLimit_iff_of_orderBot).2 ⟨hjbot, hpre⟩)
        obtain ⟨i, hiMax, hiSucc⟩ :=
          Order.not_isSuccPrelimit_iff_succ_eq.mp hnotpre
        have hij : i < j := by
          rw [← hiSucc]
          exact Order.lt_succ_of_not_isMax hiMax
        subst j
        exact relativeFiniteCellComplexes_preserves_t1 (c.map_mem i hiMax) (ih i hij)

/-- Every successor transition in a transfinite relative finite-cell presentation is a closed
embedding. -/
theorem transfiniteComposition_successor_closedEmbedding
    {J : Type u} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
    {X Y : TopCat.{u}} {f : X ⟶ Y}
    (c : HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes.TransfiniteCompositionOfShape
      J f) :
    ∀ j : J, ¬ IsMax j →
      IsClosedEmbedding (c.F.map (homOfLE (Order.le_succ j))).hom := by
  intro j hj
  exact relativeFiniteCellComplexes_le_closedEmbeddings _
    (c.map_mem j hj)

end HomotopyHypothesis.Approximation.FiniteSubcomplex
