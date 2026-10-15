import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Approximation.FiniteSubcomplex.SequentialClosedEmbedding
import HomotopyHypothesis.Approximation.FiniteSubcomplex.TransfiniteMono
universe u

open CategoryTheory Limits TopCat Topology

namespace HomotopyHypothesis.Approximation.CompactFactorization

open HomotopyHypothesis.Approximation.FiniteSubcomplex

variable {J : Type u} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
  {X Y : TopCat.{u}} {f : X ⟶ Y}
  (c : Henry.Top.relativeFiniteCellComplexes.TransfiniteCompositionOfShape J f)

/-- Every transition in a transfinite relative finite-cell presentation is a closed embedding. -/
theorem transfiniteComposition_map_closedEmbedding :
    ∀ {i j : J} (φ : i ⟶ j), IsClosedEmbedding (c.F.map φ).hom := by
  classical
  have hmain : ∀ j : J, ∀ {i : J} (φ : i ⟶ j),
      IsClosedEmbedding (c.F.map φ).hom := by
    intro j
    induction j using WellFoundedLT.induction with
    | ind j ih =>
      intro i φ
      by_cases hij : i = j
      · subst i
        have hφ : φ = 𝟙 j := Subsingleton.elim _ _
        simpa [hφ] using (Homeomorph.refl (c.F.obj j)).isClosedEmbedding
      · have hijlt : i < j := lt_of_le_of_ne φ.le hij
        by_cases hjlim : Order.IsSuccLimit j
        · let d := (Set.principalSegIio j).cocone c.F
          have hd : IsColimit d := c.F.isColimitOfIsWellOrderContinuous j hjlim
          have hmap : ∀ {a b : Set.Iio j} (ψ : a ⟶ b),
              IsClosedEmbedding (((Set.principalSegIio j).monotone.functor ⋙ c.F).map ψ).hom := by
            intro a b ψ
            exact ih b.1 b.2 (homOfLE ψ.le)
          have hdi : ∀ k : Set.Iio j, Function.Injective (d.ι.app k).hom := by
            intro k
            have hk := transfiniteComposition_stage_injective (c.iic j)
              (⟨k.1, k.2.le⟩ : Set.Iic j)
            exact hk
          have he := transfinite_colimit_stage_closedEmbedding hd hmap hdi
            (⟨i, hijlt⟩ : Set.Iio j)
          exact he
        · have hjbot : j ≠ ⊥ := ne_of_gt (bot_le.trans_lt hijlt)
          have hnotpre : ¬ Order.IsSuccPrelimit j := by
            intro hpre
            exact hjlim ((Order.isSuccLimit_iff_of_orderBot).2 ⟨hjbot, hpre⟩)
          obtain ⟨k, hkMax, hkSucc⟩ :=
            Order.not_isSuccPrelimit_iff_succ_eq.mp hnotpre
          have hkj : k < j := by
            rw [← hkSucc]
            exact Order.lt_succ_of_not_isMax hkMax
          have hik : i ≤ k := by
            rw [← hkSucc] at hijlt
            exact Order.le_of_lt_succ hijlt
          subst j
          have hφ : φ = homOfLE hik ≫ homOfLE (Order.le_succ k) :=
            Subsingleton.elim _ _
          rw [hφ, c.F.map_comp]
          exact (transfiniteComposition_successor_closedEmbedding c k hkMax).comp
            (ih k hkj (homOfLE hik))
  intro i j φ
  exact hmain j φ

/-- Each stage of a transfinite relative finite-cell presentation is closed in the colimit. -/
theorem transfiniteComposition_incl_closedEmbedding (j : J) :
    IsClosedEmbedding (c.incl.app j).hom :=
  transfinite_colimit_stage_closedEmbedding c.isColimit
    (fun φ => transfiniteComposition_map_closedEmbedding c φ)
    (transfiniteComposition_stage_injective c) j

end HomotopyHypothesis.Approximation.CompactFactorization
