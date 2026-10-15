import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Blueprint.Henry.Topology
import HomotopyHypothesis.Realization.Cellular.HomotopyProperties
/-!
# Elementary facts on relative finite cell complexes and homotopy equivalences

* Relative finite cell complexes contain the isomorphisms, are closed under composition, and are
  stable under cobase change.
* Homotopy equivalences contain the isomorphisms, satisfy 2-out-of-6, and every map between
  contractible spaces is one; topological simplices are contractible.
-/

universe u v

open CategoryTheory Limits MorphismProperty

namespace HomotopyHypothesis.Realization.SemisimplicialComparison

open HomotopyHypothesis.Henry

section CellComplexes

theorem relFinCell_of_isIso {X Y : TopCat.{u}} (f : X ⟶ Y) [IsIso f] :
    Top.relativeFiniteCellComplexes f :=
  MorphismProperty.multiplicativeClosure.of _ (Or.inr (inferInstance : IsIso f))

theorem relFinCell_comp {X Y Z : TopCat.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : Top.relativeFiniteCellComplexes f) (hg : Top.relativeFiniteCellComplexes g) :
    Top.relativeFiniteCellComplexes (f ≫ g) :=
  (MorphismProperty.multiplicativeClosure _).comp_mem _ _ hf hg

theorem relFinCell_id (X : TopCat.{u}) : Top.relativeFiniteCellComplexes (𝟙 X) :=
  .id X

/-- Finite composition preserves stability under cobase change. -/
theorem multiplicativeClosure_cobaseChange {D : Type u} [Category.{v} D] [HasPushouts D]
    (P : MorphismProperty D) [P.IsStableUnderCobaseChange]
    (hP : MorphismProperty.isomorphisms D ≤ P) :
    P.multiplicativeClosure.IsStableUnderCobaseChange where
  of_isPushout := by
    intro A A' B B' f g f' g' sq hf
    induction hf generalizing B B' with
    | of f hf => exact .of _ (MorphismProperty.IsStableUnderCobaseChange.of_isPushout sq hf)
    | id A =>
        haveI : IsIso f' := sq.isIso_inl_of_isIso
        exact .of _ (hP _ (inferInstance : IsIso f'))
    | comp_of f h hf hh ih =>
        let mid := pushout g f
        let j : B ⟶ mid := pushout.inl g f
        let k : _ ⟶ mid := pushout.inr g f
        let t : mid ⟶ B' := pushout.desc f' (h ≫ g') (by simpa using sq.w)
        have first : IsPushout g f j k := IsPushout.of_hasPushout g f
        have outer : IsPushout g (f ≫ h) (j ≫ t) g' := by
          simpa only [j, t, pushout.inl_desc] using sq
        have second : IsPushout k h t g' :=
          outer.of_top (by simp only [k, t, pushout.inr_desc]) first
        have hj := ih first
        have ht := MorphismProperty.IsStableUnderCobaseChange.of_isPushout (P := P) second hh
        have H := P.multiplicativeClosure.comp_mem j t hj (.of _ ht)
        simpa only [j, t, pushout.inl_desc] using H

instance cellSteps_cobaseChange :
    (Top.cellBoundaries.{u}.pushouts ⊔
      MorphismProperty.isomorphisms TopCat.{u}).IsStableUnderCobaseChange where
  of_isPushout := by
    intro A A' B B' f g f' g' sq hf
    rcases hf with hf | hf
    · exact Or.inl (MorphismProperty.IsStableUnderCobaseChange.of_isPushout sq hf)
    · haveI : IsIso f := hf
      exact Or.inr sq.isIso_inl_of_isIso

instance relFinCell_cobaseChange :
    Top.relativeFiniteCellComplexes.{u}.IsStableUnderCobaseChange :=
  multiplicativeClosure_cobaseChange _ le_sup_right

end CellComplexes

section HomotopyEquivalences

/-- Homotopic maps of spaces. -/
abbrev HT {X Y : TopCat.{u}} (f g : X ⟶ Y) : Prop := f.hom.Homotopic g.hom

theorem HT.refl {X Y : TopCat.{u}} (f : X ⟶ Y) : HT f f := ContinuousMap.Homotopic.refl _

theorem HT.symm {X Y : TopCat.{u}} {f g : X ⟶ Y} (h : HT f g) : HT g f :=
  ContinuousMap.Homotopic.symm h

theorem HT.trans {X Y : TopCat.{u}} {f g k : X ⟶ Y} (h : HT f g) (h' : HT g k) : HT f k :=
  ContinuousMap.Homotopic.trans h h'

theorem HT.comp {X Y Z : TopCat.{u}} {f f' : X ⟶ Y} {g g' : Y ⟶ Z} (hf : HT f f')
    (hg : HT g g') : HT (f ≫ g) (f' ≫ g') :=
  ContinuousMap.Homotopic.comp hg hf

theorem hoeq_of_isIso {X Y : TopCat.{u}} (f : X ⟶ Y) [IsIso f] : Top.homotopyEquivalences f :=
  ⟨inv f, by rw [IsIso.hom_inv_id], by rw [IsIso.inv_hom_id]⟩

theorem hoeq_comp {X Y Z : TopCat.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : Top.homotopyEquivalences f) (hg : Top.homotopyEquivalences g) :
    Top.homotopyEquivalences (f ≫ g) :=
  Top.homotopyEquivalences.comp_mem _ _ hf hg

theorem hoeq_of_comp_left {X Y Z : TopCat.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : Top.homotopyEquivalences f) (hfg : Top.homotopyEquivalences (f ≫ g)) :
    Top.homotopyEquivalences g :=
  Top.homotopyEquivalences.of_precomp f g hf hfg

theorem hoeq_of_comp_right {X Y Z : TopCat.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hg : Top.homotopyEquivalences g) (hfg : Top.homotopyEquivalences (f ≫ g)) :
    Top.homotopyEquivalences f :=
  Top.homotopyEquivalences.of_postcomp f g hg hfg

/-- Homotopy equivalences satisfy 2-out-of-6. -/
theorem hoeq_twoOutOfSix : TwoOutOfSix TopCat.{u} Top.homotopyEquivalences := by
  intro X Y Z T f g h hfg hgh
  obtain ⟨a, -, ha₂⟩ := id hfg
  obtain ⟨b, hb₁, -⟩ := id hgh
  have hl : HT ((a ≫ f) ≫ g) (𝟙 Z) := by simpa only [Category.assoc] using ha₂
  have hr : HT (g ≫ h ≫ b) (𝟙 Y) := by simpa only [Category.assoc] using hb₁
  have hg : Top.homotopyEquivalences g := by
    refine ⟨h ≫ b, hr, ?_⟩
    have s₁ : HT ((h ≫ b) ≫ g) (((a ≫ f) ≫ g) ≫ ((h ≫ b) ≫ g)) := by
      simpa only [Category.id_comp] using HT.comp hl.symm (HT.refl ((h ≫ b) ≫ g))
    have s₂ : HT (((a ≫ f) ≫ g) ≫ ((h ≫ b) ≫ g)) ((a ≫ f) ≫ g) := by
      have := HT.comp (HT.refl (a ≫ f)) (HT.comp hr (HT.refl g))
      simpa only [Category.assoc, Category.id_comp] using this
    exact (s₁.trans s₂).trans hl
  have hh : Top.homotopyEquivalences h := hoeq_of_comp_left hg hgh
  refine ⟨hoeq_of_comp_right hg hfg, hg, hh, ?_⟩
  rw [← Category.assoc]
  exact hoeq_comp hfg hh

/-- A map between contractible spaces is a homotopy equivalence. -/
theorem hoeq_of_contractibleSpace {X Y : TopCat.{u}} [ContractibleSpace X] [ContractibleSpace Y]
    (f : X ⟶ Y) : Top.homotopyEquivalences f := by
  obtain ⟨x, hx⟩ := id_nullhomotopic X
  obtain ⟨y, hy⟩ := id_nullhomotopic Y
  let g : Y ⟶ X := TopCat.ofHom (ContinuousMap.const Y x)
  refine ⟨g, ?_, ?_⟩
  · change (g.hom.comp f.hom).Homotopic (ContinuousMap.id X)
    simpa [g, ContinuousMap.comp_apply] using hx.symm
  · let c : C(Y, Y) := ContinuousMap.const Y (f.hom x)
    have hc : c.Homotopic (ContinuousMap.id Y) := by
      have hcy : c.Homotopic (ContinuousMap.const Y y) := by
        simpa [c] using hy.comp (ContinuousMap.Homotopic.refl c)
      exact hcy.trans hy.symm
    change (f.hom.comp g.hom).Homotopic (ContinuousMap.id Y)
    simpa [g, c, ContinuousMap.comp_apply] using hc

theorem contractibleSpace_stdSimplex (n : ℕ) :
    ContractibleSpace (Convexity.StdSimplex ℝ (Fin (n + 1))) := by
  have he := Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))
  have hc : Convex ℝ (Set.range
      (fun t : Convexity.StdSimplex ℝ (Fin (n + 1)) => (t.weights : Fin (n + 1) → ℝ))) := by
    rw [Convexity.StdSimplex.range_toFun_comp_weights]
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq] at hx hy ⊢
    refine ⟨fun i => ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [hx.1 i, hy.1 i]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, hx.2, hy.2]
      linarith
  have := hc.contractibleSpace (Set.range_nonempty _)
  exact he.toHomeomorph.contractibleSpace_iff.mpr inferInstance

instance contractibleSpace_toTop (n : ℕ) :
    ContractibleSpace (SemiSSet.toTop.{u}.obj (Henry.SemiSimplexCategory.mk n)) := by
  have := contractibleSpace_stdSimplex n
  exact (Homeomorph.ulift.{u} (X := Convexity.StdSimplex ℝ (Fin (n + 1)))).contractibleSpace_iff.mpr
    inferInstance

end HomotopyEquivalences

end HomotopyHypothesis.Realization.SemisimplicialComparison
