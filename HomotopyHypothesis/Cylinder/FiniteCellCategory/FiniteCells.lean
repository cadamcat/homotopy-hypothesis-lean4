import HomotopyHypothesis.Blueprint.Defs
noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Blueprint HomotopyHypothesis.Henry

namespace HomotopyHypothesis.Cylinder.FiniteCellCategory

universe u v

section Closure

variable {K : Type u} [Category.{v} K] [HasPushouts K]
variable (P : MorphismProperty K) [P.IsStableUnderCobaseChange]
  (hIso : MorphismProperty.isomorphisms K ≤ P)

include hIso in
 theorem multiplicativeClosure_cobaseChange {A B X Q : K} (i : A ⟶ B)
    (hi : P.multiplicativeClosure i) (f : A ⟶ X) (k : B ⟶ Q) (j : X ⟶ Q)
    (sq : IsPushout i f k j) : P.multiplicativeClosure j := by
  induction hi generalizing X Q with
  | of i hi => exact .of j (P.of_isPushout sq.flip hi)
  | id A =>
    have : IsIso j := sq.isIso_inr_of_isIso
    exact .of j (hIso j inferInstance)
  | @comp_of A B D i l hi hl ih =>
    let t := pushout.inl i f
    let s := pushout.inr i f
    have left : IsPushout i f t s := .of_hasPushout i f
    let d : pushout i f ⟶ Q := left.desc (l ≫ k) j (by simpa only [Category.assoc] using sq.w)
    have right : IsPushout l t k d :=
      IsPushout.of_left' sq left
    have hs : P.multiplicativeClosure s := ih f t s left
    have hd : P d := P.of_isPushout right.flip hl
    have hj : s ≫ d = j := left.inr_desc _ _ _
    rw [← hj]
    exact .comp_of s d hs hd

end Closure

variable {C : GlobularTheory.{u}}

instance finiteCellMaps_multiplicative (C : GlobularTheory.{u}) :
    (finiteCellMaps C).IsMultiplicative := by
  unfold finiteCellMaps
  infer_instance

 theorem finiteCellMaps_isomorphisms (C : GlobularTheory.{u}) :
    MorphismProperty.isomorphisms C.Model ≤ finiteCellMaps C := by
  intro X Y f hf
  exact .of f (Or.inr hf)

 theorem finiteCellMaps_le_cofibrations (C : GlobularTheory.{u}) :
    finiteCellMaps C ≤ (MorphismProperty.ofHoms (fun n : ℕ => I C n)).rlp.llp := by
  unfold finiteCellMaps
  apply (MorphismProperty.multiplicativeClosure_le_iff
    ((MorphismProperty.ofHoms (fun n : ℕ => I C n)).pushouts ⊔
      MorphismProperty.isomorphisms C.Model)
    (MorphismProperty.ofHoms (fun n : ℕ => I C n)).rlp.llp).2
  exact sup_le (MorphismProperty.pushouts_le_llp_rlp _)
    (fun _ _ f hf => by letI := hf; exact MorphismProperty.llp_of_isIso _ f)

instance finiteCellMaps_cobaseChange (C : GlobularTheory.{u}) :
    (finiteCellMaps C).IsStableUnderCobaseChange where
  of_isPushout sq hi := by
    let P := (MorphismProperty.ofHoms (fun n : ℕ => I C n)).pushouts ⊔
      MorphismProperty.isomorphisms C.Model
    have : P.IsStableUnderCobaseChange := ⟨by
      intro A A' B B' f g f' g' sq hf
      rcases hf with hf | hf
      · exact Or.inl (MorphismProperty.of_isPushout sq hf)
      · exact Or.inr (MorphismProperty.of_isPushout sq hf)⟩
    exact multiplicativeClosure_cobaseChange P (fun _ _ _ h => Or.inr h) _ hi _ _ _ sq.flip

 theorem isFinitelyCellular_of_finiteCellMap {X Y : C.Model}
    (hX : IsFinitelyCellular C X) (f : X ⟶ Y) (hf : finiteCellMaps C f) :
    IsFinitelyCellular C Y := by
  change finiteCellMaps C (initial.to Y)
  have h := (finiteCellMaps C).comp_mem (initial.to X) f hX hf
  simpa only [initial.to_comp] using h

 theorem initial_finitelyCellular (C : GlobularTheory.{u}) :
    IsFinitelyCellular C (⊥_ C.Model) := by
  have h : initial.to (⊥_ C.Model) = 𝟙 _ := initialIsInitial.hom_ext _ _
  rw [IsFinitelyCellular, h]
  exact (finiteCellMaps C).id_mem _

end HomotopyHypothesis.Cylinder.FiniteCellCategory
