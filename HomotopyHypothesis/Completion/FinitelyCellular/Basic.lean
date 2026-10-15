import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Interfaces.DiskFinitelyCellular
/-
# Finite cell maps for the equivalence between models and the completion.

The category of finitely cellular models of a globular theory and its
completion. This file collects the elementary closure properties of finite
cell maps used in the comparison.
-/

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck
open HomotopyHypothesis.Blueprint
open HomotopyHypothesis.Henry

noncomputable section

namespace HomotopyHypothesis.Completion.FinitelyCellular

universe u

variable {C : GlobularTheory.{u}}

/-- The generating inclusions lie in the finite cell maps. -/
theorem I_mem_finiteCellMaps (n : ℕ) :
    finiteCellMaps C (GlobularTheory.Model.I C n) := by
  apply MorphismProperty.le_multiplicativeClosure
  rw [MorphismProperty.sup_iff]
  left
  apply MorphismProperty.le_pushouts
  exact MorphismProperty.ofHoms.mk n

/-- Isomorphisms lie in the finite cell maps. -/
theorem iso_mem_finiteCellMaps {X Y : C.Model} (f : X ⟶ Y) [IsIso f] :
    finiteCellMaps C f := by
  apply MorphismProperty.le_multiplicativeClosure
  rw [MorphismProperty.sup_iff]
  right
  exact MorphismProperty.isomorphisms.infer_property f

/-- The identity lies in the finite cell maps. -/
theorem id_mem_finiteCellMaps (X : C.Model) :
    finiteCellMaps C (𝟙 X) :=
  iso_mem_finiteCellMaps (𝟙 X)

instance : (finiteCellMaps C).IsMultiplicative :=
  inferInstanceAs (MorphismProperty.multiplicativeClosure _).IsMultiplicative

/-- The initial model is finitely cellular. -/
theorem initial_mem : IsFinitelyCellular C (⊥_ C.Model) := by
  show finiteCellMaps C (initial.to _)
  have h : initial.to (⊥_ C.Model) = 𝟙 (⊥_ C.Model) := by
    apply initial.hom_ext
  rw [h]
  exact id_mem_finiteCellMaps _

/-- Finite cell maps are stable under pushout. -/
instance finiteCellMaps_stable : (finiteCellMaps C).IsStableUnderCobaseChange := by
  -- First the generators are stable.
  have hbase : ((MorphismProperty.ofHoms (fun n : ℕ => GlobularTheory.Model.I C n)).pushouts ⊔
      MorphismProperty.isomorphisms C.Model).IsStableUnderCobaseChange := by
    constructor
    intro A A' B B' f g f' g' sq hf
    rw [MorphismProperty.sup_iff] at hf ⊢
    cases hf with
    | inl h =>
      exact Or.inl
        (MorphismProperty.IsStableUnderCobaseChange.of_isPushout sq h)
    | inr h =>
      haveI := h
      have hI : IsIso f' := sq.isIso_inl_of_isIso
      exact Or.inr hI
  -- Then the multiplicative closure of a stable class containing isos is stable.
  -- We prove: pushout of a closure map is a closure map, by induction on the closure.
  have key : ∀ {A A' : C.Model} (f : A ⟶ A'), finiteCellMaps C f →
      ∀ (B B' : C.Model) (g : A ⟶ B) (f' : B ⟶ B') (g' : A' ⟶ B'),
        IsPushout g f f' g' → finiteCellMaps C f' := by
    intro A A' f hf
    induction hf with
    | of _ h =>
      intro B B' g f' g' sq
      apply MorphismProperty.le_multiplicativeClosure
      exact hbase.of_isPushout sq h
    | id X =>
      intro B B' g f' g' sq
      haveI : IsIso (𝟙 X) := inferInstance
      have hI : IsIso f' := sq.isIso_inl_of_isIso
      exact iso_mem_finiteCellMaps f'
    | comp_of a b ha hb ih1 =>
      intro B B' g f' g' sq
      -- Factor the pushout of the composite through the pushout of `a`.
      have sq1 : IsPushout a g (pushout.inl a g) (pushout.inr a g) :=
        IsPushout.of_hasPushout a g
      have sqFlip := sq.flip
      have sq2 := sqFlip.of_left' sq1
      have hfa : finiteCellMaps C (pushout.inr a g) := ih1 B _ g _ _ sq1.flip
      have hfb : finiteCellMaps C (sq1.desc (b ≫ g') f' (by
        rw [← Category.assoc, sqFlip.w])) := by
        apply MorphismProperty.le_multiplicativeClosure
        exact hbase.of_isPushout sq2.flip hb
      have hfac : f' = pushout.inr a g ≫ sq1.desc (b ≫ g') f' (by
        rw [← Category.assoc, sqFlip.w]) := (sq1.inr_desc _ _ _).symm
      rw [hfac]
      exact MorphismProperty.comp_mem _ _ _ hfa hfb
  constructor
  intro A A' B B' f g f' g' sq hf
  exact key f hf B B' g f' g' sq

/-- Pushouts of the generating inclusions lie in the finite cell maps. -/
theorem pushout_inl_mem (n : ℕ) :
    finiteCellMaps C (pushout.inl (GlobularTheory.Model.I C n)
      (GlobularTheory.Model.I C n)) := by
  apply MorphismProperty.le_multiplicativeClosure
  rw [MorphismProperty.sup_iff]
  left
  exact MorphismProperty.pushouts_mk _
    (IsPushout.of_hasPushout _ _) (MorphismProperty.ofHoms.mk n)

/-- The other pushout inclusion. -/
theorem pushout_inr_mem (n : ℕ) :
    finiteCellMaps C (pushout.inr (GlobularTheory.Model.I C n)
      (GlobularTheory.Model.I C n)) := by
  apply MorphismProperty.le_multiplicativeClosure
  rw [MorphismProperty.sup_iff]
  left
  exact MorphismProperty.pushouts_mk _
    (IsPushout.of_hasPushout _ _).flip (MorphismProperty.ofHoms.mk n)

/-- The source inclusions `J` are finite cell maps. -/
theorem J_mem_finiteCellMaps (n : ℕ) :
    finiteCellMaps C (GlobularTheory.Model.J C n) := by
  -- `J n = inl ≫ I (n+1)` where `inl` is a pushout of `I n`.
  have hInl : finiteCellMaps C (pushout.inl
      (GlobularTheory.Model.I C n) (GlobularTheory.Model.I C n)) :=
    pushout_inl_mem n
  have hI : finiteCellMaps C (GlobularTheory.Model.I C (n + 1)) :=
    I_mem_finiteCellMaps (n + 1)
  have heq : GlobularTheory.Model.J C n =
      pushout.inl (GlobularTheory.Model.I C n)
        (GlobularTheory.Model.I C n) ≫ GlobularTheory.Model.I C (n + 1) := by
    -- `I (n+1) = desc J targetDisk`, so `inl ≫ desc = J`.
    have hdesc : GlobularTheory.Model.I C (n + 1) =
        pushout.desc (GlobularTheory.Model.J C n)
          (GlobularTheory.Model.targetDisk C n)
          (by
            have hfc := (GlobularTheory.Model.boundaryRepresentation C n).face_condition
            -- `face_condition : I n ≫ J n = I n ≫ targetDisk n`
            exact hfc) := rfl
    rw [hdesc]
    exact (pushout.inl_desc _ _ _).symm
  rw [heq]
  exact MorphismProperty.comp_mem _ _ _ hInl hI

/-- The target inclusions are finite cell maps. -/
theorem targetDisk_mem_finiteCellMaps (n : ℕ) :
    finiteCellMaps C (GlobularTheory.Model.targetDisk C n) := by
  have hInr : finiteCellMaps C (pushout.inr
      (GlobularTheory.Model.I C n) (GlobularTheory.Model.I C n)) :=
    pushout_inr_mem n
  have hI : finiteCellMaps C (GlobularTheory.Model.I C (n + 1)) :=
    I_mem_finiteCellMaps (n + 1)
  have heq : GlobularTheory.Model.targetDisk C n =
      pushout.inr (GlobularTheory.Model.I C n)
        (GlobularTheory.Model.I C n) ≫ GlobularTheory.Model.I C (n + 1) := by
    have hdesc : GlobularTheory.Model.I C (n + 1) =
        pushout.desc (GlobularTheory.Model.J C n)
          (GlobularTheory.Model.targetDisk C n)
          (by
            have hfc := (GlobularTheory.Model.boundaryRepresentation C n).face_condition
            exact hfc) := rfl
    rw [hdesc]
    exact (pushout.inr_desc _ _ _).symm
  rw [heq]
  exact MorphismProperty.comp_mem _ _ _ hInr hI

/-- Boundary disks are finitely cellular. -/
theorem boundaryDisk_mem (n : ℕ) :
    IsFinitelyCellular C (GlobularTheory.Model.boundaryDisk C n) := by
  induction n with
  | zero =>
    -- `boundaryDisk 0 = ⊥` definitionally.
    exact initial_mem
  | succ n ih =>
    -- `boundaryDisk (n+1)` is the pushout `disk n ⊔_{boundaryDisk n} disk n`.
    show finiteCellMaps C (initial.to _)
    have hdisk : finiteCellMaps C
        (initial.to (GlobularTheory.Model.disk C n)) :=
      Packages.disk_finitelyCellular C n
    have hinl : finiteCellMaps C (pushout.inl
        (GlobularTheory.Model.I C n) (GlobularTheory.Model.I C n)) :=
      pushout_inl_mem n
    have heq : initial.to (GlobularTheory.Model.boundaryDisk C (n + 1)) =
        initial.to (GlobularTheory.Model.disk C n) ≫
          pushout.inl (GlobularTheory.Model.I C n)
            (GlobularTheory.Model.I C n) := by
      apply Subsingleton.elim
    rw [heq]
    exact MorphismProperty.comp_mem _ _ _ hdisk hinl

/-- Faces between globes give finite cell maps after applying `freeShapeMap`. -/
theorem face_mem_finiteCellMaps {m n : ℕ} (h : m < n) (side : Bool) :
    finiteCellMaps C (GlobularTheory.Model.freeShapeMap C
      (OAI.Grothendieck.Shape.face h side)) := by
  -- Induction on `n` generalizing `m` and `side`.
  induction n generalizing m side with
  | zero =>
    omega
  | succ n ih =>
    by_cases hm : m = n
    · -- Base: `m = n`, so `n+1 = m+1`; the face is a source or target.
      subst hm
      cases side with
      | false =>
        -- `face = source`, whose image is `J`.
        have heq : OAI.Grothendieck.Shape.face h false =
            OAI.Grothendieck.Shape.source m := rfl
        rw [heq]
        -- `freeShapeMap source = J` definitionally.
        exact J_mem_finiteCellMaps m
      | true =>
        have heq : OAI.Grothendieck.Shape.face h true =
            OAI.Grothendieck.Shape.target m := rfl
        rw [heq]
        exact targetDisk_mem_finiteCellMaps m
    · -- Step: `m < n`, factor through `n`.
      have hmn : m < n := by omega
      have hn : n < n + 1 := Nat.lt_succ_self n
      have hGlobe : OAI.Grothendieck.Globe.face h side =
          OAI.Grothendieck.Globe.face hmn side ≫
            OAI.Grothendieck.Globe.face hn false := rfl
      have hfac : OAI.Grothendieck.Shape.face h side =
          OAI.Grothendieck.Shape.face hmn side ≫
            OAI.Grothendieck.Shape.face hn false := by
        have e1 : OAI.Grothendieck.Shape.face h side =
            OAI.Grothendieck.GlobularPresheaf.face h side := rfl
        have e2 : OAI.Grothendieck.Shape.face hmn side =
            OAI.Grothendieck.GlobularPresheaf.face hmn side := rfl
        have e3 : OAI.Grothendieck.Shape.face hn false =
            OAI.Grothendieck.GlobularPresheaf.face hn false := rfl
        rw [e1, e2, e3]
        have f1 : OAI.Grothendieck.GlobularPresheaf.face h side =
            uliftYoneda.map (OAI.Grothendieck.Globe.face h side) := rfl
        have f2 : OAI.Grothendieck.GlobularPresheaf.face hmn side =
            uliftYoneda.map (OAI.Grothendieck.Globe.face hmn side) := rfl
        have f3 : OAI.Grothendieck.GlobularPresheaf.face hn false =
            uliftYoneda.map (OAI.Grothendieck.Globe.face hn false) := rfl
        rw [f1, f2, f3, hGlobe]
        exact Functor.map_comp _ _ _
      rw [hfac]
      -- `freeShapeMap` preserves composition.
      have hcomp : GlobularTheory.Model.freeShapeMap C
          (OAI.Grothendieck.Shape.face hmn side ≫
            OAI.Grothendieck.Shape.face hn false) =
          GlobularTheory.Model.freeShapeMap C
            (OAI.Grothendieck.Shape.face hmn side) ≫
          GlobularTheory.Model.freeShapeMap C
            (OAI.Grothendieck.Shape.face hn false) := by
        show yoneda.map (C.toTheoryData.arity.map (_ ≫ _)) =
          yoneda.map (C.toTheoryData.arity.map _) ≫
            yoneda.map (C.toTheoryData.arity.map _)
        rw [C.toTheoryData.arity.map_comp, yoneda.map_comp]
      rw [hcomp]
      exact MorphismProperty.comp_mem _ _ _ (ih hmn side)
        (J_mem_finiteCellMaps n)

end HomotopyHypothesis.Completion.FinitelyCellular
