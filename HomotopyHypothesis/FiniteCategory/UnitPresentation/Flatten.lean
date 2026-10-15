import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.SetTheory.Cardinal.Order
/-!
# Attaching the cells of a relative cell complex one at a time

A relative cell complex attaches, at each step `j`, a coproduct of cells. Well-ordering the set of
all cells, we index the stages by pairs `(j, x)` ordered lexicographically, where `x` runs through
the cells (with a bottom and a top element added): the stage `(j, x)` is obtained from the `j`-th
stage by attaching the cells of step `j` which are smaller than `x`. Consecutive stages differ by at
most one cell, so the relative cell complex is a transfinite composition of pushouts of single cells
and isomorphisms.
-/

universe w t v u

open CategoryTheory Limits HomotopicalAlgebra

namespace HomotopyHypothesis.FiniteCategory.UnitPresentation.Flatten

/-- A type with a chosen well-order. -/
def WO (α : Type*) := α

noncomputable instance (α : Type*) : LinearOrder (WO α) :=
  WellOrderingRel.isWellOrder.linearOrder

instance (α : Type*) : WellFoundedLT (WO α) :=
  (WellOrderingRel.isWellOrder (α := α)).wf

variable {C : Type u} [Category.{v} C] [HasColimitsOfSize.{w, w} C]
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {α : J → Type t} {A B : (j : J) → α j → C} {basicCell : (j : J) → (i : α j) → A j i ⟶ B j i}
  {X Y : C} {f : X ⟶ Y} (c : RelativeCellComplex.{w} basicCell f)

/-- The positions inside a step: the cells, with a bottom and a top element. -/
abbrev Pos := WithTop (WithBot (WO c.Cells))

/-- The position of a cell. -/
def toPos (γ : c.Cells) : Pos c := WithTop.some (WithBot.some (show WO c.Cells from γ))

/-- The index of the flattened composition. -/
abbrev Idx := J ×ₗ Pos c

variable {c}

/-- The cells attached at a stage `(j, x)`: the cells of step `j` smaller than `x`. -/
abbrev Q (s : Idx c) : Type w := {γ : c.Cells // γ.j = (ofLex s).1 ∧ toPos c γ < (ofLex s).2}

/-- The attaching map of a cell. -/
def attachMap (γ : c.Cells) : A γ.j γ.i ⟶ c.F.obj γ.j :=
  (c.attachCells γ.j γ.hj).cofan₁.inj γ.k ≫ (c.attachCells γ.j γ.hj).g₁

/-- The characteristic map of a cell. -/
def cellMap (γ : c.Cells) : B γ.j γ.i ⟶ c.F.obj (Order.succ γ.j) :=
  (c.attachCells γ.j γ.hj).cell γ.k

@[reassoc]
lemma attachMap_w (γ : c.Cells) :
    attachMap γ ≫ c.F.map (homOfLE (Order.le_succ γ.j)) = basicCell γ.j γ.i ≫ cellMap γ := by
  have h := (c.attachCells γ.j γ.hj).isPushout.w
  have h1 := (c.attachCells γ.j γ.hj).hm γ.k
  change ((c.attachCells γ.j γ.hj).cofan₁.inj γ.k ≫ (c.attachCells γ.j γ.hj).g₁) ≫
      c.F.map (homOfLE (Order.le_succ γ.j)) =
    basicCell γ.j ((c.attachCells γ.j γ.hj).π γ.k) ≫
      ((c.attachCells γ.j γ.hj).cofan₂.inj γ.k ≫ (c.attachCells γ.j γ.hj).g₂)
  rw [Category.assoc, h, ← Category.assoc, h1, Category.assoc]

/-- The attaching map of the cells of a stage. -/
noncomputable def attach (s : Idx c) : ∐ (fun q : Q s => A q.1.j q.1.i) ⟶ c.F.obj (ofLex s).1 :=
  Sigma.desc fun q => attachMap q.1 ≫ c.F.map (homOfLE (le_of_eq q.2.1))

/-- The coproduct of the cells of a stage. -/
noncomputable def mcop (s : Idx c) :
    ∐ (fun q : Q s => A q.1.j q.1.i) ⟶ ∐ (fun q : Q s => B q.1.j q.1.i) :=
  Limits.Sigma.map fun (q : Q s) => basicCell q.1.j q.1.i

/-- The stages of the flattened composition. -/
noncomputable abbrev stage (s : Idx c) : C := pushout (attach s) (mcop s)

/-- The map from a cell to a later stage. -/
noncomputable def cellTo (s : Idx c) (γ : c.Cells) (h₁ : γ.j ≤ (ofLex s).1)
    (h₂ : γ.j = (ofLex s).1 → toPos c γ < (ofLex s).2) : B γ.j γ.i ⟶ stage s :=
  if h : γ.j = (ofLex s).1 then
    Sigma.ι (fun q : Q s => B q.1.j q.1.i) ⟨γ, h, h₂ h⟩ ≫ pushout.inr _ _
  else cellMap γ ≫ c.F.map (homOfLE (Order.succ_le_of_lt (lt_of_le_of_ne h₁ h))) ≫
    pushout.inl _ _

lemma cellTo_pos (s : Idx c) (γ : c.Cells) (h₁ : γ.j ≤ (ofLex s).1)
    (h₂ : γ.j = (ofLex s).1 → toPos c γ < (ofLex s).2) (h : γ.j = (ofLex s).1) :
    cellTo s γ h₁ h₂ =
      Sigma.ι (fun q : Q s => B q.1.j q.1.i) ⟨γ, h, h₂ h⟩ ≫ pushout.inr _ _ := dif_pos h

lemma cellTo_neg (s : Idx c) (γ : c.Cells) (h₁ : γ.j ≤ (ofLex s).1)
    (h₂ : γ.j = (ofLex s).1 → toPos c γ < (ofLex s).2) (h : ¬ γ.j = (ofLex s).1) :
    cellTo s γ h₁ h₂ = cellMap γ ≫
      c.F.map (homOfLE (Order.succ_le_of_lt (lt_of_le_of_ne h₁ h))) ≫ pushout.inl _ _ :=
  dif_neg h

@[reassoc]
lemma ι_attach (s : Idx c) (q : Q s) :
    Sigma.ι (fun q : Q s => A q.1.j q.1.i) q ≫ attach s =
      attachMap q.1 ≫ c.F.map (homOfLE (le_of_eq q.2.1)) := by
  simp [attach]

@[reassoc]
lemma ι_mcop (s : Idx c) (q : Q s) :
    Sigma.ι (fun q : Q s => A q.1.j q.1.i) q ≫ mcop s =
      basicCell q.1.j q.1.i ≫ Sigma.ι (fun q : Q s => B q.1.j q.1.i) q := by
  simp [mcop]

lemma basicCell_cellTo (s : Idx c) (γ : c.Cells) (h₁ : γ.j ≤ (ofLex s).1)
    (h₂ : γ.j = (ofLex s).1 → toPos c γ < (ofLex s).2) :
    basicCell γ.j γ.i ≫ cellTo s γ h₁ h₂ =
      attachMap γ ≫ c.F.map (homOfLE h₁) ≫ pushout.inl _ _ := by
  by_cases h : γ.j = (ofLex s).1
  · rw [cellTo_pos _ _ _ _ h]
    have := pushout.condition (f := attach s) (g := mcop s)
    have := congrArg (fun φ => Sigma.ι (fun q : Q s => A q.1.j q.1.i) ⟨γ, h, h₂ h⟩ ≫ φ) this
    dsimp only at this
    rw [ι_attach_assoc, ι_mcop_assoc] at this
    exact this.symm
  · rw [cellTo_neg _ _ _ _ h, ← Category.assoc (basicCell _ _), ← attachMap_w, Category.assoc,
      ← Functor.map_comp_assoc]
    rfl

lemma le_fst {s s' : Idx c} (h : s ≤ s') : (ofLex s).1 ≤ (ofLex s').1 := by
  rcases Prod.Lex.le_iff.1 h with h | ⟨h, -⟩
  · exact h.le
  · exact h.le

lemma lt_snd_of_eq {s s' : Idx c} (h : s ≤ s') (q : Q s) (e : q.1.j = (ofLex s').1) :
    toPos c q.1 < (ofLex s').2 := by
  rcases Prod.Lex.le_iff.1 h with h' | ⟨h', h''⟩
  · exact absurd (q.2.1 ▸ e ▸ h') (lt_irrefl _)
  · exact lt_of_lt_of_le q.2.2 h''

/-- The maps between stages. -/
noncomputable def stageMap {s s' : Idx c} (h : s ≤ s') : stage s ⟶ stage s' :=
  pushout.desc (c.F.map (homOfLE (le_fst h)) ≫ pushout.inl _ _)
    (Sigma.desc fun q => cellTo s' q.1 ((le_of_eq q.2.1).trans (le_fst h)) (lt_snd_of_eq h q)) (by
      apply Sigma.hom_ext
      intro q
      rw [ι_attach_assoc, ι_mcop_assoc, Sigma.ι_comp_desc, basicCell_cellTo, ← Functor.map_comp_assoc]
      rfl)

@[reassoc (attr := simp)]
lemma inl_stageMap {s s' : Idx c} (h : s ≤ s') :
    pushout.inl _ _ ≫ stageMap h = c.F.map (homOfLE (le_fst h)) ≫ pushout.inl _ _ :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
lemma ι_inr_stageMap {s s' : Idx c} (h : s ≤ s') (q : Q s) :
    Sigma.ι (fun q : Q s => B q.1.j q.1.i) q ≫ pushout.inr _ _ ≫ stageMap h =
      cellTo s' q.1 ((le_of_eq q.2.1).trans (le_fst h)) (lt_snd_of_eq h q) := by
  rw [stageMap, pushout.inr_desc, Sigma.ι_comp_desc]

lemma cellTo_stageMap {s s' : Idx c} (h : s ≤ s') (γ : c.Cells) (h₁ : γ.j ≤ (ofLex s).1)
    (h₂ : γ.j = (ofLex s).1 → toPos c γ < (ofLex s).2) :
    cellTo s γ h₁ h₂ ≫ stageMap h = cellTo s' γ (h₁.trans (le_fst h))
      (fun e => by
        by_cases e' : γ.j = (ofLex s).1
        · exact lt_snd_of_eq h ⟨γ, e', h₂ e'⟩ e
        · exfalso
          exact e' (le_antisymm h₁ (e ▸ le_fst h))) := by
  by_cases e : γ.j = (ofLex s).1
  · rw [cellTo_pos _ _ _ _ e, Category.assoc, ι_inr_stageMap]
  · have e' : ¬ γ.j = (ofLex s').1 := fun e' => e (le_antisymm h₁ (e' ▸ le_fst h))
    rw [cellTo_neg _ _ _ _ e, cellTo_neg _ _ _ _ e', Category.assoc, Category.assoc,
      inl_stageMap, ← Functor.map_comp_assoc]
    rfl

/-- The flattened functor. -/
@[simps]
noncomputable def functor : Idx c ⥤ C where
  obj := stage
  map φ := stageMap (leOfHom φ)
  map_id s := by
    apply pushout.hom_ext
    · rw [inl_stageMap, Category.comp_id]
      simp [homOfLE_refl]
    · apply Sigma.hom_ext
      intro q
      rw [Category.comp_id, ι_inr_stageMap, cellTo_pos _ _ _ _ q.2.1]
  map_comp {s s' s''} φ ψ := by
    apply pushout.hom_ext
    · simp only [inl_stageMap, inl_stageMap_assoc, Category.assoc, ← Functor.map_comp_assoc]
      rfl
    · apply Sigma.hom_ext
      intro q
      rw [ι_inr_stageMap, ← Category.assoc, ← Category.assoc, Category.assoc _ (pushout.inr _ _),
        ι_inr_stageMap, cellTo_stageMap]

section Composition

noncomputable instance : SuccOrder (Idx c) := SuccOrder.ofLinearWellFoundedLT _

/-- Stages with no cell: the inclusion of the step is an isomorphism. -/
lemma isIso_inl_of_isEmpty (s : Idx c) [IsEmpty (Q s)] :
    IsIso (pushout.inl (attach s) (mcop s)) := by
  have hA : IsInitial (∐ (fun q : Q s => A q.1.j q.1.i)) :=
    IsInitial.ofUniqueHom (fun _ => Sigma.desc fun q => isEmptyElim q)
      (fun _ _ => Sigma.hom_ext _ _ (fun q => isEmptyElim q))
  have hB : IsInitial (∐ (fun q : Q s => B q.1.j q.1.i)) :=
    IsInitial.ofUniqueHom (fun _ => Sigma.desc fun q => isEmptyElim q)
      (fun _ _ => Sigma.hom_ext _ _ (fun q => isEmptyElim q))
  have : IsIso (mcop s) := ⟨⟨hB.to _, hA.hom_ext _ _, hB.hom_ext _ _⟩⟩
  infer_instance

instance : IsEmpty (Q (⊥ : Idx c)) :=
  ⟨fun q => (not_lt_bot : ¬ toPos c q.1 < ⊥) q.2.2⟩

/-- The legs of the flattened composition. -/
noncomputable def leg (s : Idx c) : stage s ⟶ Y :=
  pushout.desc (c.incl.app (ofLex s).1)
    (Sigma.desc fun q => cellMap q.1 ≫ c.incl.app (Order.succ q.1.j)) (by
      apply Sigma.hom_ext
      intro q
      rw [ι_attach_assoc, ι_mcop_assoc, Sigma.ι_comp_desc, ← attachMap_w_assoc]
      have h1 := c.incl.naturality (homOfLE (le_of_eq q.2.1))
      have h2 := c.incl.naturality (homOfLE (Order.le_succ q.1.j))
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at h1 h2
      rw [h1, h2])

@[reassoc (attr := simp)]
lemma inl_leg (s : Idx c) : pushout.inl _ _ ≫ leg s = c.incl.app (ofLex s).1 :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
lemma ι_inr_leg (s : Idx c) (q : Q s) :
    Sigma.ι (fun q : Q s => B q.1.j q.1.i) q ≫ pushout.inr _ _ ≫ leg s =
      cellMap q.1 ≫ c.incl.app (Order.succ q.1.j) := by
  rw [leg, pushout.inr_desc, Sigma.ι_comp_desc]

lemma cellTo_leg (s : Idx c) (γ : c.Cells) (h₁ : γ.j ≤ (ofLex s).1)
    (h₂ : γ.j = (ofLex s).1 → toPos c γ < (ofLex s).2) :
    cellTo s γ h₁ h₂ ≫ leg s = cellMap γ ≫ c.incl.app (Order.succ γ.j) := by
  by_cases h : γ.j = (ofLex s).1
  · rw [cellTo_pos _ _ _ _ h, Category.assoc, ι_inr_leg]
  · rw [cellTo_neg _ _ _ _ h, Category.assoc, Category.assoc, inl_leg]
    have h1 := c.incl.naturality (homOfLE (Order.succ_le_of_lt (lt_of_le_of_ne h₁ h)))
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at h1
    rw [h1]

/-- The cocone of the flattened composition. -/
@[simps]
noncomputable def cocone : Cocone (functor (c := c)) where
  pt := Y
  ι :=
    { app := leg
      naturality {s s'} φ := by
        change stageMap (leOfHom φ) ≫ leg s' = leg s ≫ 𝟙 _
        rw [Category.comp_id]
        apply pushout.hom_ext
        · rw [inl_stageMap_assoc, inl_leg, inl_leg]
          have h1 := c.incl.naturality (homOfLE (le_fst (leOfHom φ)))
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at h1
          exact h1
        · apply Sigma.hom_ext
          intro q
          rw [← Category.assoc, ← Category.assoc, Category.assoc _ (pushout.inr _ _),
            ι_inr_stageMap, cellTo_leg, ι_inr_leg] }

variable [NoMaxOrder J]

/-- The marker of the step `j`. -/
abbrev mark (j : J) : Idx c := toLex (j, ⊥)

lemma le_mark_succ (s : Idx c) : s ≤ mark (c := c) (Order.succ (ofLex s).1) :=
  Prod.Lex.le_iff.2 (Or.inl (Order.lt_succ (ofLex s).1))

lemma mark_le (s : Idx c) : mark (c := c) (ofLex s).1 ≤ s :=
  Prod.Lex.le_iff.2 (Or.inr ⟨rfl, bot_le⟩)

/-- The legs of a cocone of the flattened functor, typed by `stage`. -/
def sι (σ : Cocone (functor (c := c))) (s : Idx c) : stage s ⟶ σ.pt := σ.ι.app s

lemma sι_w (σ : Cocone (functor (c := c))) {s s' : Idx c} (h : s ≤ s') :
    stageMap h ≫ sι σ s' = sι σ s :=
  σ.w (homOfLE h)

lemma mark_le_mark {j j' : J} (h : j ≤ j') : mark (c := c) j ≤ mark j' :=
  Prod.Lex.le_iff.2 (by
    rcases h.lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, le_rfl⟩)

/-- The cocone of `c.F` induced by a cocone of the flattened functor. -/
noncomputable def restrictCocone (σ : Cocone (functor (c := c))) : Cocone c.F where
  pt := σ.pt
  ι :=
    { app j := pushout.inl (attach (mark j)) (mcop (mark j)) ≫ sι σ (mark j)
      naturality {j j'} φ := by
        have hm : mark (c := c) j ≤ mark j' := mark_le_mark (leOfHom φ)
        change c.F.map (homOfLE (le_fst hm)) ≫ pushout.inl _ _ ≫ sι σ (mark j') =
          (pushout.inl _ _ ≫ sι σ (mark j)) ≫ 𝟙 _
        rw [Category.comp_id, ← sι_w σ hm, inl_stageMap_assoc] }

/-- The map out of `Y` induced by a cocone of the flattened functor. -/
noncomputable def descY (σ : Cocone (functor (c := c))) : Y ⟶ σ.pt :=
  c.isColimit.desc (restrictCocone σ)

lemma incl_descY (σ : Cocone (functor (c := c))) (j : J) :
    c.incl.app j ≫ descY σ = pushout.inl (attach (mark j)) (mcop (mark j)) ≫ sι σ (mark j) :=
  c.isColimit.fac (restrictCocone σ) j

/-- The flattened composition has colimit `Y`. -/
noncomputable def isColimitCocone : IsColimit (cocone (c := c)) where
  desc σ := descY σ
  fac σ s := by
    change leg s ≫ descY σ = sι σ s
    apply pushout.hom_ext
    · rw [inl_leg_assoc, incl_descY, ← sι_w σ (mark_le s)]
      change pushout.inl (attach (mark _)) (mcop (mark _)) ≫ stageMap (mark_le s) ≫ sι σ s =
        pushout.inl _ _ ≫ sι σ s
      rw [inl_stageMap_assoc]
      have h1 : c.F.map (homOfLE (le_fst (mark_le (c := c) s))) = 𝟙 _ := by
        rw [← c.F.map_id]; rfl
      rw [h1]
      exact Category.id_comp _
    · apply Sigma.hom_ext
      intro q
      have hs : s ≤ mark (Order.succ q.1.j) := by rw [q.2.1]; exact le_mark_succ s
      rw [← Category.assoc, ← Category.assoc, Category.assoc _ (pushout.inr _ _), ι_inr_leg,
        Category.assoc, incl_descY, ← sι_w σ hs, ← Category.assoc (pushout.inr _ _),
        ← Category.assoc (Sigma.ι _ q), ι_inr_stageMap,
        cellTo_neg _ _ _ _ (fun e => (Order.lt_succ q.1.j).ne e)]
      have h1 : c.F.map (homOfLE (Order.succ_le_of_lt (lt_of_le_of_ne
          (((le_of_eq q.2.1).trans (le_fst hs))) (fun e => (Order.lt_succ q.1.j).ne e)))) =
          𝟙 (c.F.obj (Order.succ q.1.j)) := by
        rw [← c.F.map_id]; rfl
      rw [h1]
      erw [Category.id_comp]
      exact (Category.assoc _ _ _).symm
  uniq σ m hm := by
    let m' : Y ⟶ σ.pt := m
    change m' = descY σ
    have hm' : ∀ s, leg s ≫ m' = sι σ s := hm
    clear_value m'
    apply c.isColimit.hom_ext
    intro j
    change c.incl.app j ≫ m' = c.incl.app j ≫ descY σ
    rw [incl_descY, ← hm' (mark j), ← Category.assoc, inl_leg]
    rfl

end Composition

section Continuity

variable [NoMaxOrder J]

lemma fst_eq_of_between {t t' t'' : Idx c} (h₁ : t ≤ t') (h₂ : t' ≤ t'')
    (h : (ofLex t).1 = (ofLex t'').1) : (ofLex t').1 = (ofLex t).1 :=
  le_antisymm (h ▸ le_fst h₂) (le_fst h₁)

lemma lex_covBy_mark {b j : J} (h : b ⋖ j) : toLex (b, (⊤ : Pos c)) ⋖ mark (c := c) j := by
  refine ⟨Prod.Lex.lt_iff.2 (Or.inl h.1), fun z hz hz' => ?_⟩
  rcases Prod.Lex.lt_iff.1 hz with h1 | ⟨_, h2⟩
  · rcases Prod.Lex.lt_iff.1 hz' with h3 | ⟨_, h4⟩
    · exact h.2 h1 h3
    · exact (not_lt_bot : ¬ (ofLex z).2 < (⊥ : Pos c)) h4
  · exact (not_top_lt : ¬ (⊤ : Pos c) < (ofLex z).2) h2

lemma mark_not_isSuccLimit (hJ : ∀ j : J, ¬ Order.IsSuccLimit j) (j : J) :
    ¬ Order.IsSuccLimit (mark (c := c) j) := by
  intro hl
  rcases Order.not_isSuccLimit_iff.1 (hJ j) with hmin | hpre
  · apply hl.1
    intro z hz
    rcases Prod.Lex.le_iff.1 hz with h1 | ⟨h1, h2⟩
    · exact absurd (hmin h1.le) (not_le.2 h1)
    · exact Prod.Lex.le_iff.2 (Or.inr ⟨h1.symm, bot_le⟩)
  · obtain ⟨b, hb⟩ := Order.not_isSuccPrelimit_iff.1 hpre
    exact hl.2 _ (lex_covBy_mark hb)

lemma mark_lt (hJ : ∀ j : J, ¬ Order.IsSuccLimit j) {s : Idx c} (hs : Order.IsSuccLimit s) :
    mark (ofLex s).1 < s :=
  lt_of_le_of_ne (mark_le s) (fun e => mark_not_isSuccLimit hJ _ (e ▸ hs))

/-- A stage below a limit stage containing a given cell. -/
noncomputable def cellStage (s : Idx c) (q : Q s) : Idx c :=
  Order.succ (toLex ((ofLex s).1, toPos c q.1))

lemma cellStage_lt {s : Idx c} (hs : Order.IsSuccLimit s) (q : Q s) : cellStage s q < s :=
  hs.succ_lt (Prod.Lex.lt_iff.2 (Or.inr ⟨rfl, q.2.2⟩))

lemma cellStage_fst {s : Idx c} (hs : Order.IsSuccLimit s) (q : Q s) :
    (ofLex (cellStage s q)).1 = (ofLex s).1 :=
  fst_eq_of_between (t := toLex ((ofLex s).1, toPos c q.1)) (Order.le_succ _)
    (cellStage_lt hs q).le rfl

lemma cellStage_snd {s : Idx c} (hs : Order.IsSuccLimit s) (q : Q s) :
    toPos c q.1 < (ofLex (cellStage s q)).2 := by
  have h0 : toLex ((ofLex s).1, toPos c q.1) < s := Prod.Lex.lt_iff.2 (Or.inr ⟨rfl, q.2.2⟩)
  have h : toLex ((ofLex s).1, toPos c q.1) < cellStage s q :=
    Order.lt_succ_of_not_isMax (fun hm => not_le.2 h0 (hm h0.le))
  rcases Prod.Lex.lt_iff.1 h with h1 | ⟨_, h2⟩
  · exact absurd (cellStage_fst hs q) (ne_of_gt h1)
  · exact h2

/-- The cell `q` as a cell of its stage below `s`. -/
def cellAt {s : Idx c} (hs : Order.IsSuccLimit s) (q : Q s) : Q (cellStage s q) :=
  ⟨q.1, q.2.1.trans (cellStage_fst hs q).symm, cellStage_snd hs q⟩

variable (s : Idx c) (hs : Order.IsSuccLimit s)
  (σ : Cocone ((Set.principalSegIio s).monotone.functor ⋙ functor (c := c)))

/-- The legs of a cocone below `s`, typed by `stage`. -/
def τ (t : Idx c) (ht : t < s) : stage t ⟶ σ.pt := σ.ι.app ⟨t, ht⟩

lemma τ_w {t t' : Idx c} (h : t ≤ t') (ht : t < s) (ht' : t' < s) :
    stageMap h ≫ τ s σ t' ht' = τ s σ t ht :=
  σ.w (homOfLE (show (⟨t, ht⟩ : Set.Iio s) ≤ ⟨t', ht'⟩ from h))

variable (hJ : ∀ j : J, ¬ Order.IsSuccLimit j)

include hs in
lemma mark_le_cellStage (q : Q s) : mark (c := c) (ofLex s).1 ≤ cellStage s q := by
  have := mark_le (c := c) (cellStage s q)
  rwa [cellStage_fst hs q] at this

lemma le_of_mark_le {j : J} {t : Idx c} (h : mark (c := c) j ≤ t) : j ≤ (ofLex t).1 :=
  le_fst h

/-- The inclusion of the step `j` into its marker stage. -/
noncomputable def inlMark (j : J) : c.F.obj j ⟶ stage (mark (c := c) j) := pushout.inl _ _

@[reassoc]
lemma inlMark_stageMap {j : J} {t : Idx c} (h : mark (c := c) j ≤ t) :
    inlMark j ≫ stageMap h = c.F.map (homOfLE (le_of_mark_le h)) ≫ pushout.inl _ _ :=
  inl_stageMap h

include hs in
lemma cellStage_mem (q : Q s) : q.1.j = (ofLex (cellStage s q)).1 :=
  q.2.1.trans (cellStage_fst hs q).symm

/-- The inclusion of a cell of `s` into the coproduct at its stage below `s`. -/
noncomputable def ιAt (q : Q s) :
    B q.1.j q.1.i ⟶ ∐ (fun q' : Q (cellStage s q) => B q'.1.j q'.1.i) :=
  Sigma.ι (fun q' : Q (cellStage s q) => B q'.1.j q'.1.i) (cellAt hs q)



lemma snd_le_of_le {t t' : Idx c} (h : t ≤ t') (e : (ofLex t).1 = (ofLex t').1) :
    (ofLex t).2 ≤ (ofLex t').2 := by
  rcases Prod.Lex.le_iff.1 h with h' | ⟨_, h'⟩
  · exact absurd e (ne_of_lt h')
  · exact h'

@[reassoc]
lemma ιAt_inr_stageMap (q : Q s) {t' : Idx c} (h : cellStage s q ≤ t') :
    ιAt s hs q ≫ pushout.inr (attach (cellStage s q)) (mcop (cellStage s q)) ≫ stageMap h =
      cellTo t' q.1 ((le_of_eq (cellStage_mem s hs q)).trans (le_fst h))
        (fun e => lt_of_lt_of_le (cellStage_snd hs q)
          (snd_le_of_le h ((cellStage_mem s hs q).symm.trans e))) :=
  ι_inr_stageMap h (cellAt hs q)

/-- The cell relation at the stage of a cell. -/
lemma basicCell_ιAt (q : Q s) :
    basicCell q.1.j q.1.i ≫ ιAt s hs q ≫
      pushout.inr (attach (cellStage s q)) (mcop (cellStage s q)) =
    attachMap q.1 ≫ c.F.map (homOfLE (le_of_eq (cellStage_mem s hs q))) ≫
      pushout.inl (attach (cellStage s q)) (mcop (cellStage s q)) := by
  have h := basicCell_cellTo (cellStage s q) q.1 (le_of_eq (cellStage_mem s hs q))
    (fun _ => cellStage_snd hs q)
  rw [cellTo_pos _ _ _ _ (cellStage_mem s hs q)] at h
  exact h

include hJ in
lemma desc_w :
    attach s ≫ (inlMark (ofLex s).1 ≫ τ s σ _ (mark_lt hJ hs)) =
    mcop s ≫ Sigma.desc (fun q => ιAt s hs q ≫ pushout.inr _ _ ≫
      τ s σ _ (cellStage_lt hs q)) := by
  apply Sigma.hom_ext
  intro q
  rw [ι_attach_assoc, ι_mcop_assoc, Sigma.ι_comp_desc,
    ← τ_w s σ (mark_le_cellStage s hs q) (mark_lt hJ hs) (cellStage_lt hs q),
    inlMark_stageMap_assoc, reassoc_of% (basicCell_ιAt s hs q), ← Functor.map_comp_assoc]
  rfl

include hJ in
/-- The limit stages are colimits of the earlier ones. -/
noncomputable def isColimitAt :
    IsColimit ((Set.principalSegIio s).cocone (functor (c := c))) where
  desc σ := pushout.desc (inlMark (ofLex s).1 ≫ τ s σ _ (mark_lt hJ hs))
    (Sigma.desc fun q => ιAt s hs q ≫ pushout.inr _ _ ≫ τ s σ _ (cellStage_lt hs q))
    (desc_w s hs σ hJ)
  fac σ t := by
    obtain ⟨t, ht⟩ := t
    have ht : t < s := ht
    change stageMap ht.le ≫ _ = τ s σ t ht
    apply pushout.hom_ext
    · rw [inl_stageMap_assoc, pushout.inl_desc]
      have hm : max t (mark (ofLex s).1) < s := max_lt ht (mark_lt hJ hs)
      rw [← τ_w s σ (le_max_right t (mark (ofLex s).1)) (mark_lt hJ hs) hm,
        ← τ_w s σ (le_max_left t (mark (ofLex s).1)) ht hm, inlMark_stageMap_assoc,
        inl_stageMap_assoc, ← Functor.map_comp_assoc]
      rfl
    · apply Sigma.hom_ext
      intro q
      rw [ι_inr_stageMap_assoc]
      by_cases e : q.1.j = (ofLex s).1
      · rw [cellTo_pos _ _ _ _ e, Category.assoc, pushout.inr_desc, Sigma.ι_comp_desc]
        let q' : Q s := ⟨q.1, e, lt_snd_of_eq ht.le q e⟩
        have hm : max t (cellStage s q') < s := max_lt ht (cellStage_lt hs q')
        rw [← τ_w s σ (le_max_right t (cellStage s q')) (cellStage_lt hs q') hm,
          ← τ_w s σ (le_max_left t (cellStage s q')) ht hm,
          ιAt_inr_stageMap_assoc, ι_inr_stageMap_assoc]
      · rw [cellTo_neg _ _ _ _ e, Category.assoc, Category.assoc, pushout.inl_desc]
        have hlt : (ofLex t).1 < (ofLex s).1 :=
          lt_of_le_of_ne (le_fst ht.le) (fun e' => e (q.2.1.trans e'))
        have ht' : t ≤ mark (ofLex s).1 := Prod.Lex.le_iff.2 (Or.inl hlt)
        have e' : ¬ q.1.j = (ofLex (mark (c := c) (ofLex s).1)).1 := e
        rw [← τ_w s σ ht' ht (mark_lt hJ hs), ι_inr_stageMap_assoc, cellTo_neg _ _ _ _ e']
        simp only [Category.assoc]
        rfl
  uniq σ m hm := by
    let m' : stage s ⟶ σ.pt := m
    change m' = _
    have hm' : ∀ t (ht : t < s), stageMap ht.le ≫ m' = τ s σ t ht := fun t ht => hm ⟨t, ht⟩
    clear_value m'
    apply pushout.hom_ext
    · rw [pushout.inl_desc, ← hm' _ (mark_lt hJ hs), inlMark_stageMap_assoc]
      have h1 : c.F.map (homOfLE (le_of_mark_le (mark_lt (c := c) hJ hs).le)) = 𝟙 _ := by
        rw [← c.F.map_id]; rfl
      rw [h1, Category.id_comp]
    · apply Sigma.hom_ext
      intro q
      rw [pushout.inr_desc, Sigma.ι_comp_desc, ← hm' _ (cellStage_lt hs q),
        ιAt_inr_stageMap_assoc, cellTo_pos _ _ _ _ q.2.1, Category.assoc]

end Continuity

section Steps

variable [NoMaxOrder J]

lemma same_block_iff {s : Idx c} (hs : ¬ IsMax s) (e : (ofLex (Order.succ s)).1 = (ofLex s).1)
    (γ : c.Cells) :
    toPos c γ < (ofLex (Order.succ s)).2 ↔ toPos c γ ≤ (ofLex s).2 := by
  have hcov := Order.covBy_succ_of_not_isMax hs
  constructor
  · intro h
    by_contra h'
    exact hcov.2 (c := toLex ((ofLex s).1, toPos c γ))
      (Prod.Lex.lt_iff.2 (Or.inr ⟨rfl, lt_of_not_ge h'⟩))
      (Prod.Lex.lt_iff.2 (Or.inr ⟨e.symm, h⟩))
  · intro h
    rcases Prod.Lex.lt_iff.1 hcov.1 with h1 | ⟨_, h2⟩
    · exact absurd e (ne_of_gt h1)
    · exact lt_of_le_of_lt h h2

lemma block_change {s : Idx c} (hs : ¬ IsMax s) (e : (ofLex (Order.succ s)).1 ≠ (ofLex s).1) :
    (ofLex s).2 = ⊤ ∧ (ofLex (Order.succ s)).2 = ⊥ ∧
      (ofLex (Order.succ s)).1 = Order.succ (ofLex s).1 := by
  have hcov := Order.covBy_succ_of_not_isMax hs
  have hlt : (ofLex s).1 < (ofLex (Order.succ s)).1 := by
    rcases Prod.Lex.lt_iff.1 hcov.1 with h1 | ⟨h1, _⟩
    · exact h1
    · exact absurd h1.symm e
  refine ⟨?_, ?_, ?_⟩
  · by_contra h
    exact hcov.2 (c := toLex ((ofLex s).1, ⊤))
      (Prod.Lex.lt_iff.2 (Or.inr ⟨rfl, lt_top_iff_ne_top.2 h⟩))
      (Prod.Lex.lt_iff.2 (Or.inl hlt))
  · by_contra h
    exact hcov.2 (c := toLex ((ofLex (Order.succ s)).1, ⊥))
      (Prod.Lex.lt_iff.2 (Or.inl hlt))
      (Prod.Lex.lt_iff.2 (Or.inr ⟨rfl, bot_lt_iff_ne_bot.2 h⟩))
  · have : (ofLex s).1 ⋖ (ofLex (Order.succ s)).1 :=
      ⟨hlt, fun y h1 h2 => hcov.2 (c := toLex (y, ⊥))
        (Prod.Lex.lt_iff.2 (Or.inl h1)) (Prod.Lex.lt_iff.2 (Or.inl h2))⟩
    exact this.succ_eq.symm

/-- The relation of a cell of a stage to the pushout square of the stage. -/
lemma basicCell_ι_inr (s : Idx c) (q : Q s) :
    basicCell q.1.j q.1.i ≫ Sigma.ι (fun q : Q s => B q.1.j q.1.i) q ≫
      pushout.inr (attach s) (mcop s) =
    attachMap q.1 ≫ c.F.map (homOfLE (le_of_eq q.2.1)) ≫ pushout.inl (attach s) (mcop s) := by
  have h := basicCell_cellTo s q.1 (le_of_eq q.2.1) (fun _ => q.2.2)
  rw [cellTo_pos _ _ _ _ q.2.1] at h
  exact h

/-- A step attaching no cell is an isomorphism. -/
lemma isIso_stageMap_of_same {s s' : Idx c} (h : s ≤ s') (e : (ofLex s').1 = (ofLex s).1)
    (hQ : ∀ q : Q s', toPos c q.1 < (ofLex s).2) : IsIso (stageMap h) := by
  let inv : stage s' ⟶ stage s :=
    pushout.desc (c.F.map (homOfLE (le_of_eq e)) ≫ pushout.inl (attach s) (mcop s))
      (Sigma.desc fun q => Sigma.ι (fun q : Q s => B q.1.j q.1.i)
        ⟨q.1, q.2.1.trans e, hQ q⟩ ≫ pushout.inr (attach s) (mcop s)) (by
        apply Sigma.hom_ext
        intro q
        rw [ι_attach_assoc, ι_mcop_assoc, Sigma.ι_comp_desc,
          basicCell_ι_inr s ⟨q.1, q.2.1.trans e, hQ q⟩, ← Functor.map_comp_assoc]
        rfl)
  refine ⟨inv, ?_, ?_⟩
  · apply pushout.hom_ext
    · rw [inl_stageMap_assoc, pushout.inl_desc, ← Functor.map_comp_assoc, Category.comp_id]
      have h1 : c.F.map (homOfLE (le_fst h) ≫ homOfLE (le_of_eq e)) = 𝟙 _ := by
        rw [← c.F.map_id]; rfl
      rw [h1, Category.id_comp]
    · apply Sigma.hom_ext
      intro q
      rw [ι_inr_stageMap_assoc, cellTo_pos _ _ _ _ (q.2.1.trans e.symm), Category.assoc,
        pushout.inr_desc, Sigma.ι_comp_desc, Category.comp_id]
  · apply pushout.hom_ext
    · rw [pushout.inl_desc_assoc, Category.assoc, inl_stageMap, ← Functor.map_comp_assoc,
        Category.comp_id]
      have h1 : c.F.map (homOfLE (le_of_eq e) ≫ homOfLE (le_fst h)) = 𝟙 _ := by
        rw [← c.F.map_id]; rfl
      rw [h1, Category.id_comp]
    · apply Sigma.hom_ext
      intro q
      rw [pushout.inr_desc_assoc, Sigma.ι_comp_desc_assoc, Category.assoc, ι_inr_stageMap,
        cellTo_pos _ _ _ _ q.2.1, Category.comp_id]

section One

/-- The map out of the stage attaching one more cell. -/
noncomputable def oneDesc {s s' : Idx c} (e : (ofLex s').1 = (ofLex s).1)
    (γ₀ : c.Cells) (h₀ : γ₀.j = (ofLex s').1)
    (hQ : ∀ q : Q s', q.1 ≠ γ₀ → toPos c q.1 < (ofLex s).2)
    {T : C} (u : stage s ⟶ T) (v : B γ₀.j γ₀.i ⟶ T)
    (hw : (attachMap γ₀ ≫ c.F.map (homOfLE (le_of_eq (h₀.trans e))) ≫
      pushout.inl (attach s) (mcop s)) ≫ u = basicCell γ₀.j γ₀.i ≫ v) : stage s' ⟶ T := by
  classical
  exact pushout.desc
    (c.F.map (homOfLE (le_of_eq e)) ≫ pushout.inl (attach s) (mcop s) ≫ u)
    (Sigma.desc fun q => if hq : q.1 = γ₀ then eqToHom (by rw [hq]) ≫ v
      else Sigma.ι (fun q : Q s => B q.1.j q.1.i) ⟨q.1, q.2.1.trans e, hQ q hq⟩ ≫
        pushout.inr (attach s) (mcop s) ≫ u) (by
      apply Sigma.hom_ext
      intro q
      rw [ι_attach_assoc, ι_mcop_assoc, Sigma.ι_comp_desc]
      by_cases hq : q.1 = γ₀
      · obtain ⟨γ, hγ1, hγ2⟩ := q
        dsimp only at hq
        subst hq
        rw [dif_pos rfl, eqToHom_refl, Category.id_comp, ← hw]
        simp only [Category.assoc]
        rw [← Functor.map_comp_assoc]
        rfl
      · rw [dif_neg hq, reassoc_of% (basicCell_ι_inr s ⟨q.1, q.2.1.trans e, hQ q hq⟩),
          ← Functor.map_comp_assoc]
        rfl)

variable {s s' : Idx c} (h : s ≤ s') (e : (ofLex s').1 = (ofLex s).1)
    (γ₀ : c.Cells) (h₀ : γ₀.j = (ofLex s').1) (h₀' : toPos c γ₀ < (ofLex s').2)
    (h₀s : ¬ toPos c γ₀ < (ofLex s).2)
    (hQ : ∀ q : Q s', q.1 ≠ γ₀ → toPos c q.1 < (ofLex s).2)

variable {γ₀ h₀ hQ}

@[reassoc]
lemma inl_oneDesc {T : C} (u : stage s ⟶ T) (v : B γ₀.j γ₀.i ⟶ T) (hw) :
    pushout.inl (attach s') (mcop s') ≫ oneDesc e γ₀ h₀ hQ u v hw =
      c.F.map (homOfLE (le_of_eq e)) ≫ pushout.inl (attach s) (mcop s) ≫ u := by
  unfold oneDesc
  exact pushout.inl_desc _ _ _

@[reassoc]
lemma ι_inr_oneDesc_ne {T : C} (u : stage s ⟶ T) (v : B γ₀.j γ₀.i ⟶ T) (hw) (q : Q s')
    (hq : q.1 ≠ γ₀) :
    Sigma.ι (fun q : Q s' => B q.1.j q.1.i) q ≫ pushout.inr (attach s') (mcop s') ≫
      oneDesc e γ₀ h₀ hQ u v hw =
    Sigma.ι (fun q : Q s => B q.1.j q.1.i) ⟨q.1, q.2.1.trans e, hQ q hq⟩ ≫
      pushout.inr (attach s) (mcop s) ≫ u := by
  unfold oneDesc
  rw [pushout.inr_desc, Sigma.ι_comp_desc, dif_neg hq]

@[reassoc]
lemma ι_inr_oneDesc_eq {T : C} (u : stage s ⟶ T) (v : B γ₀.j γ₀.i ⟶ T) (hw) :
    Sigma.ι (fun q : Q s' => B q.1.j q.1.i) ⟨γ₀, h₀, h₀'⟩ ≫ pushout.inr (attach s') (mcop s') ≫
      oneDesc e γ₀ h₀ hQ u v hw = v := by
  unfold oneDesc
  rw [pushout.inr_desc, Sigma.ι_comp_desc, dif_pos rfl, eqToHom_refl, Category.id_comp]

include h₀s hQ in
/-- A step attaching one cell is a pushout of that cell. -/
lemma isPushout_stageMap_of_one :
    IsPushout (attachMap γ₀ ≫ c.F.map (homOfLE (le_of_eq (h₀.trans e))) ≫
        pushout.inl (attach s) (mcop s)) (basicCell γ₀.j γ₀.i) (stageMap h)
      (Sigma.ι (fun q : Q s' => B q.1.j q.1.i) ⟨γ₀, h₀, h₀'⟩ ≫
        pushout.inr (attach s') (mcop s')) := by
  have w : (attachMap γ₀ ≫ c.F.map (homOfLE (le_of_eq (h₀.trans e))) ≫
      pushout.inl (attach s) (mcop s)) ≫ stageMap h =
      basicCell γ₀.j γ₀.i ≫ Sigma.ι (fun q : Q s' => B q.1.j q.1.i) ⟨γ₀, h₀, h₀'⟩ ≫
        pushout.inr (attach s') (mcop s') := by
    rw [Category.assoc, Category.assoc, inl_stageMap, basicCell_ι_inr s' ⟨γ₀, h₀, h₀'⟩,
      ← Functor.map_comp_assoc]
    rfl
  have h1 : c.F.map (homOfLE (le_fst h) ≫ homOfLE (le_of_eq e)) = 𝟙 _ := by
    rw [← c.F.map_id]; rfl
  have h2 : c.F.map (homOfLE (le_of_eq e) ≫ homOfLE (le_fst h)) = 𝟙 _ := by
    rw [← c.F.map_id]; rfl
  refine IsPushout.of_isColimit (c := PushoutCocone.mk _ _ w)
    (PushoutCocone.IsColimit.mk _ (fun σ => oneDesc e γ₀ h₀ hQ σ.inl σ.inr σ.condition)
      ?_ ?_ ?_)
  · intro σ
    apply pushout.hom_ext
    · rw [inl_stageMap_assoc, inl_oneDesc, ← Functor.map_comp_assoc, h1, Category.id_comp]
    · apply Sigma.hom_ext
      intro q
      have hq : q.1 ≠ γ₀ := fun hq => h₀s (by rw [← hq]; exact q.2.2)
      have hc := ι_inr_stageMap h q
      rw [cellTo_pos s' q.1 _ _ (q.2.1.trans e.symm)] at hc
      rw [reassoc_of% hc, ι_inr_oneDesc_ne e _ _ _
        ⟨q.1, q.2.1.trans e.symm, lt_of_lt_of_le q.2.2 (snd_le_of_le h e.symm)⟩ hq]
  · intro σ
    exact (Category.assoc _ _ _).trans (ι_inr_oneDesc_eq e h₀' σ.inl σ.inr σ.condition)
  · intro σ m hm₁ hm₂
    apply pushout.hom_ext
    · have key : pushout.inl (attach s') (mcop s') = c.F.map (homOfLE (le_of_eq e)) ≫
          pushout.inl (attach s) (mcop s) ≫ stageMap h := by
        rw [inl_stageMap, ← Functor.map_comp_assoc, h2, Category.id_comp]
      rw [inl_oneDesc, key, Category.assoc, Category.assoc]
      exact congrArg (fun φ => c.F.map (homOfLE (le_of_eq e)) ≫ pushout.inl _ _ ≫ φ) hm₁
    · apply Sigma.hom_ext
      intro q
      by_cases hq : q.1 = γ₀
      · obtain ⟨γ, hγ1, hγ2⟩ := q
        dsimp only at hq
        subst hq
        rw [ι_inr_oneDesc_eq e hγ2, ← hm₂, Category.assoc]
      · rw [ι_inr_oneDesc_ne e _ _ _ q hq, ← hm₁]
        have hc := ι_inr_stageMap h ⟨q.1, q.2.1.trans e, hQ q hq⟩
        rw [cellTo_pos s' q.1 _ _ q.2.1] at hc
        rw [← reassoc_of% hc]

end One

end Steps

section Block

variable [NoMaxOrder J]

/-- The stage containing all cells of a step is the next step of the relative cell complex. -/
lemma isPushout_block (s : Idx c) (hall : ∀ γ : c.Cells, γ.j = (ofLex s).1 → toPos c γ < (ofLex s).2) :
    IsPushout (attach s) (mcop s) (c.F.map (homOfLE (Order.le_succ (ofLex s).1)))
      (Sigma.desc fun q : Q s => cellMap q.1 ≫
        c.F.map (homOfLE (Order.succ_le_succ (le_of_eq q.2.1)))) := by
  let j := (ofLex s).1
  have hj : ¬ IsMax j := not_isMax j
  let ac := c.attachCells j hj
  let qk : ac.ι → Q s := fun k => ⟨⟨j, hj, k⟩, rfl, hall _ rfl⟩
  have w : attach s ≫ c.F.map (homOfLE (Order.le_succ (ofLex s).1)) =
      mcop s ≫ Sigma.desc (fun q : Q s => cellMap q.1 ≫
        c.F.map (homOfLE (Order.succ_le_succ (le_of_eq q.2.1)))) := by
    apply Sigma.hom_ext
    intro q
    rw [ι_attach_assoc, ι_mcop_assoc, Sigma.ι_comp_desc, ← attachMap_w_assoc,
      ← Functor.map_comp, ← Functor.map_comp]
    rfl
  let ιA : ∀ k : ac.ι, A j (ac.π k) ⟶ ∐ (fun q : Q s => A q.1.j q.1.i) := fun k =>
    Sigma.ι (fun q : Q s => A q.1.j q.1.i) (qk k)
  let ιB : ∀ k : ac.ι, B j (ac.π k) ⟶ ∐ (fun q : Q s => B q.1.j q.1.i) := fun k =>
    Sigma.ι (fun q : Q s => B q.1.j q.1.i) (qk k)
  have hA : ∀ k, ιA k ≫ attach s = ac.cofan₁.inj k ≫ ac.g₁ := by
    intro k
    have h := ι_attach s (qk k)
    have h1 : c.F.map (homOfLE (le_of_eq (qk k).2.1)) = 𝟙 _ := by rw [← c.F.map_id]; rfl
    rw [h1, Category.comp_id] at h
    exact h
  have hm : ∀ k, ιA k ≫ mcop s = basicCell j (ac.π k) ≫ ιB k := fun k => ι_mcop s (qk k)
  have hB : ∀ k, ιB k ≫ (Sigma.desc fun q : Q s => cellMap q.1 ≫
      c.F.map (homOfLE (Order.succ_le_succ (le_of_eq q.2.1)))) = ac.cofan₂.inj k ≫ ac.g₂ := by
    intro k
    have h := Sigma.ι_comp_desc (fun q : Q s => cellMap q.1 ≫
      c.F.map (homOfLE (Order.succ_le_succ (le_of_eq q.2.1)))) (qk k)
    have h1 : c.F.map (homOfLE (Order.succ_le_succ (le_of_eq (qk k).2.1))) = 𝟙 _ := by
      rw [← c.F.map_id]; rfl
    rw [h1, Category.comp_id] at h
    exact h
  have hsurj : ∀ q : Q s, ∃ k, q = qk k := by
    intro q
    obtain ⟨⟨j₁, hj₁, k₁⟩, hq1, hq2⟩ := q
    dsimp only at hq1
    subst hq1
    exact ⟨k₁, rfl⟩
  refine IsPushout.of_isColimit (c := PushoutCocone.mk _ _ w)
    (PushoutCocone.IsColimit.mk _ (fun σ => ac.isPushout.desc σ.inl
      (Cofan.IsColimit.desc ac.isColimit₂ fun k => ιB k ≫ σ.inr) ?_) ?_ ?_ ?_)
  · apply Cofan.IsColimit.hom_ext ac.isColimit₁
    intro k
    have hσ := congrArg (fun φ => ιA k ≫ φ) σ.condition
    rw [reassoc_of% (hA k), reassoc_of% (hm k)] at hσ
    rw [reassoc_of% (ac.hm k), Cofan.IsColimit.fac]
    exact hσ
  · intro σ
    exact ac.isPushout.inl_desc _ _ _
  · intro σ
    apply Sigma.hom_ext
    intro q
    obtain ⟨k, rfl⟩ := hsurj q
    change ιB k ≫ _ = ιB k ≫ σ.inr
    rw [reassoc_of% (hB k), ac.isPushout.inr_desc, Cofan.IsColimit.fac]
  · intro σ m hm₁ hm₂
    apply ac.isPushout.hom_ext
    · rw [ac.isPushout.inl_desc]
      exact hm₁
    · rw [ac.isPushout.inr_desc]
      apply Cofan.IsColimit.hom_ext ac.isColimit₂
      intro k
      rw [Cofan.IsColimit.fac, ← hm₂, ← reassoc_of% (hB k)]

/-- The step from the end of a step of the complex to the beginning of the next one is an
isomorphism. -/
lemma isIso_stageMap_block {s s' : Idx c} (h : s ≤ s') (h1 : (ofLex s).2 = ⊤)
    (h2 : (ofLex s').2 = ⊥) (h3 : (ofLex s').1 = Order.succ (ofLex s).1) :
    IsIso (stageMap h) := by
  have hall : ∀ γ : c.Cells, γ.j = (ofLex s).1 → toPos c γ < (ofLex s).2 := fun γ _ => by
    rw [h1]; exact WithTop.coe_lt_top _
  have P := isPushout_block s hall
  haveI : IsEmpty (Q s') := ⟨fun q => not_lt_bot (lt_of_lt_of_le q.2.2 (le_of_eq h2))⟩
  haveI := isIso_inl_of_isEmpty s'
  let φ : c.F.obj (Order.succ (ofLex s).1) ⟶ c.F.obj (ofLex s').1 :=
    c.F.map (homOfLE (le_of_eq h3.symm))
  haveI : IsIso φ := ⟨⟨c.F.map (homOfLE (le_of_eq h3)), by
      rw [← c.F.map_comp, ← c.F.map_id]; rfl, by
      rw [← c.F.map_comp, ← c.F.map_id]; rfl⟩⟩
  have key : stageMap h = P.isoPushout.inv ≫ φ ≫ pushout.inl (attach s') (mcop s') := by
    apply pushout.hom_ext
    · rw [inl_stageMap, P.inl_isoPushout_inv_assoc, ← Functor.map_comp_assoc]
      rfl
    · apply Sigma.hom_ext
      intro q
      have hne : ¬ q.1.j = (ofLex s').1 := by
        rw [q.2.1, h3]; exact (Order.lt_succ (ofLex s).1).ne
      rw [ι_inr_stageMap, P.inr_isoPushout_inv_assoc, Sigma.ι_comp_desc_assoc,
        cellTo_neg _ _ _ _ hne, Category.assoc, ← Functor.map_comp_assoc]
      rfl
  rw [key]
  infer_instance

end Block

section Assembly

variable [NoMaxOrder J]

lemma toPos_injective : Function.Injective (toPos c) := by
  intro γ γ' h
  exact Option.some.inj (Option.some.inj h)

/-- Each successor step attaches a single cell or is an isomorphism. -/
lemma stageMap_mem (P : MorphismProperty C)
    (hP : ∀ j i, P (basicCell j i)) (s : Idx c) (hs : ¬ IsMax s) :
    (P.pushouts ⊔ MorphismProperty.isomorphisms C)
      (stageMap (Order.le_succ s)) := by
  classical
  by_cases e : (ofLex (Order.succ s)).1 = (ofLex s).1
  · by_cases hcell : ∃ γ : c.Cells, γ.j = (ofLex s).1 ∧ toPos c γ = (ofLex s).2
    · obtain ⟨γ, hγ, hp⟩ := hcell
      have h₀ : γ.j = (ofLex (Order.succ s)).1 := hγ.trans e.symm
      have h₀' : toPos c γ < (ofLex (Order.succ s)).2 :=
        (same_block_iff hs e γ).2 hp.le
      have h₀s : ¬ toPos c γ < (ofLex s).2 := by rw [hp]; exact lt_irrefl _
      have hQ : ∀ q : Q (Order.succ s), q.1 ≠ γ → toPos c q.1 < (ofLex s).2 := by
        intro q hq
        apply lt_of_le_of_ne ((same_block_iff hs e q.1).1 q.2.2)
        intro he
        exact hq (toPos_injective (he.trans hp.symm))
      exact Or.inl (P.pushouts_mk
        (isPushout_stageMap_of_one (Order.le_succ s) e (h₀ := h₀) (hQ := hQ) h₀' h₀s) (hP γ.j γ.i))
    · apply Or.inr
      apply isIso_stageMap_of_same (Order.le_succ s) e
      intro q
      apply lt_of_le_of_ne ((same_block_iff hs e q.1).1 q.2.2)
      intro he
      exact hcell ⟨q.1, q.2.1.trans e, he⟩
  · obtain ⟨h1, h2, h3⟩ := block_change hs e
    exact Or.inr (isIso_stageMap_block (Order.le_succ s) h1 h2 h3)

/-- A cellular presentation indexed by a well-order without limit elements can be refined
into a presentation attaching at most one cell at each successor step. -/
noncomputable def transfiniteComposition (hJ : ∀ j : J, ¬ Order.IsSuccLimit j)
    (P : MorphismProperty C) (hP : ∀ j i, P (basicCell j i)) :
    (P.pushouts ⊔ MorphismProperty.isomorphisms C).TransfiniteCompositionOfShape (Idx c) f where
  F := functor
  isoBot := by
    haveI := isIso_inl_of_isEmpty (c := c) (⊥ : Idx c)
    exact (asIso (pushout.inl (attach (⊥ : Idx c)) (mcop (⊥ : Idx c)))).symm ≪≫ c.isoBot
  isWellOrderContinuous := ⟨fun s hs => ⟨isColimitAt s hs hJ⟩⟩
  incl := (cocone (c := c)).ι
  isColimit := isColimitCocone
  fac := by
    change (c.isoBot.inv ≫ pushout.inl (attach (⊥ : Idx c)) (mcop (⊥ : Idx c))) ≫
      leg (⊥ : Idx c) = f
    erw [Category.assoc, inl_leg, c.fac]
  map_mem := stageMap_mem P hP

end Assembly

end HomotopyHypothesis.FiniteCategory.UnitPresentation.Flatten
