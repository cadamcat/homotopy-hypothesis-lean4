import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Category.SemiModelStructure.Filtered
import HomotopyHypothesis.Category.SemiModelStructure.Flat
import HomotopyHypothesis.Category.SemiModelStructure.SingleCell
import HomotopyHypothesis.Category.SemiModelStructure.YonedaFacts
import HomotopyHypothesis.Category.SemiModelConstruction.Colimits
import HomotopyHypothesis.Category.SemiModelConstruction.YonedaLifting
/-!
# Attaching a family of cells to a flat object

Attaching any family of cells `y c` (cofibrations `c` of `C`) to a flat object of the completion
gives a flat object; when the cells are trivial cofibrations the inclusion is a weak equivalence. The
pushout of a coproduct of cells is the filtered colimit, over finite sets of cells, of the pushouts
of the finite coproducts, which are single cells.
-/

universe w v u t

open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace HomotopyHypothesis.Category.SemiModelStructure

open Henry Category.SemiModelConstruction

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [IsCylinderCategory C] [EssentiallySmall.{w} C]

private structure RepresentedCell {α : Type t} {A B : α → Completion.{w} C}
    (g : ∀ a, A a ⟶ B a) (P : Prop) (a : α) where
  src : C
  tgt : C
  cell : src ⟶ tgt
  isCofibration : cofibrations C cell
  isWeakEquivalence : P → weakEquivalences C cell
  arrowIso : Nonempty (Arrow.mk (g a) ≅ Arrow.mk (completionSmallYoneda.{w}.map cell))

private structure FiniteCellCoproductData {I : Type w} (A B : I → C)
    (g : ∀ i, A i ⟶ B i) (S : Finset I) where
  src : C
  tgt : C
  cell : src ⟶ tgt
  ιSrc : ∀ i : {i // i ∈ S}, A i.val ⟶ src
  ιTgt : ∀ i : {i // i ∈ S}, B i.val ⟶ tgt
  isColimitSrc : IsColimit (Cofan.mk src ιSrc)
  isColimitTgt : IsColimit (Cofan.mk tgt ιTgt)
  cellCondition : ∀ i, ιSrc i ≫ cell = g i.val ≫ ιTgt i
  isCofibration : cofibrations C cell
  isWeakEquivalence : (∀ i : {i // i ∈ S}, weakEquivalences C (g i.val)) →
    weakEquivalences C cell

private noncomputable def finiteCellCoproductData {I : Type w} (A B : I → C) (g : ∀ i, A i ⟶ B i)
    (hg : ∀ i, cofibrations C (g i)) (S : Finset I) : FiniteCellCoproductData A B g S := by
  classical
  letI : Finite {i // i ∈ S} := Finite.of_fintype _
  have hData : Nonempty (FiniteCellCoproductData A B g S) := by
    obtain ⟨src, tgt, cell, ιSrc, ιTgt, hSrc, hTgt, hCell, hCof, hWeak⟩ :=
      exists_coproduct_cell (fun i : {i // i ∈ S} => g i.val) (fun i => hg i.val)
    exact ⟨⟨src, tgt, cell, ιSrc, ιTgt, hSrc.some, hTgt.some, hCell, hCof, hWeak⟩⟩
  exact Classical.choice hData

set_option maxHeartbeats 1000000000000
attribute [local instance] Category.SemiModelConstruction.completion_hasColimits

/-- Attaching cells isomorphic to `y c` (`c` a cofibration of `C`, a weak equivalence when `P`
holds) to a flat object gives a flat object, and a weak equivalence when `P` holds. -/
theorem attachCells_flat {α : Type t} {A B : α → Completion.{w} C} (g : ∀ a, A a ⟶ B a)
    (P : Prop)
    (hg : ∀ a, ∃ (Cc Dd : C) (c : Cc ⟶ Dd), cofibrations C c ∧ (P → weakEquivalences C c) ∧
      Nonempty (Arrow.mk (g a) ≅ Arrow.mk (completionSmallYoneda.{w}.map c)))
    {X₁ X₂ : Completion.{w} C} {f : X₁ ⟶ X₂} (cells : AttachCells.{w} g f) (hX : IsFlat X₁) :
    IsFlat X₂ ∧ (P → Completion.weakEquivalences C f) := by
  classical
  let chosen : ∀ i : cells.ι, RepresentedCell g P (cells.π i) := fun i =>
    Classical.choice (by
      rcases hg (cells.π i) with ⟨Cc, Dd, c, hc, hw, hiso⟩
      exact ⟨⟨Cc, Dd, c, hc, hw, hiso⟩⟩)
  let src : cells.ι → C := fun i => (chosen i).src
  let tgt : cells.ι → C := fun i => (chosen i).tgt
  let c : ∀ i, src i ⟶ tgt i := fun i => (chosen i).cell
  let hc : ∀ i, cofibrations C (c i) := fun i => (chosen i).isCofibration
  let data (S : Finset cells.ι) := finiteCellCoproductData src tgt c hc S
  let eA (i : cells.ι) : A (cells.π i) ≅ completionSmallYoneda.{w}.obj (src i) :=
    Arrow.leftFunc.mapIso (Classical.choice (chosen i).arrowIso)
  let eB (i : cells.ι) : B (cells.π i) ≅ completionSmallYoneda.{w}.obj (tgt i) :=
    Arrow.rightFunc.mapIso (Classical.choice (chosen i).arrowIso)
  let hsrcY (S : Finset cells.ι) :
      IsColimit (Cofan.mk (completionSmallYoneda.{w}.obj (data S).src)
        (fun i => completionSmallYoneda.{w}.map ((data S).ιSrc i))) :=
    Classical.choice (completionSmallYoneda_isColimit_cofan ((data S).isColimitSrc))
  let htgtY (S : Finset cells.ι) :
      IsColimit (Cofan.mk (completionSmallYoneda.{w}.obj (data S).tgt)
        (fun i => completionSmallYoneda.{w}.map ((data S).ιTgt i))) :=
    Classical.choice (completionSmallYoneda_isColimit_cofan ((data S).isColimitTgt))
  let a (S : Finset cells.ι) : completionSmallYoneda.{w}.obj (data S).src ⟶ X₁ :=
    Cofan.IsColimit.desc (hsrcY S) (fun i =>
      (eA i.val).inv ≫ cells.cofan₁.inj i.val ≫ cells.g₁)
  let b (S : Finset cells.ι) : completionSmallYoneda.{w}.obj (data S).tgt ⟶ X₂ :=
    Cofan.IsColimit.desc (htgtY S) (fun i =>
      (eB i.val).inv ≫ cells.cofan₂.inj i.val ≫ cells.g₂)
  have haFac (S : Finset cells.ι) (i : {i // i ∈ S}) :
      completionSmallYoneda.{w}.map ((data S).ιSrc i) ≫ a S =
        (eA i.val).inv ≫ cells.cofan₁.inj i.val ≫ cells.g₁ := by
    simpa [a] using Cofan.IsColimit.fac (hsrcY S)
      (fun j => (eA j.val).inv ≫ cells.cofan₁.inj j.val ≫ cells.g₁) i
  have hbFac (S : Finset cells.ι) (i : {i // i ∈ S}) :
      completionSmallYoneda.{w}.map ((data S).ιTgt i) ≫ b S =
        (eB i.val).inv ≫ cells.cofan₂.inj i.val ≫ cells.g₂ := by
    simpa [b] using Cofan.IsColimit.fac (htgtY S)
      (fun j => (eB j.val).inv ≫ cells.cofan₂.inj j.val ≫ cells.g₂) i
  have hCellStage (S : Finset cells.ι) (i : {i // i ∈ S}) :
      completionSmallYoneda.{w}.map ((data S).ιSrc i) ≫
          completionSmallYoneda.{w}.map (data S).cell ≫ b S =
        completionSmallYoneda.{w}.map (c i.val) ≫ (eB i.val).inv ≫
          cells.cofan₂.inj i.val ≫ cells.g₂ := by
    calc
      completionSmallYoneda.{w}.map ((data S).ιSrc i) ≫
          completionSmallYoneda.{w}.map (data S).cell ≫ b S =
          (completionSmallYoneda.{w}.map ((data S).ιSrc i) ≫
            completionSmallYoneda.{w}.map (data S).cell) ≫ b S :=
              (Category.assoc _ _ _).symm
      _ = completionSmallYoneda.{w}.map ((data S).ιSrc i ≫ (data S).cell) ≫ b S :=
          congrArg (fun q => q ≫ b S)
            ((completionSmallYoneda.{w}).map_comp ((data S).ιSrc i) (data S).cell).symm
      _ = completionSmallYoneda.{w}.map (c i.val ≫ (data S).ιTgt i) ≫ b S := by
          rw [(data S).cellCondition]
      _ = (completionSmallYoneda.{w}.map (c i.val) ≫
          completionSmallYoneda.{w}.map ((data S).ιTgt i)) ≫ b S :=
            congrArg (fun q => q ≫ b S)
              ((completionSmallYoneda.{w}).map_comp (c i.val) ((data S).ιTgt i))
      _ = completionSmallYoneda.{w}.map (c i.val) ≫
          completionSmallYoneda.{w}.map ((data S).ιTgt i) ≫ b S :=
            Category.assoc _ _ _
      _ = completionSmallYoneda.{w}.map (c i.val) ≫
          ((eB i.val).inv ≫ cells.cofan₂.inj i.val ≫ cells.g₂) :=
            congrArg (fun q => completionSmallYoneda.{w}.map (c i.val) ≫ q) (hbFac S i)
  have hArrow (i : cells.ι) : (eA i).hom ≫ completionSmallYoneda.{w}.map (c i) =
      g (cells.π i) ≫ (eB i).hom := by
    have hh := (Classical.choice (chosen i).arrowIso).hom.w
    change (eA i).hom ≫ completionSmallYoneda.{w}.map (c i) =
      g (cells.π i) ≫ (eB i).hom at hh
    exact hh
  have hCellIso (i : cells.ι) : (eA i).inv ≫ g (cells.π i) =
      completionSmallYoneda.{w}.map (c i) ≫ (eB i).inv := by
    calc
      (eA i).inv ≫ g (cells.π i) =
          (eA i).inv ≫ (g (cells.π i) ≫ (eB i).hom) ≫ (eB i).inv := by simp
      _ = (eA i).inv ≫ ((eA i).hom ≫ completionSmallYoneda.{w}.map (c i)) ≫ (eB i).inv :=
          by rw [hArrow i]
      _ = completionSmallYoneda.{w}.map (c i) ≫ (eB i).inv := by
          simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hLeftStage (S : Finset cells.ι) (i : {i // i ∈ S}) :
      (completionSmallYoneda.{w}.map ((data S).ιSrc i) ≫ a S) ≫ f =
        completionSmallYoneda.{w}.map (c i.val) ≫
          (eB i.val).inv ≫ cells.cofan₂.inj i.val ≫ cells.g₂ := by
    calc
      (completionSmallYoneda.{w}.map ((data S).ιSrc i) ≫ a S) ≫ f =
          ((eA i.val).inv ≫ cells.cofan₁.inj i.val ≫ cells.g₁) ≫ f :=
            congrArg (fun q => q ≫ f) (haFac S i)
      _ = (eA i.val).inv ≫ cells.cofan₁.inj i.val ≫ (cells.g₁ ≫ f) := by
          simp [Category.assoc]
      _ = (eA i.val).inv ≫ cells.cofan₁.inj i.val ≫ (cells.m ≫ cells.g₂) := by
          rw [cells.isPushout.w]
      _ = (eA i.val).inv ≫ (cells.cofan₁.inj i.val ≫ cells.m) ≫ cells.g₂ := by
          simp [Category.assoc]
      _ = (eA i.val).inv ≫ (g (cells.π i.val) ≫ cells.cofan₂.inj i.val) ≫ cells.g₂ := by
          rw [cells.hm]
      _ = ((eA i.val).inv ≫ g (cells.π i.val)) ≫ cells.cofan₂.inj i.val ≫ cells.g₂ := by
          simp [Category.assoc]
      _ = (completionSmallYoneda.{w}.map (c i.val) ≫ (eB i.val).inv) ≫
          cells.cofan₂.inj i.val ≫ cells.g₂ :=
            congrArg (fun q => q ≫ cells.cofan₂.inj i.val ≫ cells.g₂) (hCellIso i.val)
      _ = completionSmallYoneda.{w}.map (c i.val) ≫
          (eB i.val).inv ≫ cells.cofan₂.inj i.val ≫ cells.g₂ := by
            simp [Category.assoc]
  let obj (S : Finset cells.ι) : Completion.{w} C :=
    pushout (a S) (completionSmallYoneda.{w}.map (data S).cell)
  let stageLeg (S : Finset cells.ι) : obj S ⟶ X₂ :=
    pushout.desc f (b S) (by
      apply Cofan.IsColimit.hom_ext (hsrcY S)
      intro i
      change (completionSmallYoneda.{w}.map ((data S).ιSrc i) ≫ a S) ≫ f =
        completionSmallYoneda.{w}.map ((data S).ιSrc i) ≫
          completionSmallYoneda.{w}.map (data S).cell ≫ b S
      exact (hLeftStage S i).trans (hCellStage S i).symm)
  have hObjFlat (S : Finset cells.ι) : IsFlat (obj S) := by
    change IsFlat (pushout (a S) (completionSmallYoneda.{w}.map (data S).cell))
    exact (singleCell (X := X₁) hX (data S).cell
      (data S).isCofibration (a S) (pushout.inl _ _) (pushout.inr _ _)
      (IsPushout.of_hasPushout _ _)).1
  have hObjWeak (S : Finset cells.ι) :
      P → Completion.weakEquivalences C (pushout.inl (a S)
        (completionSmallYoneda.{w}.map (data S).cell)) := by
    intro hP
    exact (singleCell (X := X₁) hX (data S).cell
      (data S).isCofibration (a S) (pushout.inl _ _) (pushout.inr _ _)
      (IsPushout.of_hasPushout _ _)).2 ((data S).isWeakEquivalence (fun i =>
        (chosen i.val).isWeakEquivalence hP))

  let incSrc {S T : Finset cells.ι} (h : S ⊆ T) : (data S).src ⟶ (data T).src :=
    Cofan.IsColimit.desc (data S).isColimitSrc
      (fun i => (data T).ιSrc ⟨i.val, h i.property⟩)
  let incTgt {S T : Finset cells.ι} (h : S ⊆ T) : (data S).tgt ⟶ (data T).tgt :=
    Cofan.IsColimit.desc (data S).isColimitTgt
      (fun i => (data T).ιTgt ⟨i.val, h i.property⟩)
  have incSrcFac {S T : Finset cells.ι} (h : S ⊆ T) (i : {i // i ∈ S}) :
      (data S).ιSrc i ≫ incSrc h = (data T).ιSrc ⟨i.val, h i.property⟩ := by
    simpa [incSrc] using Cofan.IsColimit.fac (data S).isColimitSrc
      (fun j => (data T).ιSrc ⟨j.val, h j.property⟩) i
  have incTgtFac {S T : Finset cells.ι} (h : S ⊆ T) (i : {i // i ∈ S}) :
      (data S).ιTgt i ≫ incTgt h = (data T).ιTgt ⟨i.val, h i.property⟩ := by
    simpa [incTgt] using Cofan.IsColimit.fac (data S).isColimitTgt
      (fun j => (data T).ιTgt ⟨j.val, h j.property⟩) i
  have incSrcId (S : Finset cells.ι) :
      incSrc (fun i hi => hi) = 𝟙 ((data S).src) := by
    apply Cofan.IsColimit.hom_ext (data S).isColimitSrc
    intro i
    simpa [incSrc] using Cofan.IsColimit.fac (data S).isColimitSrc
      (fun j => (data S).ιSrc ⟨j.val, j.property⟩) i
  have incTgtId (S : Finset cells.ι) :
      incTgt (fun i hi => hi) = 𝟙 ((data S).tgt) := by
    apply Cofan.IsColimit.hom_ext (data S).isColimitTgt
    intro i
    simpa [incTgt] using Cofan.IsColimit.fac (data S).isColimitTgt
      (fun j => (data S).ιTgt ⟨j.val, j.property⟩) i
  have incSrcComp {S T U : Finset cells.ι} (hST : S ⊆ T) (hTU : T ⊆ U) :
      incSrc hST ≫ incSrc hTU = incSrc (hST.trans hTU) := by
    apply Cofan.IsColimit.hom_ext (data S).isColimitSrc
    intro i
    calc
      (data S).ιSrc i ≫ incSrc hST ≫ incSrc hTU =
          ((data S).ιSrc i ≫ incSrc hST) ≫ incSrc hTU := (Category.assoc _ _ _).symm
      _ = (data T).ιSrc ⟨i.val, hST i.property⟩ ≫ incSrc hTU :=
          congrArg (fun q => q ≫ incSrc hTU) (incSrcFac hST i)
      _ = (data U).ιSrc ⟨i.val, hTU (hST i.property)⟩ :=
          incSrcFac hTU ⟨i.val, hST i.property⟩
      _ = (data S).ιSrc i ≫ incSrc (hST.trans hTU) :=
          (incSrcFac (hST.trans hTU) i).symm
  have incTgtComp {S T U : Finset cells.ι} (hST : S ⊆ T) (hTU : T ⊆ U) :
      incTgt hST ≫ incTgt hTU = incTgt (hST.trans hTU) := by
    apply Cofan.IsColimit.hom_ext (data S).isColimitTgt
    intro i
    calc
      (data S).ιTgt i ≫ incTgt hST ≫ incTgt hTU =
          ((data S).ιTgt i ≫ incTgt hST) ≫ incTgt hTU := (Category.assoc _ _ _).symm
      _ = (data T).ιTgt ⟨i.val, hST i.property⟩ ≫ incTgt hTU :=
          congrArg (fun q => q ≫ incTgt hTU) (incTgtFac hST i)
      _ = (data U).ιTgt ⟨i.val, hTU (hST i.property)⟩ :=
          incTgtFac hTU ⟨i.val, hST i.property⟩
      _ = (data S).ιTgt i ≫ incTgt (hST.trans hTU) :=
          (incTgtFac (hST.trans hTU) i).symm
  have hCellInc {S T : Finset cells.ι} (h : S ⊆ T) :
      (data S).cell ≫ incTgt h = incSrc h ≫ (data T).cell := by
    apply Cofan.IsColimit.hom_ext (data S).isColimitSrc
    intro i
    calc
      (data S).ιSrc i ≫ (data S).cell ≫ incTgt h =
          ((data S).ιSrc i ≫ (data S).cell) ≫ incTgt h := (Category.assoc _ _ _).symm
      _ = (c i.val ≫ (data S).ιTgt i) ≫ incTgt h :=
          congrArg (fun q => q ≫ incTgt h) ((data S).cellCondition i)
      _ = c i.val ≫ (data T).ιTgt ⟨i.val, h i.property⟩ := by
          rw [Category.assoc, incTgtFac h i]
      _ = (data T).ιSrc ⟨i.val, h i.property⟩ ≫ (data T).cell :=
          ((data T).cellCondition ⟨i.val, h i.property⟩).symm
      _ = ((data S).ιSrc i ≫ incSrc h) ≫ (data T).cell := by
          rw [← incSrcFac h i]
      _ = (data S).ιSrc i ≫ incSrc h ≫ (data T).cell := Category.assoc _ _ _
  have haInc {S T : Finset cells.ι} (h : S ⊆ T) :
      completionSmallYoneda.{w}.map (incSrc h) ≫ a T = a S := by
    apply Cofan.IsColimit.hom_ext (hsrcY S)
    intro i
    calc
      completionSmallYoneda.{w}.map ((data S).ιSrc i) ≫
          completionSmallYoneda.{w}.map (incSrc h) ≫ a T =
          (completionSmallYoneda.{w}.map ((data S).ιSrc i) ≫
            completionSmallYoneda.{w}.map (incSrc h)) ≫ a T := (Category.assoc _ _ _).symm
      _ = completionSmallYoneda.{w}.map ((data S).ιSrc i ≫ incSrc h) ≫ a T :=
          congrArg (fun q => q ≫ a T)
            ((completionSmallYoneda.{w}).map_comp ((data S).ιSrc i) (incSrc h)).symm
      _ = completionSmallYoneda.{w}.map ((data T).ιSrc ⟨i.val, h i.property⟩) ≫ a T := by
          rw [incSrcFac h i]
      _ = (eA i.val).inv ≫ cells.cofan₁.inj i.val ≫ cells.g₁ := haFac T ⟨i.val, h i.property⟩
      _ = completionSmallYoneda.{w}.map ((data S).ιSrc i) ≫ a S := (haFac S i).symm
  have hbInc {S T : Finset cells.ι} (h : S ⊆ T) :
      completionSmallYoneda.{w}.map (incTgt h) ≫ b T = b S := by
    apply Cofan.IsColimit.hom_ext (htgtY S)
    intro i
    calc
      completionSmallYoneda.{w}.map ((data S).ιTgt i) ≫
          completionSmallYoneda.{w}.map (incTgt h) ≫ b T =
          (completionSmallYoneda.{w}.map ((data S).ιTgt i) ≫
            completionSmallYoneda.{w}.map (incTgt h)) ≫ b T := (Category.assoc _ _ _).symm
      _ = completionSmallYoneda.{w}.map ((data S).ιTgt i ≫ incTgt h) ≫ b T :=
          congrArg (fun q => q ≫ b T)
            ((completionSmallYoneda.{w}).map_comp ((data S).ιTgt i) (incTgt h)).symm
      _ = completionSmallYoneda.{w}.map ((data T).ιTgt ⟨i.val, h i.property⟩) ≫ b T := by
          rw [incTgtFac h i]
      _ = (eB i.val).inv ≫ cells.cofan₂.inj i.val ≫ cells.g₂ := hbFac T ⟨i.val, h i.property⟩
      _ = completionSmallYoneda.{w}.map ((data S).ιTgt i) ≫ b S := (hbFac S i).symm
  have hStageCond {S T : Finset cells.ι} (h : S ⊆ T) :
      a S ≫ pushout.inl (a T) (completionSmallYoneda.{w}.map (data T).cell) =
        completionSmallYoneda.{w}.map (data S).cell ≫
          completionSmallYoneda.{w}.map (incTgt h) ≫
            pushout.inr (a T) (completionSmallYoneda.{w}.map (data T).cell) := by
    calc
      a S ≫ pushout.inl (a T) (completionSmallYoneda.{w}.map (data T).cell) =
          (completionSmallYoneda.{w}.map (incSrc h) ≫ a T) ≫
            pushout.inl (a T) (completionSmallYoneda.{w}.map (data T).cell) :=
              congrArg (fun q => q ≫ pushout.inl _ _) (haInc h).symm
      _ = completionSmallYoneda.{w}.map (incSrc h) ≫
          (a T ≫ pushout.inl (a T) (completionSmallYoneda.{w}.map (data T).cell)) :=
            Category.assoc _ _ _
      _ = completionSmallYoneda.{w}.map (incSrc h) ≫
          (completionSmallYoneda.{w}.map (data T).cell ≫
            pushout.inr (a T) (completionSmallYoneda.{w}.map (data T).cell)) := by
              rw [pushout.condition]
      _ = (completionSmallYoneda.{w}.map (incSrc h) ≫
          completionSmallYoneda.{w}.map (data T).cell) ≫
            pushout.inr (a T) (completionSmallYoneda.{w}.map (data T).cell) :=
              (Category.assoc _ _ _).symm
      _ = completionSmallYoneda.{w}.map (incSrc h ≫ (data T).cell) ≫
          pushout.inr (a T) (completionSmallYoneda.{w}.map (data T).cell) :=
            congrArg (fun q => q ≫ pushout.inr _ _)
              ((completionSmallYoneda.{w}).map_comp (incSrc h) (data T).cell).symm
      _ = completionSmallYoneda.{w}.map ((data S).cell ≫ incTgt h) ≫
          pushout.inr (a T) (completionSmallYoneda.{w}.map (data T).cell) := by
            rw [← hCellInc h]
      _ = (completionSmallYoneda.{w}.map (data S).cell ≫
          completionSmallYoneda.{w}.map (incTgt h)) ≫
            pushout.inr (a T) (completionSmallYoneda.{w}.map (data T).cell) :=
              congrArg (fun q => q ≫ pushout.inr _ _)
                ((completionSmallYoneda.{w}).map_comp (data S).cell (incTgt h))
      _ = completionSmallYoneda.{w}.map (data S).cell ≫
          completionSmallYoneda.{w}.map (incTgt h) ≫
            pushout.inr (a T) (completionSmallYoneda.{w}.map (data T).cell) :=
              Category.assoc _ _ _
  let stageMap {S T : Finset cells.ι} (h : S ⊆ T) : obj S ⟶ obj T :=
    pushout.desc (pushout.inl (a T) (completionSmallYoneda.{w}.map (data T).cell))
      (completionSmallYoneda.{w}.map (incTgt h) ≫
        pushout.inr (a T) (completionSmallYoneda.{w}.map (data T).cell)) (hStageCond h)
  have stageMapInl {S T : Finset cells.ι} (h : S ⊆ T) :
      pushout.inl (a S) (completionSmallYoneda.{w}.map (data S).cell) ≫ stageMap h =
        pushout.inl (a T) (completionSmallYoneda.{w}.map (data T).cell) := by
    dsimp [stageMap]
    rw [pushout.inl_desc]
  have stageMapInr {S T : Finset cells.ι} (h : S ⊆ T) :
      pushout.inr (a S) (completionSmallYoneda.{w}.map (data S).cell) ≫ stageMap h =
        completionSmallYoneda.{w}.map (incTgt h) ≫
          pushout.inr (a T) (completionSmallYoneda.{w}.map (data T).cell) := by
    dsimp [stageMap]
    rw [pushout.inr_desc]
  have stageMapId (S : Finset cells.ι) :
      stageMap (fun i hi => hi) = 𝟙 (obj S) := by
    apply pushout.hom_ext
    · rw [stageMapInl (S := S) (T := S) (fun i hi => hi)]
      exact (Category.comp_id _).symm
    · rw [stageMapInr (S := S) (T := S) (fun i hi => hi), incTgtId S]
      rw [completionSmallYoneda.map_id]
      exact (Category.comp_id _).symm
  have stageMapComp {S T U : Finset cells.ι} (hST : S ⊆ T) (hTU : T ⊆ U) :
      stageMap hST ≫ stageMap hTU = stageMap (hST.trans hTU) := by
    apply pushout.hom_ext
    · calc
        pushout.inl (a S) (completionSmallYoneda.{w}.map (data S).cell) ≫
            stageMap hST ≫ stageMap hTU =
            (pushout.inl (a S) (completionSmallYoneda.{w}.map (data S).cell) ≫ stageMap hST) ≫
              stageMap hTU := (Category.assoc _ _ _).symm
        _ = pushout.inl (a T) (completionSmallYoneda.{w}.map (data T).cell) ≫ stageMap hTU :=
            congrArg (fun q => q ≫ stageMap hTU) (stageMapInl hST)
        _ = pushout.inl (a U) (completionSmallYoneda.{w}.map (data U).cell) := stageMapInl hTU
        _ = pushout.inl (a S) (completionSmallYoneda.{w}.map (data S).cell) ≫
            stageMap (hST.trans hTU) := (stageMapInl (hST.trans hTU)).symm
    · calc
        pushout.inr (a S) (completionSmallYoneda.{w}.map (data S).cell) ≫
            stageMap hST ≫ stageMap hTU =
            (pushout.inr (a S) (completionSmallYoneda.{w}.map (data S).cell) ≫ stageMap hST) ≫
              stageMap hTU := (Category.assoc _ _ _).symm
        _ = (completionSmallYoneda.{w}.map (incTgt hST) ≫
            pushout.inr (a T) (completionSmallYoneda.{w}.map (data T).cell)) ≫ stageMap hTU :=
              congrArg (fun q => q ≫ stageMap hTU) (stageMapInr hST)
        _ = completionSmallYoneda.{w}.map (incTgt hST) ≫
            (pushout.inr (a T) (completionSmallYoneda.{w}.map (data T).cell) ≫ stageMap hTU) :=
              Category.assoc _ _ _
        _ = completionSmallYoneda.{w}.map (incTgt hST) ≫
            (completionSmallYoneda.{w}.map (incTgt hTU) ≫
              pushout.inr (a U) (completionSmallYoneda.{w}.map (data U).cell)) :=
                congrArg (fun q => completionSmallYoneda.{w}.map (incTgt hST) ≫ q)
                  (stageMapInr hTU)
        _ = (completionSmallYoneda.{w}.map (incTgt hST) ≫
            completionSmallYoneda.{w}.map (incTgt hTU)) ≫
              pushout.inr (a U) (completionSmallYoneda.{w}.map (data U).cell) :=
                (Category.assoc _ _ _).symm
        _ = completionSmallYoneda.{w}.map (incTgt hST ≫ incTgt hTU) ≫
            pushout.inr (a U) (completionSmallYoneda.{w}.map (data U).cell) :=
              congrArg (fun q => q ≫ pushout.inr _ _)
                ((completionSmallYoneda.{w}).map_comp (incTgt hST) (incTgt hTU)).symm
        _ = completionSmallYoneda.{w}.map (incTgt (hST.trans hTU)) ≫
            pushout.inr (a U) (completionSmallYoneda.{w}.map (data U).cell) :=
              congrArg (fun q => completionSmallYoneda.{w}.map q ≫ pushout.inr _ _) (incTgtComp hST hTU)
        _ = pushout.inr (a S) (completionSmallYoneda.{w}.map (data S).cell) ≫
            stageMap (hST.trans hTU) := (stageMapInr (hST.trans hTU)).symm
  let F : Finset cells.ι ⥤ Completion.{w} C := {
    obj := obj
    map := fun {S T} h => stageMap (leOfHom h)
    map_id := fun S => by simpa using stageMapId S
    map_comp := fun {S T U} hST hTU => by
      simpa using (stageMapComp (leOfHom hST) (leOfHom hTU)).symm
  }
  letI : IsFiltered (Finset cells.ι) := inferInstance
  let K : Cocone F := {
    pt := X₂
    ι := {
      app := stageLeg
      naturality := by
        intro S T h
        change stageMap (leOfHom h) ≫ stageLeg T = stageLeg S
        apply pushout.hom_ext
        · calc
            pushout.inl (a S) (completionSmallYoneda.{w}.map (data S).cell) ≫
                (stageMap (leOfHom h) ≫ stageLeg T) =
                (pushout.inl (a S) (completionSmallYoneda.{w}.map (data S).cell) ≫
                  stageMap (leOfHom h)) ≫ stageLeg T := (Category.assoc _ _ _).symm
            _ = pushout.inl (a T) (completionSmallYoneda.{w}.map (data T).cell) ≫ stageLeg T :=
                congrArg (fun q => q ≫ stageLeg T) (stageMapInl (leOfHom h))
            _ = f := by
                  dsimp [stageLeg]
                  rw [pushout.inl_desc]
            _ = pushout.inl (a S) (completionSmallYoneda.{w}.map (data S).cell) ≫ stageLeg S :=
                by
                  symm
                  dsimp [stageLeg]
                  rw [pushout.inl_desc]
        · calc
            pushout.inr (a S) (completionSmallYoneda.{w}.map (data S).cell) ≫
                (stageMap (leOfHom h) ≫ stageLeg T) =
                (pushout.inr (a S) (completionSmallYoneda.{w}.map (data S).cell) ≫
                  stageMap (leOfHom h)) ≫ stageLeg T := (Category.assoc _ _ _).symm
            _ = (completionSmallYoneda.{w}.map (incTgt (leOfHom h)) ≫
                pushout.inr (a T) (completionSmallYoneda.{w}.map (data T).cell)) ≫ stageLeg T :=
                  congrArg (fun q => q ≫ stageLeg T) (stageMapInr (leOfHom h))
            _ = completionSmallYoneda.{w}.map (incTgt (leOfHom h)) ≫
                (pushout.inr (a T) (completionSmallYoneda.{w}.map (data T).cell) ≫ stageLeg T) :=
                  Category.assoc _ _ _
            _ = completionSmallYoneda.{w}.map (incTgt (leOfHom h)) ≫ b T := by
                  have hDesc : pushout.inr (a T) (completionSmallYoneda.{w}.map (data T).cell) ≫
                      stageLeg T = b T := by
                    dsimp [stageLeg]
                    rw [pushout.inr_desc]
                  exact congrArg (fun q => completionSmallYoneda.{w}.map (incTgt (leOfHom h)) ≫ q)
                    hDesc
            _ = b S := hbInc (leOfHom h)
            _ = pushout.inr (a S) (completionSmallYoneda.{w}.map (data S).cell) ≫ stageLeg S :=
                  by
                    symm
                    dsimp [stageLeg]
                    rw [pushout.inr_desc]
    }
  }
  let initialStage : Finset cells.ι := ∅
  have hInitialStage (S : Finset cells.ι) : initialStage ⊆ S := by simp [initialStage]
  let base (Q : Cocone F) : X₁ ⟶ Q.pt :=
    pushout.inl (a initialStage) (completionSmallYoneda.{w}.map (data initialStage).cell) ≫
      Q.ι.app initialStage
  have baseFac (Q : Cocone F) (S : Finset cells.ι) :
      pushout.inl (a S) (completionSmallYoneda.{w}.map (data S).cell) ≫ Q.ι.app S = base Q := by
    calc
      pushout.inl (a S) (completionSmallYoneda.{w}.map (data S).cell) ≫ Q.ι.app S =
          (pushout.inl (a initialStage)
            (completionSmallYoneda.{w}.map (data initialStage).cell) ≫
              F.map (homOfLE (hInitialStage S))) ≫ Q.ι.app S :=
                congrArg (fun q => q ≫ Q.ι.app S)
                  (stageMapInl (hInitialStage S)).symm
      _ = pushout.inl (a initialStage)
            (completionSmallYoneda.{w}.map (data initialStage).cell) ≫
              (F.map (homOfLE (hInitialStage S)) ≫ Q.ι.app S) := Category.assoc _ _ _
      _ = base Q := by rw [Q.w (homOfLE (hInitialStage S))]
  let singleton (i : cells.ι) : Finset cells.ι := {i}
  let singletonIndex (i : cells.ι) : {j // j ∈ singleton i} :=
    ⟨i, by simp [singleton]⟩
  let z (Q : Cocone F) (i : cells.ι) : B (cells.π i) ⟶ Q.pt :=
    (eB i).hom ≫ completionSmallYoneda.{w}.map ((data (singleton i)).ιTgt (singletonIndex i)) ≫
      pushout.inr (a (singleton i))
        (completionSmallYoneda.{w}.map (data (singleton i)).cell) ≫ Q.ι.app (singleton i)
  let bMap (Q : Cocone F) : cells.cofan₂.pt ⟶ Q.pt :=
    Cofan.IsColimit.desc cells.isColimit₂ (fun i => z Q i)
  have bMapFac (Q : Cocone F) (i : cells.ι) :
      cells.cofan₂.inj i ≫ bMap Q = z Q i := by
    simpa [bMap] using Cofan.IsColimit.fac cells.isColimit₂ (fun j => z Q j) i
  have zAtStage (Q : Cocone F) {S : Finset cells.ι} (i : cells.ι) (hi : i ∈ S) :
      z Q i = (eB i).hom ≫ completionSmallYoneda.{w}.map ((data S).ιTgt ⟨i, hi⟩) ≫
        pushout.inr (a S) (completionSmallYoneda.{w}.map (data S).cell) ≫ Q.ι.app S := by
    let h : singleton i ⊆ S := by
      intro j hj
      have hj' : j = i := by simpa [singleton] using hj
      subst j
      exact hi
    calc
      z Q i = (eB i).hom ≫ completionSmallYoneda.{w}.map
          ((data (singleton i)).ιTgt (singletonIndex i)) ≫
            pushout.inr (a (singleton i))
              (completionSmallYoneda.{w}.map (data (singleton i)).cell) ≫
                (F.map (homOfLE h) ≫ Q.ι.app S) := by
          dsimp [z]
          rw [← Q.w (homOfLE h)]
      _ = (eB i).hom ≫ completionSmallYoneda.{w}.map
          ((data (singleton i)).ιTgt (singletonIndex i)) ≫
            (pushout.inr (a (singleton i))
              (completionSmallYoneda.{w}.map (data (singleton i)).cell) ≫
                F.map (homOfLE h)) ≫ Q.ι.app S := by
          simp [Category.assoc]
      _ = (eB i).hom ≫ completionSmallYoneda.{w}.map
          ((data (singleton i)).ιTgt (singletonIndex i)) ≫
            (completionSmallYoneda.{w}.map (incTgt h) ≫
              pushout.inr (a S) (completionSmallYoneda.{w}.map (data S).cell)) ≫
                Q.ι.app S := by
          rw [stageMapInr h]
      _ = (eB i).hom ≫ completionSmallYoneda.{w}.map
          ((data (singleton i)).ιTgt (singletonIndex i) ≫ incTgt h) ≫
            pushout.inr (a S) (completionSmallYoneda.{w}.map (data S).cell) ≫ Q.ι.app S := by
          simp only [← Category.assoc, ← (completionSmallYoneda.{w}).map_comp]
      _ = (eB i).hom ≫ completionSmallYoneda.{w}.map ((data S).ιTgt ⟨i, hi⟩) ≫
          pushout.inr (a S) (completionSmallYoneda.{w}.map (data S).cell) ≫ Q.ι.app S := by
          rw [incTgtFac h (singletonIndex i)]
  have hMapCell {S : Finset cells.ι} (i : cells.ι) (hi : i ∈ S) :
      completionSmallYoneda.{w}.map ((data S).ιSrc ⟨i, hi⟩) ≫
          completionSmallYoneda.{w}.map (data S).cell =
        completionSmallYoneda.{w}.map (c i) ≫
          completionSmallYoneda.{w}.map ((data S).ιTgt ⟨i, hi⟩) := by
    calc
      completionSmallYoneda.{w}.map ((data S).ιSrc ⟨i, hi⟩) ≫
          completionSmallYoneda.{w}.map (data S).cell =
          completionSmallYoneda.{w}.map ((data S).ιSrc ⟨i, hi⟩ ≫ (data S).cell) :=
            ((completionSmallYoneda.{w}).map_comp ((data S).ιSrc ⟨i, hi⟩) (data S).cell).symm
      _ = completionSmallYoneda.{w}.map (c i ≫ (data S).ιTgt ⟨i, hi⟩) := by
          rw [(data S).cellCondition ⟨i, hi⟩]
      _ = completionSmallYoneda.{w}.map (c i) ≫
          completionSmallYoneda.{w}.map ((data S).ιTgt ⟨i, hi⟩) :=
            (completionSmallYoneda.{w}).map_comp (c i) ((data S).ιTgt ⟨i, hi⟩)
  have hSingleSquare (Q : Cocone F) (i : cells.ι) :
      (completionSmallYoneda.{w}.map
        ((data (singleton i)).ιSrc (singletonIndex i)) ≫ a (singleton i)) ≫
          pushout.inl (a (singleton i))
            (completionSmallYoneda.{w}.map (data (singleton i)).cell) =
        completionSmallYoneda.{w}.map (c i) ≫
          completionSmallYoneda.{w}.map
            ((data (singleton i)).ιTgt (singletonIndex i)) ≫
              pushout.inr (a (singleton i))
                (completionSmallYoneda.{w}.map (data (singleton i)).cell) := by
    calc
      _ = completionSmallYoneda.{w}.map
            ((data (singleton i)).ιSrc (singletonIndex i)) ≫
              (a (singleton i) ≫ pushout.inl (a (singleton i))
                (completionSmallYoneda.{w}.map (data (singleton i)).cell)) :=
              Category.assoc _ _ _
      _ = completionSmallYoneda.{w}.map
            ((data (singleton i)).ιSrc (singletonIndex i)) ≫
              (completionSmallYoneda.{w}.map (data (singleton i)).cell ≫
                pushout.inr (a (singleton i))
                  (completionSmallYoneda.{w}.map (data (singleton i)).cell)) := by
              rw [pushout.condition]
      _ = (completionSmallYoneda.{w}.map
            ((data (singleton i)).ιSrc (singletonIndex i)) ≫
              completionSmallYoneda.{w}.map (data (singleton i)).cell) ≫
                pushout.inr (a (singleton i))
                  (completionSmallYoneda.{w}.map (data (singleton i)).cell) :=
              (Category.assoc _ _ _).symm
      _ = (completionSmallYoneda.{w}.map (c i) ≫
            completionSmallYoneda.{w}.map
              ((data (singleton i)).ιTgt (singletonIndex i))) ≫
                pushout.inr (a (singleton i))
                  (completionSmallYoneda.{w}.map (data (singleton i)).cell) :=
              congrArg (fun q => q ≫ pushout.inr _ _) (hMapCell i (by simp [singleton]))
      _ = completionSmallYoneda.{w}.map (c i) ≫
            completionSmallYoneda.{w}.map
              ((data (singleton i)).ιTgt (singletonIndex i)) ≫
                pushout.inr (a (singleton i))
                  (completionSmallYoneda.{w}.map (data (singleton i)).cell) :=
              Category.assoc _ _ _
  have hCellSource (Q : Cocone F) (i : cells.ι) :
      cells.cofan₁.inj i ≫ cells.g₁ ≫ base Q = g (cells.π i) ≫ z Q i := by
    calc
      cells.cofan₁.inj i ≫ cells.g₁ ≫ base Q =
          (eA i).hom ≫ ((eA i).inv ≫ cells.cofan₁.inj i ≫ cells.g₁) ≫ base Q := by
            simp [Category.assoc]
      _ = (eA i).hom ≫
          ((completionSmallYoneda.{w}.map
              ((data (singleton i)).ιSrc (singletonIndex i)) ≫ a (singleton i)) ≫ base Q) :=
            congrArg (fun q => (eA i).hom ≫ q ≫ base Q) (haFac (singleton i) (singletonIndex i)).symm
      _ = (eA i).hom ≫
          ((completionSmallYoneda.{w}.map
              ((data (singleton i)).ιSrc (singletonIndex i)) ≫ a (singleton i)) ≫
            (pushout.inl (a (singleton i))
              (completionSmallYoneda.{w}.map (data (singleton i)).cell) ≫
                Q.ι.app (singleton i))) :=
            congrArg (fun q => (eA i).hom ≫
              ((completionSmallYoneda.{w}.map
                ((data (singleton i)).ιSrc (singletonIndex i)) ≫ a (singleton i)) ≫ q))
              (baseFac Q (singleton i)).symm
      _ = (eA i).hom ≫
          (((completionSmallYoneda.{w}.map
              ((data (singleton i)).ιSrc (singletonIndex i)) ≫ a (singleton i)) ≫
            pushout.inl (a (singleton i))
              (completionSmallYoneda.{w}.map (data (singleton i)).cell)) ≫
                Q.ι.app (singleton i)) := by
              simp only [Category.assoc]
      _ = (eA i).hom ≫
          ((completionSmallYoneda.{w}.map (c i) ≫
              completionSmallYoneda.{w}.map
                ((data (singleton i)).ιTgt (singletonIndex i)) ≫
            pushout.inr (a (singleton i))
              (completionSmallYoneda.{w}.map (data (singleton i)).cell)) ≫
                Q.ι.app (singleton i)) :=
              congrArg (fun q => (eA i).hom ≫ q ≫ Q.ι.app (singleton i))
                (hSingleSquare Q i)
      _ = g (cells.π i) ≫ z Q i := by
            calc
              _ = (((eA i).hom ≫ completionSmallYoneda.{w}.map (c i)) ≫
                    completionSmallYoneda.{w}.map
                      ((data (singleton i)).ιTgt (singletonIndex i)) ≫
                    pushout.inr (a (singleton i))
                      (completionSmallYoneda.{w}.map (data (singleton i)).cell)) ≫
                    Q.ι.app (singleton i) := by simp [Category.assoc]
              _ = ((g (cells.π i) ≫ (eB i).hom) ≫
                    completionSmallYoneda.{w}.map
                      ((data (singleton i)).ιTgt (singletonIndex i)) ≫
                    pushout.inr (a (singleton i))
                      (completionSmallYoneda.{w}.map (data (singleton i)).cell)) ≫
                    Q.ι.app (singleton i) := by rw [hArrow i]
              _ = g (cells.π i) ≫ z Q i := by
                    dsimp [z]
                    simp [Category.assoc]
  have hCompat (Q : Cocone F) : cells.g₁ ≫ base Q = cells.m ≫ bMap Q := by
    apply Cofan.IsColimit.hom_ext cells.isColimit₁
    intro i
    calc
      cells.cofan₁.inj i ≫ cells.g₁ ≫ base Q =
          g (cells.π i) ≫ cells.cofan₂.inj i ≫ bMap Q := by
            calc
              _ = g (cells.π i) ≫ z Q i := hCellSource Q i
              _ = g (cells.π i) ≫ (cells.cofan₂.inj i ≫ bMap Q) :=
                    congrArg (fun q => g (cells.π i) ≫ q) (bMapFac Q i).symm
              _ = g (cells.π i) ≫ cells.cofan₂.inj i ≫ bMap Q := rfl
      _ = (cells.cofan₁.inj i ≫ cells.m) ≫ bMap Q := by
            calc
              _ = (g (cells.π i) ≫ cells.cofan₂.inj i) ≫ bMap Q :=
                    (Category.assoc _ _ _).symm
              _ = (cells.cofan₁.inj i ≫ cells.m) ≫ bMap Q :=
                    congrArg (fun q => q ≫ bMap Q) (cells.hm i).symm
      _ = cells.cofan₁.inj i ≫ cells.m ≫ bMap Q := Category.assoc _ _ _
  let extend (Q : Cocone F) : X₂ ⟶ Q.pt :=
    cells.isPushout.desc (base Q) (bMap Q) (hCompat Q)
  have extendInl (Q : Cocone F) : f ≫ extend Q = base Q := by
    dsimp [extend]
    exact cells.isPushout.inl_desc (base Q) (bMap Q) (hCompat Q)
  have extendInr (Q : Cocone F) : cells.g₂ ≫ extend Q = bMap Q := by
    dsimp [extend]
    exact cells.isPushout.inr_desc (base Q) (bMap Q) (hCompat Q)
  have targetFactor (Q : Cocone F) (S : Finset cells.ι) :
      b S ≫ extend Q =
        pushout.inr (a S) (completionSmallYoneda.{w}.map (data S).cell) ≫ Q.ι.app S := by
    apply Cofan.IsColimit.hom_ext (htgtY S)
    intro j
    calc
      completionSmallYoneda.{w}.map ((data S).ιTgt j) ≫ b S ≫ extend Q =
          (completionSmallYoneda.{w}.map ((data S).ιTgt j) ≫ b S) ≫ extend Q :=
            (Category.assoc _ _ _).symm
      _ = ((eB j.val).inv ≫ cells.cofan₂.inj j.val ≫ cells.g₂) ≫ extend Q :=
            congrArg (fun q => q ≫ extend Q) (hbFac S j)
      _ = (eB j.val).inv ≫ cells.cofan₂.inj j.val ≫ (cells.g₂ ≫ extend Q) := by
            simp [Category.assoc]
      _ = (eB j.val).inv ≫ cells.cofan₂.inj j.val ≫ bMap Q :=
            congrArg (fun q => (eB j.val).inv ≫ cells.cofan₂.inj j.val ≫ q)
              (extendInr Q)
      _ = (eB j.val).inv ≫ z Q j.val :=
            congrArg (fun q => (eB j.val).inv ≫ q) (bMapFac Q j.val)
      _ = completionSmallYoneda.{w}.map ((data S).ιTgt j) ≫
            pushout.inr (a S) (completionSmallYoneda.{w}.map (data S).cell) ≫ Q.ι.app S := by
              rw [zAtStage Q j.val j.property]
              simp [Category.assoc]
  have stageLegInl (S : Finset cells.ι) :
      pushout.inl (a S) (completionSmallYoneda.{w}.map (data S).cell) ≫ stageLeg S = f := by
    dsimp [stageLeg]
    rw [pushout.inl_desc]
  have stageLegInr (S : Finset cells.ι) :
      pushout.inr (a S) (completionSmallYoneda.{w}.map (data S).cell) ≫ stageLeg S = b S := by
    dsimp [stageLeg]
    rw [pushout.inr_desc]
  have extendFactor (Q : Cocone F) (S : Finset cells.ι) :
      stageLeg S ≫ extend Q = Q.ι.app S := by
    apply pushout.hom_ext
    · calc
        pushout.inl (a S) (completionSmallYoneda.{w}.map (data S).cell) ≫
            (stageLeg S ≫ extend Q) =
            (pushout.inl (a S) (completionSmallYoneda.{w}.map (data S).cell) ≫ stageLeg S) ≫
              extend Q := (Category.assoc _ _ _).symm
        _ = f ≫ extend Q := congrArg (fun q => q ≫ extend Q) (stageLegInl S)
        _ = base Q := extendInl Q
        _ = pushout.inl (a S) (completionSmallYoneda.{w}.map (data S).cell) ≫ Q.ι.app S :=
              (baseFac Q S).symm
    · calc
        pushout.inr (a S) (completionSmallYoneda.{w}.map (data S).cell) ≫
            (stageLeg S ≫ extend Q) =
            (pushout.inr (a S) (completionSmallYoneda.{w}.map (data S).cell) ≫ stageLeg S) ≫
              extend Q := (Category.assoc _ _ _).symm
        _ = b S ≫ extend Q := congrArg (fun q => q ≫ extend Q) (stageLegInr S)
        _ = pushout.inr (a S) (completionSmallYoneda.{w}.map (data S).cell) ≫ Q.ι.app S :=
              targetFactor Q S
  have cellFactor (i : cells.ι) :
      cells.cell i = (eB i).hom ≫
        completionSmallYoneda.{w}.map
          ((data (singleton i)).ιTgt (singletonIndex i)) ≫
        pushout.inr (a (singleton i))
          (completionSmallYoneda.{w}.map (data (singleton i)).cell) ≫ stageLeg (singleton i) := by
    change cells.cofan₂.inj i ≫ cells.g₂ = _
    calc
      cells.cofan₂.inj i ≫ cells.g₂ =
          (eB i).hom ≫ ((eB i).inv ≫ cells.cofan₂.inj i ≫ cells.g₂) := by simp [Category.assoc]
      _ = (eB i).hom ≫
          (completionSmallYoneda.{w}.map
            ((data (singleton i)).ιTgt (singletonIndex i)) ≫ b (singleton i)) :=
            congrArg (fun q => (eB i).hom ≫ q)
              (hbFac (singleton i) (singletonIndex i)).symm
      _ = (eB i).hom ≫ completionSmallYoneda.{w}.map
          ((data (singleton i)).ιTgt (singletonIndex i)) ≫
            (pushout.inr (a (singleton i))
              (completionSmallYoneda.{w}.map (data (singleton i)).cell) ≫
                stageLeg (singleton i)) := by
              rw [stageLegInr]
  have isColimitK : IsColimit K := by
    refine { desc := extend, fac := fun Q S => extendFactor Q S, uniq := ?_ }
    intro Q m hm
    apply cells.hom_ext
    · calc
        f ≫ m = (pushout.inl (a initialStage)
            (completionSmallYoneda.{w}.map (data initialStage).cell) ≫
              stageLeg initialStage) ≫ m :=
                congrArg (fun q => q ≫ m) (stageLegInl initialStage).symm
        _ = pushout.inl (a initialStage)
            (completionSmallYoneda.{w}.map (data initialStage).cell) ≫
              (stageLeg initialStage ≫ m) := Category.assoc _ _ _
        _ = pushout.inl (a initialStage)
            (completionSmallYoneda.{w}.map (data initialStage).cell) ≫
              Q.ι.app initialStage :=
                congrArg (fun q => pushout.inl (a initialStage)
                  (completionSmallYoneda.{w}.map (data initialStage).cell) ≫ q)
                  (hm initialStage)
        _ = base Q := baseFac Q initialStage
        _ = f ≫ extend Q := (extendInl Q).symm
    · intro i
      have hCellExtend : cells.cell i ≫ extend Q = z Q i := by
        rw [cellFactor i]
        calc
          _ = (eB i).hom ≫
              completionSmallYoneda.{w}.map
                ((data (singleton i)).ιTgt (singletonIndex i)) ≫
              pushout.inr (a (singleton i))
                (completionSmallYoneda.{w}.map (data (singleton i)).cell) ≫
              (stageLeg (singleton i) ≫ extend Q) := by simp [Category.assoc]
          _ = z Q i := by rw [extendFactor Q (singleton i)]
      have hCellM : cells.cell i ≫ m = z Q i := by
        rw [cellFactor i]
        calc
          _ = (eB i).hom ≫
              completionSmallYoneda.{w}.map
                ((data (singleton i)).ιTgt (singletonIndex i)) ≫
              pushout.inr (a (singleton i))
                (completionSmallYoneda.{w}.map (data (singleton i)).cell) ≫
              (stageLeg (singleton i) ≫ m) := by simp [Category.assoc]
          _ = z Q i := by rw [hm (singleton i)]
      exact hCellM.trans hCellExtend.symm
  refine ⟨isFlat_of_isColimit isColimitK (fun S => hObjFlat S), ?_⟩
  intro hP
  haveI : IsConnected (Finset cells.ι) :=
    isConnected_of_isInitial (Finset cells.ι) Limits.isInitialBot
  let F₀ : Finset cells.ι ⥤ Completion.{w} C :=
    (Functor.const (Finset cells.ι)).obj X₁
  let t : F₀ ⟶ F := {
    app := fun S => pushout.inl (a S) (completionSmallYoneda.{w}.map (data S).cell)
    naturality := by
      intro S T h
      change 𝟙 X₁ ≫ pushout.inl (a T) (completionSmallYoneda.{w}.map (data T).cell) =
        pushout.inl (a S) (completionSmallYoneda.{w}.map (data S).cell) ≫
          stageMap (leOfHom h)
      rw [Category.id_comp, stageMapInl]
  }
  have ht (S : Finset cells.ι) : Completion.weakEquivalences C (t.app S) := by
    simpa [t] using hObjWeak S hP
  exact completion_weakEquivalence_of_isColimit t ht
    (isColimitConstCocone (Finset cells.ι) X₁) isColimitK f (by
      intro S
      change 𝟙 X₁ ≫ f =
        pushout.inl (a S) (completionSmallYoneda.{w}.map (data S).cell) ≫ stageLeg S
      rw [Category.id_comp]
      exact (stageLegInl S).symm)

end HomotopyHypothesis.Category.SemiModelStructure
