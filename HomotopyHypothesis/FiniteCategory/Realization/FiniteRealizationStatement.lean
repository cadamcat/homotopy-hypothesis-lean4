import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Interfaces.AfinIotaMapInitial
import HomotopyHypothesis.Blueprint.Interfaces.AfinIotaMapIsPushout
import HomotopyHypothesis.Cylinder.FiniteCellCategory.FiniteCells
import HomotopyHypothesis.FiniteCategory.Lifting.HelperStatements
import HomotopyHypothesis.FiniteCategory.Lifting.Nerve
noncomputable section

universe u v

open CategoryTheory Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Blueprint HomotopyHypothesis.Henry HomotopyHypothesis.FiniteCategory.Lifting

namespace HomotopyHypothesis.FiniteCategory.Realization

variable {C : GlobularTheory.{v}} {X : Type u} [Category.{v} X]

theorem leftAdjointObjIsDefined_of_iso (R : TheoryInterpretation C X) {A B : C.Model}
    (e : A ≅ B) (hA : R.nerve.leftAdjointObjIsDefined A) :
    R.nerve.leftAdjointObjIsDefined B := by
  let F₀ := R.nerve ⋙ coyoneda.obj (op A)
  let F₁ := R.nerve ⋙ coyoneda.obj (op B)
  have hF₀ : F₀.IsCorepresentable := hA
  let e' : F₀ ≅ F₁ := Functor.isoWhiskerLeft R.nerve (coyoneda.mapIso e.symm.op)
  letI : F₀.IsCorepresentable := hF₀
  exact (F₀.corepresentableBy.ofIso e').isCorepresentable

theorem leftAdjointObjIsDefined_of_pushout (R : TheoryInterpretation C X)
    [CategoryWithCofibrations X] [IsCofibrationCategory X]
    {A B Y P : C.Model} (i : A ⟶ B) (f : A ⟶ Y) (k : B ⟶ P) (j : Y ⟶ P)
    (sq : IsPushout i f k j)
    (hA : R.nerve.leftAdjointObjIsDefined A)
    (hB : R.nerve.leftAdjointObjIsDefined B)
    (hY : R.nerve.leftAdjointObjIsDefined Y)
    (hi : cofibrations X
      (R.nerve.partialLeftAdjoint.map
        (ObjectProperty.homMk i :
          (⟨A, hA⟩ : R.nerve.PartialLeftAdjointSource) ⟶ ⟨B, hB⟩))) :
    R.nerve.leftAdjointObjIsDefined P := by
  let D := span i f
  let D' : WalkingSpan ⥤ R.nerve.PartialLeftAdjointSource :=
    ObjectProperty.lift R.nerve.leftAdjointObjIsDefined D (by
      intro j'
      rcases j' with _ | j'
      · simpa [D] using hA
      · rcases j' with _ | _
        · simpa [D] using hB
        · simpa [D] using hY)
  let i' := D'.map WalkingSpan.Hom.fst
  let f' := D'.map WalkingSpan.Hom.snd
  letI : HasPushout (R.nerve.partialLeftAdjoint.map i')
      (R.nerve.partialLeftAdjoint.map f') :=
    IsCofibrationCategory.hasPushout _ _ hi
  let sq' := IsPushout.of_hasPushout
    (R.nerve.partialLeftAdjoint.map i') (R.nerve.partialLeftAdjoint.map f')
  let sourcePushout : PushoutCocone i f := PushoutCocone.mk k j sq.w
  have hSourcePushout : IsColimit sourcePushout := by
    change IsColimit sourcePushout
    exact sq.isColimit
  let c : Cocone (D' ⋙ ObjectProperty.ι _) := sourcePushout
  have hc : IsColimit c := hSourcePushout
  have hcLeft : c.ι.app WalkingSpan.left = k := rfl
  have hcRight : c.ι.app WalkingSpan.right = j := rfl
  let c' : Cocone (D' ⋙ R.nerve.partialLeftAdjoint) :=
    Cocone.ofPushoutCocone sq'.cocone
  let hc' : IsColimit c' := by
    exact (IsColimit.precomposeHomEquiv
      (diagramIsoSpan (D' ⋙ R.nerve.partialLeftAdjoint)) sq'.cocone).symm sq'.isColimit
  exact (Functor.corepresentableByCompCoyonedaObjOfIsColimit
    (R := D') hc hc').isCorepresentable

theorem partialLeftAdjoint_map_isPushout (R : TheoryInterpretation C X)
    [CategoryWithCofibrations X] [IsCofibrationCategory X]
    {A B Y P : C.Model} (i : A ⟶ B) (f : A ⟶ Y) (k : B ⟶ P) (j : Y ⟶ P)
    (sq : IsPushout i f k j)
    (hA : R.nerve.leftAdjointObjIsDefined A)
    (hB : R.nerve.leftAdjointObjIsDefined B)
    (hY : R.nerve.leftAdjointObjIsDefined Y)
    (hP : R.nerve.leftAdjointObjIsDefined P)
    (hi : cofibrations X
      (R.nerve.partialLeftAdjoint.map
        (ObjectProperty.homMk i :
          (⟨A, hA⟩ : R.nerve.PartialLeftAdjointSource) ⟶ ⟨B, hB⟩))) :
    IsPushout (R.nerve.partialLeftAdjoint.map
        (ObjectProperty.homMk i :
          (⟨A, hA⟩ : R.nerve.PartialLeftAdjointSource) ⟶ ⟨B, hB⟩))
      (R.nerve.partialLeftAdjoint.map
        (ObjectProperty.homMk f :
          (⟨A, hA⟩ : R.nerve.PartialLeftAdjointSource) ⟶ ⟨Y, hY⟩))
      (R.nerve.partialLeftAdjoint.map
        (ObjectProperty.homMk k :
          (⟨B, hB⟩ : R.nerve.PartialLeftAdjointSource) ⟶ ⟨P, hP⟩))
      (R.nerve.partialLeftAdjoint.map
        (ObjectProperty.homMk j :
          (⟨Y, hY⟩ : R.nerve.PartialLeftAdjointSource) ⟶ ⟨P, hP⟩)) := by
  let A₀ : R.nerve.PartialLeftAdjointSource := ⟨A, hA⟩
  let B₀ : R.nerve.PartialLeftAdjointSource := ⟨B, hB⟩
  let Y₀ : R.nerve.PartialLeftAdjointSource := ⟨Y, hY⟩
  let P₀ : R.nerve.PartialLeftAdjointSource := ⟨P, hP⟩
  let L := R.nerve.partialLeftAdjoint
  let i₀ : A₀ ⟶ B₀ := ObjectProperty.homMk i
  let f₀ : A₀ ⟶ Y₀ := ObjectProperty.homMk f
  let k₀ : B₀ ⟶ P₀ := ObjectProperty.homMk k
  let j₀ : Y₀ ⟶ P₀ := ObjectProperty.homMk j
  let iL := R.nerve.partialLeftAdjointMap i₀
  let fL := R.nerve.partialLeftAdjointMap f₀
  let kL := R.nerve.partialLeftAdjointMap k₀
  let jL := R.nerve.partialLeftAdjointMap j₀
  let eA (Z : X) := R.nerve.partialLeftAdjointHomEquiv (X := A₀) (Y := Z)
  let eB (Z : X) := R.nerve.partialLeftAdjointHomEquiv (X := B₀) (Y := Z)
  let eY (Z : X) := R.nerve.partialLeftAdjointHomEquiv (X := Y₀) (Y := Z)
  let eP (Z : X) := R.nerve.partialLeftAdjointHomEquiv (X := P₀) (Y := Z)
  let cL : PushoutCocone iL fL :=
    PushoutCocone.mk kL jL (by
      change L.map i₀ ≫ L.map k₀ = L.map f₀ ≫ L.map j₀
      rw [← L.map_comp, ← L.map_comp]
      apply congrArg L.map
      apply ObjectProperty.hom_ext
      exact sq.w)
  have hcompat (s : PushoutCocone iL fL) :
      i ≫ eB s.pt s.inl = f ≫ eY s.pt s.inr := by
    have hleft : eA s.pt (iL ≫ s.inl) = i ≫ eB s.pt s.inl := by
      change R.nerve.partialLeftAdjointHomEquiv (iL ≫ s.inl) = _
      rw [R.nerve.partialLeftAdjointHomEquiv_map_comp]
      rfl
    have hright : eA s.pt (fL ≫ s.inr) = f ≫ eY s.pt s.inr := by
      change R.nerve.partialLeftAdjointHomEquiv (fL ≫ s.inr) = _
      rw [R.nerve.partialLeftAdjointHomEquiv_map_comp]
      rfl
    calc
      i ≫ eB s.pt s.inl = eA s.pt (iL ≫ s.inl) := hleft.symm
      _ = eA s.pt (fL ≫ s.inr) := congrArg (eA s.pt) s.condition
      _ = f ≫ eY s.pt s.inr := hright
  let desc (s : PushoutCocone iL fL) : R.nerve.partialLeftAdjointObj P₀ ⟶ s.pt :=
    (eP s.pt).symm (sq.desc (eB s.pt s.inl) (eY s.pt s.inr) (hcompat s))
  have facLeft (s : PushoutCocone iL fL) :
      cL.inl ≫ desc s = s.inl := by
    apply (eB s.pt).injective
    change R.nerve.partialLeftAdjointHomEquiv
      (kL ≫ desc s) = R.nerve.partialLeftAdjointHomEquiv s.inl
    rw [R.nerve.partialLeftAdjointHomEquiv_map_comp]
    change k ≫ eP s.pt (desc s) = eB s.pt s.inl
    dsimp [desc]
    rw [Equiv.apply_symm_apply]
    exact sq.inl_desc (eB s.pt s.inl) (eY s.pt s.inr) (hcompat s)
  have facRight (s : PushoutCocone iL fL) :
      cL.inr ≫ desc s = s.inr := by
    apply (eY s.pt).injective
    change R.nerve.partialLeftAdjointHomEquiv
      (jL ≫ desc s) = R.nerve.partialLeftAdjointHomEquiv s.inr
    rw [R.nerve.partialLeftAdjointHomEquiv_map_comp]
    change j ≫ eP s.pt (desc s) = eY s.pt s.inr
    dsimp [desc]
    rw [Equiv.apply_symm_apply]
    exact sq.inr_desc (eB s.pt s.inl) (eY s.pt s.inr) (hcompat s)
  have uniq (s : PushoutCocone iL fL) (m : R.nerve.partialLeftAdjointObj P₀ ⟶ s.pt)
      (hm : ∀ j', cL.ι.app j' ≫ m = s.ι.app j') : m = desc s := by
    apply (eP s.pt).injective
    apply sq.hom_ext
    · have h := congrArg (eB s.pt) (hm WalkingSpan.left)
      change R.nerve.partialLeftAdjointHomEquiv
        (kL ≫ m) = R.nerve.partialLeftAdjointHomEquiv s.inl at h
      rw [R.nerve.partialLeftAdjointHomEquiv_map_comp] at h
      calc
        k ≫ eP s.pt m = eB s.pt s.inl := by simpa [k₀] using h
        _ = k ≫ eP s.pt (desc s) := by
          simp [desc]
    · have h := congrArg (eY s.pt) (hm WalkingSpan.right)
      change R.nerve.partialLeftAdjointHomEquiv
        (jL ≫ m) = R.nerve.partialLeftAdjointHomEquiv s.inr at h
      rw [R.nerve.partialLeftAdjointHomEquiv_map_comp] at h
      calc
        j ≫ eP s.pt m = eY s.pt s.inr := by simpa [j₀] using h
        _ = j ≫ eP s.pt (desc s) := by
          simp [desc]
  exact IsPushout.of_isColimit (PushoutCocone.isColimitAux cL desc facLeft facRight uniq)

theorem leftAdjointObjIsDefined_of_finiteCellMap (R : TheoryInterpretation C X)
    [CategoryWithCofibrations X] [IsCofibrationCategory X]
    (hb : ∀ n, R.nerve.leftAdjointObjIsDefined (boundaryDisk C n))
    (hc : ∀ n, cofibrations X (R.nerve.partialLeftAdjoint.map
      (ObjectProperty.homMk (I C n) :
        (⟨boundaryDisk C n, hb n⟩ : R.nerve.PartialLeftAdjointSource) ⟶
          ⟨disk C n, R.freeShape_leftAdjointObjIsDefined (Shape.globe n)⟩)))
    {A B : C.Model} (f : A ⟶ B) (hf : finiteCellMaps C f)
    (hA : R.nerve.leftAdjointObjIsDefined A) :
    R.nerve.leftAdjointObjIsDefined B := by
  let G : MorphismProperty C.Model :=
    (MorphismProperty.ofHoms (fun n : ℕ => I C n)).pushouts ⊔
      MorphismProperty.isomorphisms C.Model
  change G.multiplicativeClosure f at hf
  have hGenerator : ∀ {A B : C.Model} (g : A ⟶ B), G g →
      R.nerve.leftAdjointObjIsDefined A → R.nerve.leftAdjointObjIsDefined B := by
    intro A B g hg hA
    rcases hg with hpush | hiso
    · rcases hpush with ⟨A', B', p, a, b, hp, hsq⟩
      cases hp with
      | mk n =>
          exact leftAdjointObjIsDefined_of_pushout R (I C n) a b g hsq.flip
            (hb n) (R.freeShape_leftAdjointObjIsDefined (Shape.globe n)) hA (hc n)
    · haveI : IsIso g := hiso
      exact leftAdjointObjIsDefined_of_iso R (asIso g) hA
  induction hf with
  | of g hg => exact hGenerator g hg hA
  | id A => exact hA
  | comp_of f g hf hg ih => exact hGenerator g hg (ih hA)

theorem finiteCellMaps_map_cofibration (R : TheoryInterpretation C X)
    [CategoryWithCofibrations X] [IsCofibrationCategory X]
    (hReal : ∀ M : C.Model, IsFinitelyCellular C M →
      R.nerve.leftAdjointObjIsDefined M)
    (hb : ∀ n, R.nerve.leftAdjointObjIsDefined (boundaryDisk C n))
    (hc : ∀ n, cofibrations X (R.nerve.partialLeftAdjoint.map
      (ObjectProperty.homMk (I C n) :
        (⟨boundaryDisk C n, hb n⟩ : R.nerve.PartialLeftAdjointSource) ⟶
          ⟨disk C n, R.freeShape_leftAdjointObjIsDefined (Shape.globe n)⟩)))
    {A B : C.Model} (f : A ⟶ B) (hf : finiteCellMaps C f)
    (hA : IsFinitelyCellular C A) :
    cofibrations X (R.nerve.partialLeftAdjoint.map
      (ObjectProperty.homMk f :
        (⟨A, hReal A hA⟩ : R.nerve.PartialLeftAdjointSource) ⟶
          ⟨B, hReal B (Cylinder.FiniteCellCategory.isFinitelyCellular_of_finiteCellMap hA f hf)⟩)) := by
  let G : MorphismProperty C.Model :=
    (MorphismProperty.ofHoms (fun n : ℕ => I C n)).pushouts ⊔
      MorphismProperty.isomorphisms C.Model
  change G.multiplicativeClosure f at hf
  have hGenerator : ∀ {A B : C.Model} (g : A ⟶ B) (hg : G g)
      (hA : IsFinitelyCellular C A),
      cofibrations X (R.nerve.partialLeftAdjoint.map
        (ObjectProperty.homMk g :
          (⟨A, hReal A hA⟩ : R.nerve.PartialLeftAdjointSource) ⟶
            ⟨B, hReal B (Cylinder.FiniteCellCategory.isFinitelyCellular_of_finiteCellMap hA g
              ((MorphismProperty.le_multiplicativeClosure G) g hg))⟩)) := by
    intro A B g hg hA
    rcases hg with hpush | hiso
    · rcases hpush with ⟨A', B', p, a, b, hp, hsq⟩
      have hgenCell : finiteCellMaps C g :=
        by
          apply MorphismProperty.le_multiplicativeClosure
          apply Or.inl
          exact (MorphismProperty.ofHoms (fun n : ℕ => I C n)).pushouts_mk hsq hp
      cases hp with
      | mk n =>
          have hBcell : IsFinitelyCellular C B :=
            Cylinder.FiniteCellCategory.isFinitelyCellular_of_finiteCellMap hA g hgenCell
          have hAreal := hReal A hA
          have hBreal := hReal B hBcell
          have hDisk : R.nerve.leftAdjointObjIsDefined (disk C n) :=
            R.freeShape_leftAdjointObjIsDefined (Shape.globe n)
          have hPush : IsPushout
              (R.nerve.partialLeftAdjoint.map
                (ObjectProperty.homMk (I C n) :
                  (⟨boundaryDisk C n, hb n⟩ : R.nerve.PartialLeftAdjointSource) ⟶
                    ⟨disk C n, hDisk⟩))
              (R.nerve.partialLeftAdjoint.map
                (ObjectProperty.homMk a :
                  (⟨boundaryDisk C n, hb n⟩ : R.nerve.PartialLeftAdjointSource) ⟶
                    ⟨A, hAreal⟩))
              (R.nerve.partialLeftAdjoint.map
                (ObjectProperty.homMk b :
                  (⟨disk C n, hDisk⟩ : R.nerve.PartialLeftAdjointSource) ⟶
                    ⟨B, hBreal⟩))
              (R.nerve.partialLeftAdjoint.map
                (ObjectProperty.homMk g :
                  (⟨A, hAreal⟩ : R.nerve.PartialLeftAdjointSource) ⟶
                    ⟨B, hBreal⟩)) := by
            exact partialLeftAdjoint_map_isPushout R (I C n) a b g hsq.flip
              (hb n) hDisk hAreal hBreal (hc n)
          exact (IsCofibrationCategory.isStableUnderCobaseChange
            (C := X)).of_isPushout hPush.flip (hc n)
    · haveI : IsIso g := hiso
      have hBcell : IsFinitelyCellular C B :=
        Cylinder.FiniteCellCategory.isFinitelyCellular_of_finiteCellMap hA g
          ((MorphismProperty.le_multiplicativeClosure G) g (Or.inr hiso))
      let g₀ : (⟨A, hReal A hA⟩ : R.nerve.PartialLeftAdjointSource) ⟶
          ⟨B, hReal B hBcell⟩ := ObjectProperty.homMk g
      have hIsoHom : IsIso g₀.hom := by
        change IsIso g
        exact hiso
      haveI : IsIso g₀ := (ObjectProperty.isIso_hom_iff g₀).1 hIsoHom
      have hMapIso : IsIso (R.nerve.partialLeftAdjoint.map g₀) := by
        infer_instance
      exact IsCofibrationCategory.isomorphisms_le (C := X)
        (R.nerve.partialLeftAdjoint.map g₀) hMapIso
  induction hf with
  | of g hg => exact hGenerator g hg hA
  | id A =>
      let id₀ : (⟨A, hReal A hA⟩ : R.nerve.PartialLeftAdjointSource) ⟶
          ⟨A, hReal A hA⟩ := ObjectProperty.homMk (𝟙 A)
      have hIdHom : IsIso id₀.hom := by
        change IsIso (𝟙 A)
        infer_instance
      haveI : IsIso id₀ := (ObjectProperty.isIso_hom_iff id₀).1 hIdHom
      have hMapIso : IsIso (R.nerve.partialLeftAdjoint.map id₀) := by infer_instance
      exact IsCofibrationCategory.isomorphisms_le (C := X) _ hMapIso
  | @comp_of A B D f g hf hg ih =>
      have hBcell : IsFinitelyCellular C B :=
        Cylinder.FiniteCellCategory.isFinitelyCellular_of_finiteCellMap hA f hf
      have hDcell : IsFinitelyCellular C D :=
        Cylinder.FiniteCellCategory.isFinitelyCellular_of_finiteCellMap hBcell g
          ((MorphismProperty.le_multiplicativeClosure G) g hg)
      let f₀ : (⟨A, hReal A hA⟩ : R.nerve.PartialLeftAdjointSource) ⟶
          ⟨B, hReal B hBcell⟩ := ObjectProperty.homMk f
      let g₀ : (⟨B, hReal B hBcell⟩ : R.nerve.PartialLeftAdjointSource) ⟶
          ⟨D, hReal D hDcell⟩ := ObjectProperty.homMk g
      let fg₀ : (⟨A, hReal A hA⟩ : R.nerve.PartialLeftAdjointSource) ⟶
          ⟨D, hReal D hDcell⟩ := ObjectProperty.homMk (f ≫ g)
      have hcomp := (IsCofibrationCategory.isMultiplicative (C := X)).comp_mem _ _
        (ih hA) (hGenerator g hg hBcell)
      have hhom : f₀ ≫ g₀ = fg₀ := by
        apply ObjectProperty.hom_ext
        rfl
      rw [← R.nerve.partialLeftAdjoint.map_comp, hhom] at hcomp
      exact hcomp

theorem finiteRealizationStatement_proof
    {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    {X : Type u} [Category.{v} X] [CategoryWithCofibrations X]
    [IsCofibrationCategory X] (R : TheoryInterpretation C X)
    (hb : ∀ n, R.nerve.leftAdjointObjIsDefined (boundaryDisk C n))
    (hc : ∀ n, cofibrations X (R.nerve.partialLeftAdjoint.map
      (ObjectProperty.homMk (I C n) :
        (⟨boundaryDisk C n, hb n⟩ : R.nerve.PartialLeftAdjointSource) ⟶
          ⟨disk C n, R.freeShape_leftAdjointObjIsDefined (Shape.globe n)⟩))) :
    FiniteRealizationStatement hC R hb hc := by
  obtain ⟨O, hO⟩ := IsCofibrationCategory.exists_initial (C := X)
  obtain ⟨hO⟩ := hO
  have hInit := R.initial_leftAdjointObjIsDefined initialIsInitial hO
  let H : ∀ M : C.Model, IsFinitelyCellular C M →
      R.nerve.leftAdjointObjIsDefined M := fun M hM =>
    leftAdjointObjIsDefined_of_finiteCellMap R hb hc (initial.to M) hM hInit
  let F := R.finiteRealization hC H
  refine ⟨H, ?_⟩
  refine {
    map_cofibration := ?_
    map_initial := ?_
    map_isPushout := ?_ }
  · intro A B f hf
    change finiteCellMaps C f.hom at hf
    change cofibrations X (R.nerve.partialLeftAdjoint.map
      (ObjectProperty.homMk f.hom :
        (⟨A.obj, H A.obj A.property⟩ : R.nerve.PartialLeftAdjointSource) ⟶
          ⟨B.obj, H B.obj B.property⟩))
    exact finiteCellMaps_map_cofibration R H hb hc f.hom hf A.property
  · intro I hI
    obtain ⟨hIModel⟩ := Packages.afin_ι_map_initial hC hI
    obtain ⟨O, hO⟩ := IsCofibrationCategory.exists_initial (C := X)
    obtain ⟨hO⟩ := hO
    let I₀ : R.nerve.PartialLeftAdjointSource := ⟨I.obj, H I.obj I.property⟩
    let FI := R.nerve ⋙ coyoneda.obj (op I.obj)
    letI : FI.IsCorepresentable := H I.obj I.property
    let eI := FI.corepresentableBy
    let eO := R.initialCorepresentable hIModel hO
    let e : R.nerve.partialLeftAdjointObj I₀ ≅ O := eI.uniqueUpToIso eO
    change Nonempty (IsInitial (R.nerve.partialLeftAdjoint.obj I₀))
    exact ⟨hO.ofIso e.symm⟩
  · intro A B Y P i f k j hsq hi
    have hsqModel := Packages.afin_ι_map_isPushout hC i f k j hsq hi
    change IsPushout i.hom f.hom k.hom j.hom at hsqModel
    change finiteCellMaps C i.hom at hi
    have hIcof : cofibrations X
        (R.nerve.partialLeftAdjoint.map
          (ObjectProperty.homMk i.hom :
            (⟨A.obj, H A.obj A.property⟩ : R.nerve.PartialLeftAdjointSource) ⟶
              ⟨B.obj, H B.obj B.property⟩)) :=
      finiteCellMaps_map_cofibration R H hb hc i.hom hi A.property
    exact partialLeftAdjoint_map_isPushout R i.hom f.hom k.hom j.hom hsqModel
      (H A.obj A.property) (H B.obj B.property) (H Y.obj Y.property) (H P.obj P.property)
      hIcof

example : ∀ {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    {X : Type u} [Category.{v} X] [CategoryWithCofibrations X]
    [IsCofibrationCategory X] (R : TheoryInterpretation C X)
    (hb : ∀ n, R.nerve.leftAdjointObjIsDefined (boundaryDisk C n))
    (hc : ∀ n, cofibrations X (R.nerve.partialLeftAdjoint.map
      (ObjectProperty.homMk (I C n) :
        (⟨boundaryDisk C n, hb n⟩ : R.nerve.PartialLeftAdjointSource) ⟶
          ⟨disk C n, R.freeShape_leftAdjointObjIsDefined (Shape.globe n)⟩))),
    FiniteRealizationStatement hC R hb hc :=
  @finiteRealizationStatement_proof

#print axioms finiteRealizationStatement_proof

end HomotopyHypothesis.FiniteCategory.Realization
