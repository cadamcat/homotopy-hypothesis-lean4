import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Interfaces.AfinIotaMapIsPushout
import HomotopyHypothesis.Blueprint.Interfaces.AfinIsCylinderCategory
import HomotopyHypothesis.Blueprint.Interfaces.DiskFinitelyCellular
import HomotopyHypothesis.Blueprint.Interfaces.Fibrant
import HomotopyHypothesis.Blueprint.Interfaces.LiftingTest
import HomotopyHypothesis.Blueprint.Interfaces.Restriction
import HomotopyHypothesis.Blueprint.Interfaces.TrivialCofibrationLift
import HomotopyHypothesis.Blueprint.Interfaces.WeakEquivalenceClosure
import HomotopyHypothesis.Blueprint.Interfaces.WeakEquivalenceTwoOutOfSix
import HomotopyHypothesis.Cylinder.FiniteCellCategory.CellCylinders
import HomotopyHypothesis.Cylinder.FiniteCellCategory.Cofibrations
import HomotopyHypothesis.Cylinder.FiniteCellCategory.FiniteCells
import HomotopyHypothesis.Cylinder.FiniteCellCategory.WeakEquivalences
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Blueprint HomotopyHypothesis.Henry

namespace HomotopyHypothesis.Homotopy.WeakEquivalence

universe u v

variable {C : GlobularTheory.{u}}

private abbrev boundaryMaps (C : GlobularTheory.{u}) : MorphismProperty C.Model :=
  MorphismProperty.ofHoms (fun n : ℕ => I C n)

private abbrev sourceMaps (C : GlobularTheory.{u}) : MorphismProperty C.Model :=
  MorphismProperty.ofHoms (fun n : ℕ => J C n)

private abbrev ModelCofibrant (C : GlobularTheory.{u}) (X : C.Model) : Prop :=
  (boundaryMaps C).rlp.llp (initial.to X)

private theorem boundaryRlp_weakEquivalence {C : GlobularTheory.{u}}
    (hC : C.IsCoherator) {X Y : C.Model} (p : X ⟶ Y)
    (hp : (boundaryMaps C).rlp p) : W hC p ∧ (sourceMaps C).rlp p := by
  have h := congrArg (fun P : MorphismProperty C.Model => P p) (Packages.lifting_test hC)
  exact h.mp hp

private theorem factorByBoundary {C : GlobularTheory.{u}} (_hC : C.IsCoherator)
    {X Y : C.Model} (f : X ⟶ Y) :
    ∃ (Z : C.Model) (i : X ⟶ Z) (p : Z ⟶ Y),
      (boundaryMaps C).rlp.llp i ∧ (boundaryMaps C).rlp p ∧ i ≫ p = f := by
  let _ := smallObjectArgument_of_finiteDomains (fun n : ℕ => I C n)
  let F := MorphismProperty.factorizationData
    (boundaryMaps C).rlp.llp (boundaryMaps C).rlp f
  exact ⟨F.Z, F.i, F.p, F.hi, F.hp, F.fac⟩

private def modelCofibrationData (C : GlobularTheory.{u}) :
    CategoryWithCofibrations C.Model := ⟨(boundaryMaps C).rlp.llp⟩

private def modelWeakEquivalenceData (hC : C.IsCoherator) :
    CategoryWithWeakEquivalences C.Model := ⟨W hC⟩

private structure ModelRelativeCylinder (hC : C.IsCoherator) {X Z : C.Model}
    (e : X ⟶ Z) where
  P : C.Model
  j₀ : Z ⟶ P
  j₁ : Z ⟶ P
  isPushout : IsPushout e e j₀ j₁
  I : C.Model
  c : P ⟶ I
  p : I ⟶ Z
  c_mem : (boundaryMaps C).rlp.llp c
  p_mem : W hC p
  j₀_c_p : j₀ ≫ c ≫ p = 𝟙 Z
  j₁_c_p : j₁ ≫ c ≫ p = 𝟙 Z

private theorem trivialCofibration_retraction {X Z : C.Model} (hC : C.IsCoherator)
    (e : X ⟶ Z)
    (he : (boundaryMaps C).rlp.llp e) (hwe : W hC e) (hX : ModelCofibrant C X) :
    ∃ r : Z ⟶ X, e ≫ r = 𝟙 X := by
  have hp : (sourceMaps C).rlp (terminal.from X) := Packages.fibrant hC X
  letI := Packages.trivialCofibration_lift hC e he hwe hX (terminal.from X) hp
  have hs : CommSq (𝟙 X) e (terminal.from X) (terminal.from Z) :=
    ⟨terminal.hom_ext _ _⟩
  exact ⟨hs.lift, hs.fac_left⟩

private theorem trivialCofibration_relHomotopy {X Z : C.Model} (hC : C.IsCoherator)
    (e : X ⟶ Z)
    (he : (boundaryMaps C).rlp.llp e) (hwe : W hC e)
    (hX : ModelCofibrant C X) (hZ : ModelCofibrant C Z)
    (r : Z ⟶ X) (hr : e ≫ r = 𝟙 X) :
    ∃ (cyl : ModelRelativeCylinder hC e) (H : cyl.I ⟶ Z),
      cyl.j₀ ≫ cyl.c ≫ H = r ≫ e ∧ cyl.j₁ ≫ cyl.c ≫ H = 𝟙 Z := by
  letI : CategoryWithCofibrations C.Model := modelCofibrationData C
  letI : CategoryWithWeakEquivalences C.Model := modelWeakEquivalenceData hC
  letI : HasPushout e e := inferInstance
  let P := pushout e e
  let j₀ : Z ⟶ P := pushout.inl e e
  let j₁ : Z ⟶ P := pushout.inr e e
  let hP : IsPushout e e j₀ j₁ := IsPushout.of_hasPushout e e
  have hj₀ : W hC j₀ :=
    Cylinder.FiniteCellCategory.model_trivialCofibration_cobaseChange hC e e j₁ j₀ hP.flip he hwe hX hZ
  let fold : P ⟶ Z := hP.desc (𝟙 Z) (𝟙 Z) (by simp)
  have hid : W hC (𝟙 Z) :=
    (Packages.weakEquivalence_closure hC).1 (𝟙 Z) inferInstance
  have h₁ : W hC ((𝟙 Z) ≫ j₀) := by simpa using hj₀
  have h₂ : W hC (j₀ ≫ fold) := by rw [hP.inl_desc]; exact hid
  have hfold : W hC fold :=
    (Packages.weakEquivalence_twoOutOfSix hC (𝟙 Z) j₀ fold h₁ h₂).2.2.1
  let cyl : ModelRelativeCylinder hC e :=
    ⟨P, j₀, j₁, hP, P, 𝟙 P, fold,
      (MorphismProperty.llp_isMultiplicative (boundaryMaps C).rlp).toContainsIdentities.id_mem P,
      hfold,
      by simp [fold, hP.inl_desc],
      by simp [fold, hP.inr_desc]⟩
  have hcompat : e ≫ (r ≫ e) = e ≫ 𝟙 Z := by
    calc
      e ≫ (r ≫ e) = (e ≫ r) ≫ e := by simp [Category.assoc]
      _ = 𝟙 X ≫ e := by rw [hr]
      _ = e ≫ 𝟙 Z := by simp
  let H : P ⟶ Z := hP.desc (r ≫ e) (𝟙 Z) hcompat
  refine ⟨cyl, H, ?_, ?_⟩
  · simpa [cyl, H, Category.assoc] using hP.inl_desc (r ≫ e) (𝟙 Z) hcompat
  · simpa [cyl, H, Category.assoc] using hP.inr_desc (r ≫ e) (𝟙 Z) hcompat

private theorem modelExactLift {A B X Y : C.Model} (hC : C.IsCoherator)
    (i : A ⟶ B) (f : X ⟶ Y) (a : A ⟶ X) (b : B ⟶ Y)
    (hi : (boundaryMaps C).rlp.llp i) (hf : W hC f)
    (hsq : a ≫ f = i ≫ b) (hX : ModelCofibrant C X) :
    ∃ l : B ⟶ X, i ≫ l = a := by
  letI : HasPushout i a := inferInstance
  let P := pushout i a
  let k : B ⟶ P := pushout.inl i a
  let j : X ⟶ P := pushout.inr i a
  let hP : IsPushout i a k j := IsPushout.of_hasPushout i a
  let q : P ⟶ Y := hP.desc b f hsq.symm
  obtain ⟨Z, c, w, hc, hwp, hcw⟩ := factorByBoundary hC q
  have hj : (boundaryMaps C).rlp.llp j :=
    (MorphismProperty.llp_isStableUnderCobaseChange (boundaryMaps C).rlp).of_isPushout
      hP.flip hi
  have he : (boundaryMaps C).rlp.llp (j ≫ c) :=
    (MorphismProperty.llp_isMultiplicative (boundaryMaps C).rlp).comp_mem _ _ hj hc
  have hcomp : (j ≫ c) ≫ w = f := by
    calc
      (j ≫ c) ≫ w = j ≫ (c ≫ w) := by simp [Category.assoc]
      _ = j ≫ q := by rw [hcw]
      _ = f := hP.inr_desc b f hsq.symm
  have hw : W hC w := (boundaryRlp_weakEquivalence hC w hwp).1
  have hcompW : W hC ((j ≫ c) ≫ w) := by rw [hcomp]; exact hf
  have hwid : W hC (w ≫ 𝟙 Y) := by simpa using hw
  have heW : W hC (j ≫ c) :=
    (Packages.weakEquivalence_twoOutOfSix hC (j ≫ c) w (𝟙 Y) hcompW hwid).1
  obtain ⟨r, hr⟩ := trivialCofibration_retraction hC (j ≫ c) he heW hX
  refine ⟨k ≫ c ≫ r, ?_⟩
  calc
    i ≫ (k ≫ c ≫ r) = (i ≫ k) ≫ c ≫ r := by simp [Category.assoc]
    _ = (a ≫ j) ≫ c ≫ r := by rw [hP.w]
    _ = a ≫ ((j ≫ c) ≫ r) := by simp [Category.assoc]
    _ = a := by rw [hr]; simp

private theorem afinObject_modelCofibrant (hC : C.IsCoherator) (A : Afin C hC) :
    ModelCofibrant C ((Afin.ι hC).obj A) := by
  change (boundaryMaps C).rlp.llp (initial.to ((Afin.ι hC).obj A))
  exact Cylinder.FiniteCellCategory.finiteCellMaps_le_cofibrations C (initial.to A.obj) A.property

private def modelCylinderOfAfin (hC : C.IsCoherator)
    {A B : Afin C hC} (i : A ⟶ B) (hi : cofibrations (Afin C hC) i)
    (cyl : RelativeCylinder i) :
    ModelRelativeCylinder hC ((Afin.ι hC).map i) := by
  let F := Afin.ι hC
  refine ⟨F.obj cyl.P, F.map cyl.j₀, F.map cyl.j₁,
    Packages.afin_ι_map_isPushout hC i i cyl.j₀ cyl.j₁ cyl.isPushout hi,
    F.obj cyl.I, F.map cyl.c, F.map cyl.p, ?_, ?_, ?_, ?_⟩
  · change (boundaryMaps C).rlp.llp (F.map cyl.c)
    apply Cylinder.FiniteCellCategory.finiteCellMaps_le_cofibrations C
    exact cyl.c_mem
  · change W hC (F.map cyl.p)
    exact cyl.p_mem
  · calc
      F.map cyl.j₀ ≫ F.map cyl.c ≫ F.map cyl.p = F.map (cyl.j₀ ≫ cyl.c ≫ cyl.p) := by
        simp only [← Functor.map_comp]
      _ = F.map (𝟙 B) := congrArg F.map cyl.j₀_c_p
      _ = 𝟙 (F.obj B) := F.map_id _
  · calc
      F.map cyl.j₁ ≫ F.map cyl.c ≫ F.map cyl.p = F.map (cyl.j₁ ≫ cyl.c ≫ cyl.p) := by
        simp only [← Functor.map_comp]
      _ = F.map (𝟙 B) := congrArg F.map cyl.j₁_c_p
      _ = 𝟙 (F.obj B) := F.map_id _

private theorem modelRelativeCylinder_I_cofibrant {hC : C.IsCoherator}
    {A B : C.Model} {i : A ⟶ B} (cyl : ModelRelativeCylinder hC i)
    (hP : ModelCofibrant C cyl.P) : ModelCofibrant C cyl.I := by
  change (boundaryMaps C).rlp.llp (initial.to cyl.I)
  have heq : initial.to cyl.I = initial.to cyl.P ≫ cyl.c := by
    apply initial.hom_ext
  rw [heq]
  exact (MorphismProperty.llp_isMultiplicative (boundaryMaps C).rlp).comp_mem
    _ _ hP cyl.c_mem

private theorem modelWeakEquivalenceHomotopyLift {A B X Y : C.Model}
    (hC : C.IsCoherator) (i : A ⟶ B) (f : X ⟶ Y)
    (a : A ⟶ X) (b : B ⟶ Y) (cyl : ModelRelativeCylinder hC i)
    (hi : (boundaryMaps C).rlp.llp i) (hf : W hC f)
    (hsq : a ≫ f = i ≫ b) (hX : ModelCofibrant C X)
    (hP : ModelCofibrant C cyl.P) :
    ∃ l : B ⟶ X, i ≫ l = a ∧
      ∃ H : cyl.I ⟶ Y,
        cyl.j₀ ≫ cyl.c ≫ H = l ≫ f ∧ cyl.j₁ ≫ cyl.c ≫ H = b := by
  letI : CategoryWithCofibrations C.Model := modelCofibrationData C
  letI : CategoryWithWeakEquivalences C.Model := modelWeakEquivalenceData hC
  let _ : HasPushout i a := inferInstance
  let P := pushout i a
  let k : B ⟶ P := pushout.inl i a
  let j : X ⟶ P := pushout.inr i a
  let hPq : IsPushout i a k j := IsPushout.of_hasPushout i a
  let q : P ⟶ Y := hPq.desc b f hsq.symm
  obtain ⟨Z, c, w, hc, hwp, hcw⟩ := factorByBoundary hC q
  have hj : (boundaryMaps C).rlp.llp j :=
    (MorphismProperty.llp_isStableUnderCobaseChange (boundaryMaps C).rlp).of_isPushout
      hPq.flip hi
  have he : (boundaryMaps C).rlp.llp (j ≫ c) :=
    (MorphismProperty.llp_isMultiplicative (boundaryMaps C).rlp).comp_mem _ _ hj hc
  have hcomp : (j ≫ c) ≫ w = f := by
    calc
      (j ≫ c) ≫ w = j ≫ (c ≫ w) := by simp [Category.assoc]
      _ = j ≫ q := by rw [hcw]
      _ = f := hPq.inr_desc b f hsq.symm
  have hw : W hC w := (boundaryRlp_weakEquivalence hC w hwp).1
  have hcompW : W hC ((j ≫ c) ≫ w) := by rw [hcomp]; exact hf
  have hwid : W hC (w ≫ 𝟙 Y) := by simpa using hw
  have heW : W hC (j ≫ c) :=
    (Packages.weakEquivalence_twoOutOfSix hC (j ≫ c) w (𝟙 Y) hcompW hwid).1
  obtain ⟨r, hr⟩ := trivialCofibration_retraction hC (j ≫ c) he heW hX
  have hZ : ModelCofibrant C Z := by
    change (boundaryMaps C).rlp.llp (initial.to Z)
    have heq : initial.to Z = initial.to X ≫ (j ≫ c) := by
      apply initial.hom_ext
    rw [heq]
    exact (MorphismProperty.llp_isMultiplicative (boundaryMaps C).rlp).comp_mem
      _ _ hX he
  obtain ⟨cylE, HE, hE₀, hE₁⟩ :=
    trivialCofibration_relHomotopy hC (j ≫ c) he heW hX hZ r hr
  have hE_P : ModelCofibrant C cylE.P := by
    change (boundaryMaps C).rlp.llp (initial.to cylE.P)
    have hjE : (boundaryMaps C).rlp.llp cylE.j₀ :=
      (MorphismProperty.llp_isStableUnderCobaseChange (boundaryMaps C).rlp).of_isPushout
        cylE.isPushout he
    have heq : initial.to cylE.P = initial.to Z ≫ cylE.j₀ := by
      apply initial.hom_ext
    rw [heq]
    exact (MorphismProperty.llp_isMultiplicative (boundaryMaps C).rlp).comp_mem
      _ _ hZ hjE
  have hE_I : ModelCofibrant C cylE.I :=
    modelRelativeCylinder_I_cofibrant cylE hE_P
  let u : B ⟶ Z := k ≫ c
  have hsqE : a ≫ (j ≫ c) = i ≫ u := by
    calc
      a ≫ (j ≫ c) = (a ≫ j) ≫ c := by simp [Category.assoc]
      _ = (i ≫ k) ≫ c := by rw [hPq.w]
      _ = i ≫ u := by simp [u, Category.assoc]
  have hcomm : i ≫ (u ≫ cylE.j₀) = i ≫ (u ≫ cylE.j₁) := by
    calc
      i ≫ (u ≫ cylE.j₀) = (i ≫ u) ≫ cylE.j₀ := by simp [Category.assoc]
      _ = (a ≫ (j ≫ c)) ≫ cylE.j₀ := by rw [← hsqE]
      _ = a ≫ ((j ≫ c) ≫ cylE.j₀) := by simp [Category.assoc]
      _ = a ≫ ((j ≫ c) ≫ cylE.j₁) := by rw [cylE.isPushout.w]
      _ = (a ≫ (j ≫ c)) ≫ cylE.j₁ := by simp [Category.assoc]
      _ = (i ≫ u) ≫ cylE.j₁ := by rw [hsqE]
      _ = i ≫ (u ≫ cylE.j₁) := by simp [Category.assoc]
  let φP : cyl.P ⟶ cylE.P :=
    cyl.isPushout.desc (u ≫ cylE.j₀) (u ≫ cylE.j₁) hcomm
  have hφ₀ : cyl.j₀ ≫ φP = u ≫ cylE.j₀ :=
    cyl.isPushout.inl_desc _ _ hcomm
  have hφ₁ : cyl.j₁ ≫ φP = u ≫ cylE.j₁ :=
    cyl.isPushout.inr_desc _ _ hcomm
  have hsqLift : cyl.c ≫ (cyl.p ≫ u) = (φP ≫ cylE.c) ≫ cylE.p := by
    apply cyl.isPushout.hom_ext
    · calc
        cyl.j₀ ≫ cyl.c ≫ (cyl.p ≫ u) = (cyl.j₀ ≫ cyl.c ≫ cyl.p) ≫ u := by
          cat_disch
        _ = (𝟙 B) ≫ u := by rw [cyl.j₀_c_p]
        _ = u := by simp
        _ = u ≫ (cylE.j₀ ≫ cylE.c ≫ cylE.p) := by rw [cylE.j₀_c_p]; simp
        _ = (u ≫ cylE.j₀) ≫ cylE.c ≫ cylE.p := by cat_disch
        _ = (cyl.j₀ ≫ φP) ≫ cylE.c ≫ cylE.p := by rw [hφ₀]
        _ = cyl.j₀ ≫ (φP ≫ cylE.c) ≫ cylE.p := by cat_disch
    · calc
        cyl.j₁ ≫ cyl.c ≫ (cyl.p ≫ u) = (cyl.j₁ ≫ cyl.c ≫ cyl.p) ≫ u := by
          cat_disch
        _ = (𝟙 B) ≫ u := by rw [cyl.j₁_c_p]
        _ = u := by simp
        _ = u ≫ (cylE.j₁ ≫ cylE.c ≫ cylE.p) := by rw [cylE.j₁_c_p]; simp
        _ = (u ≫ cylE.j₁) ≫ cylE.c ≫ cylE.p := by cat_disch
        _ = (cyl.j₁ ≫ φP) ≫ cylE.c ≫ cylE.p := by rw [hφ₁]
        _ = cyl.j₁ ≫ (φP ≫ cylE.c) ≫ cylE.p := by cat_disch
  obtain ⟨t, ht⟩ := modelExactLift hC cyl.c cylE.p (φP ≫ cylE.c) (cyl.p ≫ u)
    cyl.c_mem cylE.p_mem hsqLift.symm hE_I
  let l : B ⟶ X := u ≫ r
  have hl : i ≫ l = a := by
    calc
      i ≫ l = (i ≫ u) ≫ r := by simp [l, Category.assoc]
      _ = (a ≫ (j ≫ c)) ≫ r := by rw [← hsqE]
      _ = a ≫ ((j ≫ c) ≫ r) := by simp [Category.assoc]
      _ = a := by rw [hr]; simp
  have heWcomp : (j ≫ c) ≫ w = f := hcomp
  have h₀pre : cyl.j₀ ≫ cyl.c ≫ t ≫ HE = u ≫ r ≫ j ≫ c := by
    calc
      cyl.j₀ ≫ cyl.c ≫ t ≫ HE = cyl.j₀ ≫ (cyl.c ≫ t) ≫ HE := by cat_disch
      _ = cyl.j₀ ≫ (φP ≫ cylE.c) ≫ HE := by rw [ht]
      _ = (cyl.j₀ ≫ φP) ≫ cylE.c ≫ HE := by cat_disch
      _ = (u ≫ cylE.j₀) ≫ cylE.c ≫ HE := by rw [hφ₀]
      _ = u ≫ (cylE.j₀ ≫ cylE.c ≫ HE) := by cat_disch
      _ = u ≫ (r ≫ j ≫ c) := by rw [hE₀]
  have h₁pre : cyl.j₁ ≫ cyl.c ≫ t ≫ HE = u := by
    calc
      cyl.j₁ ≫ cyl.c ≫ t ≫ HE = cyl.j₁ ≫ (cyl.c ≫ t) ≫ HE := by cat_disch
      _ = cyl.j₁ ≫ (φP ≫ cylE.c) ≫ HE := by rw [ht]
      _ = (cyl.j₁ ≫ φP) ≫ cylE.c ≫ HE := by cat_disch
      _ = (u ≫ cylE.j₁) ≫ cylE.c ≫ HE := by rw [hφ₁]
      _ = u ≫ (cylE.j₁ ≫ cylE.c ≫ HE) := by cat_disch
      _ = u := by rw [hE₁]; simp
  refine ⟨l, hl, t ≫ HE ≫ w, ?_, ?_⟩
  · calc
      cyl.j₀ ≫ cyl.c ≫ (t ≫ HE ≫ w) = (cyl.j₀ ≫ cyl.c ≫ t ≫ HE) ≫ w := by cat_disch
      _ = (u ≫ r ≫ j ≫ c) ≫ w := by rw [h₀pre]
      _ = (u ≫ r) ≫ ((j ≫ c) ≫ w) := by cat_disch
      _ = l ≫ f := by rw [heWcomp]
  · calc
      cyl.j₁ ≫ cyl.c ≫ (t ≫ HE ≫ w) = (cyl.j₁ ≫ cyl.c ≫ t ≫ HE) ≫ w := by cat_disch
      _ = u ≫ w := by rw [h₁pre]
      _ = (k ≫ c) ≫ w := rfl
      _ = k ≫ (c ≫ w) := by cat_disch
      _ = k ≫ q := by rw [hcw]
      _ = b := hPq.inl_desc b f hsq.symm

private theorem cylinderPushout_reassociate
    {D : Type u} [Category D] [CategoryWithCofibrations D]
    {O X Y P I Q M : D} {iX : O ⟶ X} {iY : O ⟶ Y}
    (hO : IsInitial O) {j₀ j₁ : X ⟶ P} (hP : IsPushout iX iX j₀ j₁)
    {qX : X ⟶ Q} {qY : Y ⟶ Q} (hQ : IsPushout iX iY qX qY)
    {c : P ⟶ I} {f : X ⟶ Y} {d : P ⟶ Q}
    (hd₀ : j₀ ≫ d = qX) (hd₁ : j₁ ≫ d = f ≫ qY)
    {mI : I ⟶ M} {mQ : Q ⟶ M} (hM : IsPushout c d mI mQ) :
    IsPushout (j₁ ≫ c) f mI (qY ≫ mQ) := by
  have hcomm : (j₁ ≫ c) ≫ mI = f ≫ (qY ≫ mQ) := by
    calc
      (j₁ ≫ c) ≫ mI = j₁ ≫ (c ≫ mI) := by simp [Category.assoc]
      _ = j₁ ≫ (d ≫ mQ) := by rw [hM.w]
      _ = (f ≫ qY) ≫ mQ := by rw [← Category.assoc, hd₁]
      _ = f ≫ (qY ≫ mQ) := by simp [Category.assoc]
  let desc : (s : PushoutCocone (j₁ ≫ c) f) → M ⟶ s.pt := fun s => by
    have hqcomm : iX ≫ (j₀ ≫ c ≫ s.inl) = iY ≫ s.inr := hO.hom_ext _ _
    let q : Q ⟶ s.pt := hQ.desc (j₀ ≫ c ≫ s.inl) s.inr hqcomm
    refine hM.desc s.inl q ?_
    apply hP.hom_ext
    · calc
        j₀ ≫ c ≫ s.inl = qX ≫ q :=
          (hQ.inl_desc (j₀ ≫ c ≫ s.inl) s.inr hqcomm).symm
        _ = (j₀ ≫ d) ≫ q := by rw [← hd₀]
        _ = j₀ ≫ d ≫ q := by simp [Category.assoc]
    · calc
        j₁ ≫ c ≫ s.inl = f ≫ s.inr := by simpa [Category.assoc] using s.condition
        _ = f ≫ qY ≫ q := by rw [← hQ.inr_desc (j₀ ≫ c ≫ s.inl) s.inr hqcomm]
        _ = (f ≫ qY) ≫ q := by simp [Category.assoc]
        _ = (j₁ ≫ d) ≫ q := by rw [← hd₁]
        _ = j₁ ≫ d ≫ q := by simp [Category.assoc]
  have facL (s : PushoutCocone (j₁ ≫ c) f) : mI ≫ desc s = s.inl := by simp [desc]
  have facR (s : PushoutCocone (j₁ ≫ c) f) : (qY ≫ mQ) ≫ desc s = s.inr := by
    simp [desc, Category.assoc]
  have uniq (s : PushoutCocone (j₁ ≫ c) f) (m : M ⟶ s.pt)
      (hmI : mI ≫ m = s.inl) (hmY : (qY ≫ mQ) ≫ m = s.inr) : m = desc s := by
    have hqcomm : iX ≫ (j₀ ≫ c ≫ s.inl) = iY ≫ s.inr := hO.hom_ext _ _
    let q : Q ⟶ s.pt := hQ.desc (j₀ ≫ c ≫ s.inl) s.inr hqcomm
    have hmq : mQ ≫ m = q := by
      apply hQ.hom_ext
      · calc
          qX ≫ mQ ≫ m = (j₀ ≫ d) ≫ mQ ≫ m := by rw [← hd₀]
          _ = j₀ ≫ (c ≫ mI) ≫ m := by simp [Category.assoc, hM.w]
          _ = j₀ ≫ c ≫ (mI ≫ m) := by simp [Category.assoc]
          _ = j₀ ≫ c ≫ s.inl := by rw [hmI]
          _ = qX ≫ q := (hQ.inl_desc (j₀ ≫ c ≫ s.inl) s.inr hqcomm).symm
      · calc
          qY ≫ mQ ≫ m = (qY ≫ mQ) ≫ m := by simp [Category.assoc]
          _ = s.inr := hmY
          _ = qY ≫ q := (hQ.inr_desc (j₀ ≫ c ≫ s.inl) s.inr hqcomm).symm
    apply hM.hom_ext
    · exact hmI.trans (facL s).symm
    · exact hmq.trans (hM.inr_desc s.inl q (by
        apply hP.hom_ext
        · calc
            j₀ ≫ c ≫ s.inl = qX ≫ q :=
              (hQ.inl_desc (j₀ ≫ c ≫ s.inl) s.inr hqcomm).symm
            _ = (j₀ ≫ d) ≫ q := by rw [← hd₀]
            _ = j₀ ≫ d ≫ q := by simp [Category.assoc]
        · calc
            j₁ ≫ c ≫ s.inl = f ≫ s.inr := by simpa [Category.assoc] using s.condition
            _ = f ≫ qY ≫ q := by rw [← hQ.inr_desc (j₀ ≫ c ≫ s.inl) s.inr hqcomm]
            _ = (f ≫ qY) ≫ q := by simp [Category.assoc]
            _ = (j₁ ≫ d) ≫ q := by rw [← hd₁]
            _ = j₁ ≫ d ≫ q := by simp [Category.assoc])).symm
  exact IsPushout.of_isColimit (PushoutCocone.IsColimit.mk hcomm desc facL facR uniq)

private theorem cylinderFactorization
    {D : Type u} [Category D] [CategoryWithCofibrations D]
    [CategoryWithWeakEquivalences D] [IsCylinderCategory D]
    {X Y : D} (f : X ⟶ Y) :
    ∃ (Z : D) (i : X ⟶ Z) (p : Z ⟶ Y),
      cofibrations D i ∧ weakEquivalences D p ∧ i ≫ p = f := by
  obtain ⟨O, hO₀⟩ := IsCofibrationCategory.exists_initial (C := D)
  obtain ⟨hO⟩ := hO₀
  have hcofO_X : cofibrations D (hO.to X) :=
    IsCofibrationCategory.initial_cofibration (C := D) hO X
  have hcofO_Y : cofibrations D (hO.to Y) :=
    IsCofibrationCategory.initial_cofibration (C := D) hO Y
  obtain ⟨cyl⟩ := IsCylinderCategory.exists_cylinder (C := D) hO X
  have hcofJ₀ : cofibrations D cyl.j₀ :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := D)).of_isPushout
      cyl.isPushout hcofO_X
  have hcofJ₁ : cofibrations D cyl.j₁ :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := D)).of_isPushout
      cyl.isPushout.flip hcofO_X
  have hcofJ₀c : cofibrations D (cyl.j₀ ≫ cyl.c) :=
    (IsCofibrationCategory.isMultiplicative (C := D)).comp_mem _ _ hcofJ₀ cyl.c_mem
  have hcofJ₁c : cofibrations D (cyl.j₁ ≫ cyl.c) :=
    (IsCofibrationCategory.isMultiplicative (C := D)).comp_mem _ _ hcofJ₁ cyl.c_mem
  have hidX : weakEquivalences D (𝟙 X) :=
    IsCylinderCategory.weakEquivalences_isMultiplicative.toContainsIdentities.id_mem X
  have hidY : weakEquivalences D (𝟙 Y) :=
    IsCylinderCategory.weakEquivalences_isMultiplicative.toContainsIdentities.id_mem Y
  have hj₁cp : (cyl.j₁ ≫ cyl.c) ≫ cyl.p = 𝟙 X := by
    simpa [Category.assoc] using cyl.j₁_c_p
  have hJ₁cW : weakEquivalences D (cyl.j₁ ≫ cyl.c) := by
    have h₁ : weakEquivalences D ((cyl.j₁ ≫ cyl.c) ≫ cyl.p) := by rw [hj₁cp]; exact hidX
    have h₂ : weakEquivalences D (cyl.p ≫ 𝟙 X) := by simpa using cyl.p_mem
    exact (IsCylinderCategory.twoOutOfSix (C := D) (cyl.j₁ ≫ cyl.c) cyl.p (𝟙 X) h₁ h₂).1
  letI : HasPushout (hO.to X) (hO.to Y) :=
    IsCofibrationCategory.hasPushout (C := D) (hO.to X) (hO.to Y) hcofO_X
  let Q := pushout (hO.to X) (hO.to Y)
  let qX : X ⟶ Q := pushout.inl (hO.to X) (hO.to Y)
  let qY : Y ⟶ Q := pushout.inr (hO.to X) (hO.to Y)
  let hQ : IsPushout (hO.to X) (hO.to Y) qX qY := IsPushout.of_hasPushout _ _
  let d : cyl.P ⟶ Q := cyl.isPushout.desc qX (f ≫ qY) (hO.hom_ext _ _)
  have hd₀ : cyl.j₀ ≫ d = qX := by simp [d]
  have hd₁ : cyl.j₁ ≫ d = f ≫ qY := by simp [d]
  letI : HasPushout cyl.c d :=
    IsCofibrationCategory.hasPushout (C := D) cyl.c d cyl.c_mem
  let M := pushout cyl.c d
  let mI : cyl.I ⟶ M := pushout.inl cyl.c d
  let mQ : Q ⟶ M := pushout.inr cyl.c d
  have hM : IsPushout cyl.c d mI mQ := IsPushout.of_hasPushout _ _
  have hY : IsPushout (cyl.j₁ ≫ cyl.c) f mI (qY ≫ mQ) :=
    cylinderPushout_reassociate hO cyl.isPushout hQ hd₀ hd₁ hM
  have hcofQX : cofibrations D qX :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := D)).of_isPushout hQ hcofO_Y
  have hcofMQ : cofibrations D mQ :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := D)).of_isPushout hM.flip cyl.c_mem
  have hcofI : cofibrations D (qX ≫ mQ) :=
    (IsCofibrationCategory.isMultiplicative (C := D)).comp_mem _ _ hcofQX hcofMQ
  have hWEqY : weakEquivalences D (qY ≫ mQ) :=
    IsCylinderCategory.trivialCofibration_cobaseChange
      (cyl.j₁ ≫ cyl.c) f mI (qY ≫ mQ) hY hcofJ₁c hJ₁cW
  have hqQcomm : (hO.to X) ≫ f = (hO.to Y) ≫ (𝟙 Y) := hO.hom_ext _ _
  let qQ : Q ⟶ Y := hQ.desc f (𝟙 Y) hqQcomm
  have hj₀cp : (cyl.j₀ ≫ cyl.c) ≫ cyl.p = 𝟙 X := by
    simpa [Category.assoc] using cyl.j₀_c_p
  have hcompat : cyl.c ≫ (cyl.p ≫ f) = d ≫ qQ := by
    apply cyl.isPushout.hom_ext
    · calc
        cyl.j₀ ≫ cyl.c ≫ (cyl.p ≫ f) = ((cyl.j₀ ≫ cyl.c) ≫ cyl.p) ≫ f := by
          simp [Category.assoc]
        _ = f := by rw [hj₀cp]; simp
        _ = qX ≫ qQ := (hQ.inl_desc f (𝟙 Y) hqQcomm).symm
        _ = (cyl.j₀ ≫ d) ≫ qQ := by rw [← hd₀]
        _ = cyl.j₀ ≫ d ≫ qQ := by simp [Category.assoc]
    · calc
        cyl.j₁ ≫ cyl.c ≫ (cyl.p ≫ f) = ((cyl.j₁ ≫ cyl.c) ≫ cyl.p) ≫ f := by
          simp [Category.assoc]
        _ = f := by rw [hj₁cp]; simp
        _ = f ≫ (qY ≫ qQ) := by rw [hQ.inr_desc f (𝟙 Y) hqQcomm]; simp
        _ = (f ≫ qY) ≫ qQ := by simp [Category.assoc]
        _ = (cyl.j₁ ≫ d) ≫ qQ := by rw [← hd₁]
        _ = cyl.j₁ ≫ d ≫ qQ := by simp [Category.assoc]
  let qM : M ⟶ Y := hM.desc (cyl.p ≫ f) qQ hcompat
  have hsplit : (qY ≫ mQ) ≫ qM = 𝟙 Y := by
    calc
      (qY ≫ mQ) ≫ qM = qY ≫ (mQ ≫ qM) := by simp [Category.assoc]
      _ = qY ≫ qQ := congrArg (fun g => qY ≫ g) (hM.inr_desc (cyl.p ≫ f) qQ hcompat)
      _ = 𝟙 Y := hQ.inr_desc f (𝟙 Y) hqQcomm
  have hqM : weakEquivalences D qM := by
    have h₁ : weakEquivalences D ((𝟙 Y) ≫ (qY ≫ mQ)) := by simpa using hWEqY
    have h₂ : weakEquivalences D ((qY ≫ mQ) ≫ qM) := by rw [hsplit]; exact hidY
    exact (IsCylinderCategory.twoOutOfSix (C := D) (𝟙 Y) (qY ≫ mQ) qM h₁ h₂).2.2.1
  refine ⟨M, qX ≫ mQ, qM, hcofI, hqM, ?_⟩
  calc
    (qX ≫ mQ) ≫ qM = qX ≫ (mQ ≫ qM) := by simp [Category.assoc]
    _ = qX ≫ qQ := congrArg (fun g => qX ≫ g) (hM.inr_desc (cyl.p ≫ f) qQ hcompat)
    _ = f := hQ.inl_desc f (𝟙 Y) hqQcomm

private theorem relativeCylinderOfCofibration
    {D : Type u} [Category.{v} D] [CategoryWithCofibrations D]
    [CategoryWithWeakEquivalences D] [IsCylinderCategory D]
    {A B : D} (i : A ⟶ B) (hi : cofibrations D i) : Nonempty (RelativeCylinder i) := by
  letI : HasPushout i i := IsCofibrationCategory.hasPushout (C := D) i i hi
  let P := pushout i i
  let j₀ : B ⟶ P := pushout.inl i i
  let j₁ : B ⟶ P := pushout.inr i i
  let hP : IsPushout i i j₀ j₁ := IsPushout.of_hasPushout i i
  let fold : P ⟶ B := hP.desc (𝟙 B) (𝟙 B) (by simp)
  obtain ⟨I, c, p, hc, hp, hcp⟩ := cylinderFactorization fold
  refine ⟨⟨P, j₀, j₁, hP, I, c, p, hc, hp, ?_, ?_⟩⟩
  · calc
      j₀ ≫ c ≫ p = j₀ ≫ (c ≫ p) := by simp [Category.assoc]
      _ = j₀ ≫ fold := by rw [hcp]
      _ = 𝟙 B := hP.inl_desc (𝟙 B) (𝟙 B) (by simp)
  · calc
      j₁ ≫ c ≫ p = j₁ ≫ (c ≫ p) := by simp [Category.assoc]
      _ = j₁ ≫ fold := by rw [hcp]
      _ = 𝟙 B := hP.inr_desc (𝟙 B) (𝟙 B) (by simp)

private theorem cylinderCategory_exactLift
    {D : Type u} [Category.{v} D] [CategoryWithCofibrations D]
    [CategoryWithWeakEquivalences D] [IsCylinderCategory D]
    {A B X Y : D} (i : A ⟶ B) (f : X ⟶ Y) (a : A ⟶ X) (b : B ⟶ Y)
    (hi : cofibrations D i) (hf : weakEquivalences D f) (hsq : a ≫ f = i ≫ b) :
    ∃ l : B ⟶ X, i ≫ l = a := by
  letI : HasPushout i a := IsCofibrationCategory.hasPushout (C := D) i a hi
  let P := pushout i a
  let k : B ⟶ P := pushout.inl i a
  let j : X ⟶ P := pushout.inr i a
  let hP : IsPushout i a k j := IsPushout.of_hasPushout i a
  let q : P ⟶ Y := hP.desc b f hsq.symm
  obtain ⟨Z, c, w, hc, hw, hcw⟩ := cylinderFactorization q
  have hj : cofibrations D j :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := D)).of_isPushout hP.flip hi
  have he : cofibrations D (j ≫ c) :=
    (IsCofibrationCategory.isMultiplicative (C := D)).comp_mem _ _ hj hc
  have hcomp : (j ≫ c) ≫ w = f := by
    calc
      (j ≫ c) ≫ w = j ≫ (c ≫ w) := by simp [Category.assoc]
      _ = j ≫ q := by rw [hcw]
      _ = f := hP.inr_desc b f hsq.symm
  have hcompW : weakEquivalences D ((j ≫ c) ≫ w) := by rw [hcomp]; exact hf
  have hwid : weakEquivalences D (w ≫ 𝟙 Y) := by simpa using hw
  have heW : weakEquivalences D (j ≫ c) :=
    (IsCylinderCategory.twoOutOfSix (C := D) (j ≫ c) w (𝟙 Y) hcompW hwid).1
  obtain ⟨r, hr⟩ := IsCylinderCategory.exists_retraction (C := D) (j ≫ c) he heW
  refine ⟨k ≫ c ≫ r, ?_⟩
  calc
    i ≫ (k ≫ c ≫ r) = (i ≫ k) ≫ c ≫ r := by simp [Category.assoc]
    _ = (a ≫ j) ≫ c ≫ r := by rw [hP.w]
    _ = a ≫ ((j ≫ c) ≫ r) := by simp [Category.assoc]
    _ = a := by rw [hr]; simp

private theorem completionWeakEquivalence_of_W {C : GlobularTheory.{u}}
    (hC : C.IsCoherator) {X Y : C.Model} (f : X ⟶ Y) (hf : W hC f) :
    Completion.weakEquivalences (Afin C hC) ((Packages.restriction hC).map f) := by
  change presheafWeakEquivalences ((Packages.restriction hC).map f).hom
  intro A B i hi a b hab
  let F := Afin.ι hC
  change (F.obj A ⟶ X) at a
  change (F.obj B ⟶ Y) at b
  have hab' : a ≫ f = F.map i ≫ b := by
    change a ≫ f = F.map i ≫ b at hab
    exact hab
  obtain ⟨Xc, q, p, hq, hp, hfac⟩ := factorByBoundary hC (initial.to X)
  have hXc : ModelCofibrant C Xc := by
    change (boundaryMaps C).rlp.llp (initial.to Xc)
    have hqeq : q = initial.to Xc := initial.hom_ext _ _
    rw [← hqeq]
    exact hq
  have hpW : W hC p := (boundaryRlp_weakEquivalence hC p hp).1
  have hpf : W hC (p ≫ f) :=
    (Packages.weakEquivalence_closure hC).2.comp_mem _ _ hpW hf
  have hA : ModelCofibrant C (F.obj A) := afinObject_modelCofibrant hC A
  let _ := hA p hp
  have hs : CommSq (initial.to Xc) (initial.to (F.obj A)) p a := by
    exact ⟨initial.hom_ext _ _⟩
  let a' := hs.lift
  have ha'p : a' ≫ p = a := hs.fac_right
  have hsq' : a' ≫ (p ≫ f) = F.map i ≫ b := by
    calc
      a' ≫ (p ≫ f) = (a' ≫ p) ≫ f := by simp [Category.assoc]
      _ = a ≫ f := by rw [ha'p]
      _ = F.map i ≫ b := hab'
  letI : IsCylinderCategory (Afin C hC) := Packages.afin_isCylinderCategory hC
  obtain ⟨cylA⟩ := relativeCylinderOfCofibration i hi
  let cylM := modelCylinderOfAfin hC i hi cylA
  have hiM : (boundaryMaps C).rlp.llp (F.map i) :=
    Cylinder.FiniteCellCategory.finiteCellMaps_le_cofibrations C (F.map i) hi
  have hP : ModelCofibrant C cylM.P := afinObject_modelCofibrant hC cylA.P
  obtain ⟨l', hl', H, h₀, h₁⟩ :=
    modelWeakEquivalenceHomotopyLift hC (F.map i) (p ≫ f) a' b cylM hiM hpf hsq' hXc hP
  let l : F.obj B ⟶ X := l' ≫ p
  have hl : F.map i ≫ l = a := by
    calc
      F.map i ≫ l = (F.map i ≫ l') ≫ p := by simp [l, Category.assoc]
      _ = a' ≫ p := by rw [hl']
      _ = a := ha'p
  refine ⟨l, cylA, H, ?_, ?_, ?_⟩
  · change F.map i ≫ l = a
    exact hl
  · change F.map (cylA.j₀ ≫ cylA.c) ≫ H = l ≫ f
    calc
      F.map (cylA.j₀ ≫ cylA.c) ≫ H =
          F.map cylA.j₀ ≫ F.map cylA.c ≫ H := by simp only [Functor.map_comp]; cat_disch
      _ = l' ≫ (p ≫ f) := h₀
      _ = l ≫ f := by simp [l, Category.assoc]
  · change F.map (cylA.j₁ ≫ cylA.c) ≫ H = b
    calc
      F.map (cylA.j₁ ≫ cylA.c) ≫ H =
          F.map cylA.j₁ ≫ F.map cylA.c ≫ H := by simp only [Functor.map_comp]; cat_disch
      _ = b := h₁

private theorem boundaryDisk_finitelyCellular {C : GlobularTheory.{u}} (n : ℕ) :
    IsFinitelyCellular C (boundaryDisk C n) := by
  cases n with
  | zero =>
      simpa [boundaryDisk, boundaryRepresentation, BoundaryRepresentation.zero] using
        Cylinder.FiniteCellCategory.initial_finitelyCellular C
  | succ n =>
      let i := I C n
      letI : HasPushout i i := inferInstance
      have hpo : IsPushout i i (pushout.inl i i) (pushout.inr i i) :=
        IsPushout.of_hasPushout i i
      have hinl : finiteCellMaps C (pushout.inl i i) :=
        (finiteCellMaps C).of_isPushout hpo (Cylinder.FiniteCellCategory.finiteCellMaps_I (C := C) n)
      have hcomp : finiteCellMaps C
          (initial.to (disk C n) ≫ pushout.inl i i) :=
        (finiteCellMaps C).comp_mem _ _ (Packages.disk_finitelyCellular C n) hinl
      have heq : initial.to (boundaryDisk C (n+1)) =
          initial.to (disk C n) ≫ pushout.inl i i := by
        apply initial.hom_ext
      change finiteCellMaps C (initial.to (boundaryDisk C (n+1)))
      rw [heq]
      exact hcomp

private noncomputable def unitRetraction (hC : C.IsCoherator) (n : ℕ) :
    disk C (n+1) ⟶ disk C n :=
  show (disk C (n+1)).presheaf ⟶ (disk C n).presheaf from
    yoneda.map (show (⟨Shape.globe (n+1)⟩ : C.Obj) ⟶ ⟨Shape.globe n⟩ from C.unit hC n)

private theorem source_unitRetraction (hC : C.IsCoherator) (n : ℕ) :
    J C n ≫ unitRetraction hC n = 𝟙 (disk C n) := by
  let S : C.Obj := ⟨Shape.globe n⟩
  let T : C.Obj := ⟨Shape.globe (n+1)⟩
  let s : S ⟶ T := C.base (Shape.source n)
  let u : T ⟶ S := C.unit hC n
  change yoneda.map s ≫ yoneda.map u = 𝟙 (disk C n)
  calc
    yoneda.map s ≫ yoneda.map u = yoneda.map (s ≫ u) :=
      (Functor.map_comp yoneda s u).symm
    _ = yoneda.map (𝟙 S) := by
      congr 1
      exact C.unit_source hC n
    _ = 𝟙 (yoneda.obj S) := yoneda.map_id _

private theorem target_unitRetraction (hC : C.IsCoherator) (n : ℕ) :
    targetDisk C n ≫ unitRetraction hC n = 𝟙 (disk C n) := by
  let S : C.Obj := ⟨Shape.globe n⟩
  let T : C.Obj := ⟨Shape.globe (n+1)⟩
  let t : S ⟶ T := C.base (Shape.target n)
  let u : T ⟶ S := C.unit hC n
  change yoneda.map t ≫ yoneda.map u = 𝟙 (disk C n)
  calc
    yoneda.map t ≫ yoneda.map u = yoneda.map (t ≫ u) :=
      (Functor.map_comp yoneda t u).symm
    _ = yoneda.map (𝟙 S) := by
      congr 1
      exact C.unit_target hC n
    _ = 𝟙 (yoneda.obj S) := yoneda.map_id _

private theorem unitRetraction_weakEquivalence (hC : C.IsCoherator) (n : ℕ) :
    W hC (unitRetraction hC n) := by
  have hJcof : (sourceMaps C).rlp.llp (J C n) :=
    (sourceMaps C).le_llp_rlp _ (MorphismProperty.ofHoms.mk n)
  have hDisk : ModelCofibrant C (disk C n) := by
    change (boundaryMaps C).rlp.llp (initial.to (disk C n))
    exact Cylinder.FiniteCellCategory.finiteCellMaps_le_cofibrations C _ (Packages.disk_finitelyCellular C n)
  have hJ : W hC (J C n) := Cylinder.FiniteCellCategory.source_llp_weakEquivalence hC (J C n) hJcof hDisk
  have hId : W hC (𝟙 (disk C n)) :=
    (Packages.weakEquivalence_closure hC).1 (𝟙 _) inferInstance
  have h₁ : W hC ((𝟙 (disk C n)) ≫ J C n) := by simpa using hJ
  have h₂ : W hC (J C n ≫ unitRetraction hC n) := by
    rw [source_unitRetraction]
    exact hId
  exact (Packages.weakEquivalence_twoOutOfSix hC (𝟙 (disk C n)) (J C n)
    (unitRetraction hC n) h₁ h₂).2.2.1

private abbrev afinBoundaryObj (hC : C.IsCoherator) (n : ℕ) : Afin C hC :=
  ⟨boundaryDisk C n, boundaryDisk_finitelyCellular n⟩

private abbrev afinDiskObj (hC : C.IsCoherator) (n : ℕ) : Afin C hC :=
  ⟨disk C n, Packages.disk_finitelyCellular C n⟩

private abbrev afinBoundaryIncl (hC : C.IsCoherator) (n : ℕ) :
    afinBoundaryObj hC n ⟶ afinDiskObj hC n :=
  ObjectProperty.homMk (I C n)

private theorem boundaryCylinder_to_arbitrary (hC : C.IsCoherator) (n : ℕ)
    (cyl : RelativeCylinder (afinBoundaryIncl hC n)) :
    ∃ t : afinDiskObj hC (n+1) ⟶ cyl.I,
      (ObjectProperty.homMk (J C n) : afinDiskObj hC n ⟶ afinDiskObj hC (n+1)) ≫ t =
        cyl.j₀ ≫ cyl.c ∧
      (ObjectProperty.homMk (targetDisk C n) : afinDiskObj hC n ⟶ afinDiskObj hC (n+1)) ≫ t =
        cyl.j₁ ≫ cyl.c := by
  letI : IsCylinderCategory (Afin C hC) := Packages.afin_isCylinderCategory hC
  let A := afinBoundaryObj hC n
  let D : Afin C hC := ⟨disk C n, Packages.disk_finitelyCellular C n⟩
  let B : Afin C hC := ⟨disk C (n+1), Packages.disk_finitelyCellular C (n+1)⟩
  let P := afinBoundaryObj hC (n+1)
  let i : A ⟶ D := afinBoundaryIncl hC n
  let F := Afin.ι hC
  let j₀Std : D ⟶ P := ObjectProperty.homMk (pushout.inl (I C n) (I C n))
  let j₁Std : D ⟶ P := ObjectProperty.homMk (pushout.inr (I C n) (I C n))
  have hi : cofibrations (Afin C hC) i := by
    change finiteCellMaps C (F.map i)
    exact Cylinder.FiniteCellCategory.finiteCellMaps_I (C := C) n
  have hStd : IsPushout i i j₀Std j₁Std :=
    IsPushout.of_map_of_faithful (Afin.ι hC)
      (IsPushout.of_hasPushout (I C n) (I C n))
  let c₀ : P ⟶ B := ObjectProperty.homMk (I C (n+1))
  let u : B ⟶ D := ObjectProperty.homMk (unitRetraction hC n)
  let j₀Face : D ⟶ B := ObjectProperty.homMk (J C n)
  let j₁Face : D ⟶ B := ObjectProperty.homMk (targetDisk C n)
  have hc₀ : cofibrations (Afin C hC) c₀ := by
    change finiteCellMaps C (F.map c₀)
    exact Cylinder.FiniteCellCategory.finiteCellMaps_I (C := C) (n+1)
  have hInl : j₀Std ≫ c₀ = j₀Face := by
    apply F.map_injective
    change pushout.inl (I C n) (I C n) ≫ I C (n+1) = J C n
    exact Cylinder.FiniteCellCategory.boundary_inl_I (C := C) n
  have hInr : j₁Std ≫ c₀ = j₁Face := by
    apply F.map_injective
    change pushout.inr (I C n) (I C n) ≫ I C (n+1) = targetDisk C n
    exact Cylinder.FiniteCellCategory.boundary_inr_I (C := C) n
  have hJ : j₀Face ≫ u = 𝟙 D := by
    apply F.map_injective
    change J C n ≫ unitRetraction hC n = 𝟙 (disk C n)
    exact source_unitRetraction hC n
  have hT : j₁Face ≫ u = 𝟙 D := by
    apply F.map_injective
    change targetDisk C n ≫ unitRetraction hC n = 𝟙 (disk C n)
    exact target_unitRetraction hC n
  have hcomm : i ≫ cyl.j₀ = i ≫ cyl.j₁ := cyl.isPushout.w
  let φP : P ⟶ cyl.P := hStd.desc cyl.j₀ cyl.j₁ hcomm
  have hφ₀ : j₀Std ≫ φP = cyl.j₀ := hStd.inl_desc _ _ hcomm
  have hφ₁ : j₁Std ≫ φP = cyl.j₁ := hStd.inr_desc _ _ hcomm
  have hsq : (φP ≫ cyl.c) ≫ cyl.p = c₀ ≫ u := by
    apply hStd.hom_ext
    · calc
        j₀Std ≫ φP ≫ cyl.c ≫ cyl.p = (j₀Std ≫ φP) ≫ cyl.c ≫ cyl.p := by cat_disch
        _ = cyl.j₀ ≫ cyl.c ≫ cyl.p := by rw [hφ₀]
        _ = 𝟙 D := cyl.j₀_c_p
        _ = j₀Face ≫ u := hJ.symm
        _ = (j₀Std ≫ c₀) ≫ u := by rw [hInl]
        _ = j₀Std ≫ (c₀ ≫ u) := by cat_disch
    · calc
        j₁Std ≫ φP ≫ cyl.c ≫ cyl.p = (j₁Std ≫ φP) ≫ cyl.c ≫ cyl.p := by cat_disch
        _ = cyl.j₁ ≫ cyl.c ≫ cyl.p := by rw [hφ₁]
        _ = 𝟙 D := cyl.j₁_c_p
        _ = j₁Face ≫ u := hT.symm
        _ = (j₁Std ≫ c₀) ≫ u := by rw [hInr]
        _ = j₁Std ≫ (c₀ ≫ u) := by cat_disch
  obtain ⟨t, ht⟩ := cylinderCategory_exactLift c₀ cyl.p (φP ≫ cyl.c) u
    hc₀ cyl.p_mem hsq
  have hsource : j₀Face ≫ t = cyl.j₀ ≫ cyl.c := by
    calc
      j₀Face ≫ t = (j₀Std ≫ c₀) ≫ t := by rw [← hInl]
      _ = j₀Std ≫ (c₀ ≫ t) := by cat_disch
      _ = j₀Std ≫ (φP ≫ cyl.c) := by rw [ht]
      _ = (j₀Std ≫ φP) ≫ cyl.c := by cat_disch
      _ = cyl.j₀ ≫ cyl.c := by rw [hφ₀]
  have htarget : j₁Face ≫ t = cyl.j₁ ≫ cyl.c := by
    calc
      j₁Face ≫ t = (j₁Std ≫ c₀) ≫ t := by rw [← hInr]
      _ = j₁Std ≫ (c₀ ≫ t) := by cat_disch
      _ = j₁Std ≫ (φP ≫ cyl.c) := by rw [ht]
      _ = (j₁Std ≫ φP) ≫ cyl.c := by cat_disch
      _ = cyl.j₁ ≫ cyl.c := by rw [hφ₁]
  exact ⟨t, hsource, htarget⟩

private theorem W_of_completionWeakEquivalence {C : GlobularTheory.{u}}
    (hC : C.IsCoherator) {X Y : C.Model} (f : X ⟶ Y)
    (h : Completion.weakEquivalences (Afin C hC) ((Packages.restriction hC).map f)) :
    W hC f := by
  change presheafWeakEquivalences ((Packages.restriction hC).map f).hom at h
  let F := Afin.ι hC
  have hExact : GlobularSet.ExactBoundaryTest (underlyingMap f) := by
    intro n bd y hy
    let R := boundaryRepresentation C n
    let A : Afin C hC := ⟨R.obj, boundaryDisk_finitelyCellular n⟩
    let B : Afin C hC := ⟨disk C n, Packages.disk_finitelyCellular C n⟩
    let i : A ⟶ B := ObjectProperty.homMk R.inclusion
    have hi : cofibrations (Afin C hC) i := by
      change finiteCellMaps C (F.map i)
      change finiteCellMaps C R.inclusion
      simpa [R] using Cylinder.FiniteCellCategory.finiteCellMaps_I (C := C) n
    let a : F.obj A ⟶ X := (R.equiv X).symm bd
    let b : F.obj B ⟶ Y := (cellEquiv Y n).symm y
    have hsq : a ≫ f = R.inclusion ≫ b := by
      apply (R.equiv Y).injective
      calc
        R.equiv Y (a ≫ f) = (underlyingMap f).boundaryMap n (R.equiv X a) := R.naturality a f
        _ = (underlyingMap f).boundaryMap n bd := by simp [a]
        _ = Y.underlying.boundary n y := hy.symm
        _ = R.equiv Y (R.inclusion ≫ b) := by
          rw [R.inclusion_boundary]
          simp [b]
    have hsqPres : ((Packages.restriction hC).map f).hom.app (op A) a =
        ((Packages.restriction hC).obj Y).1.map i.op b := by
      change a ≫ f = F.map i ≫ b
      exact hsq
    obtain ⟨l, cyl, H, hl, h₀, h₁⟩ := h i hi a b hsqPres
    have hlModel : R.inclusion ≫ l = a := by
      change F.map i ≫ l = a at hl
      exact hl
    change disk C n ⟶ X at l
    change disk C n ⟶ Y at b
    change F.obj cyl.I ⟶ Y at H
    have h₀Model : F.map (cyl.j₀ ≫ cyl.c) ≫ H = l ≫ f := by
      change F.map (cyl.j₀ ≫ cyl.c) ≫ H = l ≫ f
      exact h₀
    have h₁Model : F.map (cyl.j₁ ≫ cyl.c) ≫ H = b := by
      change F.map (cyl.j₁ ≫ cyl.c) ≫ H = b
      exact h₁
    let e₀ : F.obj B ⟶ F.obj cyl.I := F.map (cyl.j₀ ≫ cyl.c)
    let e₁ : F.obj B ⟶ F.obj cyl.I := F.map (cyl.j₁ ≫ cyl.c)
    let x₀ := cellEquiv (F.obj cyl.I) n e₀
    let x₁ := cellEquiv (F.obj cyl.I) n e₁
    have hEq : R.inclusion ≫ e₀ = R.inclusion ≫ e₁ := by
      have hpush : i ≫ (cyl.j₀ ≫ cyl.c) = i ≫ (cyl.j₁ ≫ cyl.c) := by
        calc
          i ≫ (cyl.j₀ ≫ cyl.c) = (i ≫ cyl.j₀) ≫ cyl.c := by cat_disch
          _ = (i ≫ cyl.j₁) ≫ cyl.c := by rw [cyl.isPushout.w]
          _ = i ≫ (cyl.j₁ ≫ cyl.c) := by cat_disch
      have hFi : F.map i = R.inclusion := rfl
      rw [← hFi]
      change F.map i ≫ F.map (cyl.j₀ ≫ cyl.c) =
        F.map i ≫ F.map (cyl.j₁ ≫ cyl.c)
      calc
        F.map i ≫ F.map (cyl.j₀ ≫ cyl.c) = F.map (i ≫ (cyl.j₀ ≫ cyl.c)) :=
          (Functor.map_comp F i (cyl.j₀ ≫ cyl.c)).symm
        _ = F.map (i ≫ (cyl.j₁ ≫ cyl.c)) := congrArg F.map hpush
        _ = F.map i ≫ F.map (cyl.j₁ ≫ cyl.c) :=
          Functor.map_comp F i (cyl.j₁ ≫ cyl.c)
    have hBoundaryEq :
        (F.obj cyl.I).underlying.boundary n x₀ =
          (F.obj cyl.I).underlying.boundary n x₁ := by
      calc
        (F.obj cyl.I).underlying.boundary n x₀ =
            R.equiv (F.obj cyl.I) (R.inclusion ≫ e₀) := (R.inclusion_boundary e₀).symm
        _ = R.equiv (F.obj cyl.I) (R.inclusion ≫ e₁) :=
          congrArg (R.equiv (F.obj cyl.I)) hEq
        _ = (F.obj cyl.I).underlying.boundary n x₁ := R.inclusion_boundary e₁
    have hParallel : (F.obj cyl.I).underlying.Parallel n x₀ x₁ :=
      (GlobularSet.parallel_iff_boundary_eq (F.obj cyl.I).underlying n x₀ x₁).2 hBoundaryEq
    let bdCyl : (F.obj cyl.I).underlying.Boundary (n+1) := ⟨(x₀,x₁), hParallel⟩
    let yUnit : (F.obj B).underlying.Cell (n+1) :=
      (F.obj B).unitCell hC n (cellEquiv (F.obj B) n (𝟙 (F.obj B)))
    have h₀p : e₀ ≫ F.map cyl.p = 𝟙 (F.obj B) := by
      have h := congrArg F.map cyl.j₀_c_p
      simpa only [e₀, Functor.map_comp, F.map_id, Category.assoc] using h
    have h₁p : e₁ ≫ F.map cyl.p = 𝟙 (F.obj B) := by
      have h := congrArg F.map cyl.j₁_c_p
      simpa only [e₁, Functor.map_comp, F.map_id, Category.assoc] using h
    have hp₀ : (underlyingMap (F.map cyl.p)).app n x₀ =
        cellEquiv (F.obj B) n (𝟙 (F.obj B)) := by
      calc
        (underlyingMap (F.map cyl.p)).app n x₀ =
            cellEquiv (F.obj B) n (e₀ ≫ F.map cyl.p) :=
          (cellEquiv_comp n e₀ (F.map cyl.p)).symm
        _ = cellEquiv (F.obj B) n (𝟙 (F.obj B)) :=
          congrArg (cellEquiv (F.obj B) n) h₀p
    have hp₁ : (underlyingMap (F.map cyl.p)).app n x₁ =
        cellEquiv (F.obj B) n (𝟙 (F.obj B)) := by
      calc
        (underlyingMap (F.map cyl.p)).app n x₁ =
            cellEquiv (F.obj B) n (e₁ ≫ F.map cyl.p) :=
          (cellEquiv_comp n e₁ (F.map cyl.p)).symm
        _ = cellEquiv (F.obj B) n (𝟙 (F.obj B)) :=
          congrArg (cellEquiv (F.obj B) n) h₁p
    have hUnitBoundary : (F.obj B).underlying.boundary (n+1) yUnit =
        (underlyingMap (F.map cyl.p)).boundaryMap (n+1) bdCyl := by
      apply Subtype.ext
      change ((F.obj B).underlying.source n yUnit,
          (F.obj B).underlying.target n yUnit) =
        ((underlyingMap (F.map cyl.p)).app n x₀,
          (underlyingMap (F.map cyl.p)).app n x₁)
      apply Prod.ext
      · simpa [yUnit, GlobularTheory.Model.unitCell_source] using hp₀.symm
      · simpa [yUnit, GlobularTheory.Model.unitCell_target] using hp₁.symm
    have hpW : W hC (F.map cyl.p) := cyl.p_mem
    have hCylCof : ModelCofibrant C (F.obj cyl.I) := afinObject_modelCofibrant hC cyl.I
    obtain ⟨z, hz, _⟩ := Cylinder.FiniteCellCategory.weakEquivalence_exactBoundaryTest hC
      (F.map cyl.p) hpW hCylCof (n+1) bdCyl yUnit hUnitBoundary
    let g : disk C (n+1) ⟶ F.obj cyl.I :=
      (cellEquiv (F.obj cyl.I) (n+1)).symm z
    have hz' := congrArg Subtype.val hz
    have hSourceCell : (F.obj cyl.I).underlying.source n z = x₀ :=
      congrArg Prod.fst hz'
    have hTargetCell : (F.obj cyl.I).underlying.target n z = x₁ :=
      congrArg Prod.snd hz'
    have hJg : J C n ≫ g = e₀ := by
      apply (cellEquiv (F.obj cyl.I) n).injective
      rw [cellEquiv_J]
      simpa [g, x₀] using hSourceCell
    have hTg : targetDisk C n ≫ g = e₁ := by
      apply (cellEquiv (F.obj cyl.I) n).injective
      rw [cellEquiv_targetDisk]
      simpa [g, x₁] using hTargetCell
    have hJPath : J C n ≫ (g ≫ H) = l ≫ f := by
      rw [← Category.assoc, hJg]
      change e₀ ≫ H = l ≫ f
      exact h₀Model
    have hTPath : targetDisk C n ≫ (g ≫ H) = b := by
      rw [← Category.assoc, hTg]
      change e₁ ≫ H = b
      exact h₁Model
    have hxBoundary : X.underlying.boundary n (cellEquiv X n l) = bd := by
      calc
        X.underlying.boundary n (cellEquiv X n l) = R.equiv X (R.inclusion ≫ l) :=
          (R.inclusion_boundary l).symm
        _ = R.equiv X a := congrArg (R.equiv X) hlModel
        _ = bd := Equiv.apply_symm_apply (R.equiv X) bd
    refine ⟨cellEquiv X n l, hxBoundary, ?_⟩
    refine ⟨cellEquiv Y (n+1) (g ≫ H), ?_, ?_⟩
    · calc
        Y.underlying.source n (cellEquiv Y (n+1) (g ≫ H)) =
            cellEquiv Y n (J C n ≫ (g ≫ H)) := by rw [← cellEquiv_J]
        _ = cellEquiv Y n (l ≫ f) := congrArg (cellEquiv Y n) hJPath
        _ = (underlyingMap f).app n (cellEquiv X n l) := cellEquiv_comp n l f
    · calc
        Y.underlying.target n (cellEquiv Y (n+1) (g ≫ H)) =
            cellEquiv Y n (targetDisk C n ≫ (g ≫ H)) := by rw [← cellEquiv_targetDisk]
        _ = cellEquiv Y n b := congrArg (cellEquiv Y n) hTPath
        _ = y := by simp [b]
  exact GlobularTheory.Model.weakEquivalence_of_exactBoundaryTest hC f hExact

end HomotopyHypothesis.Homotopy.WeakEquivalence

namespace HomotopyHypothesis.Blueprint.Packages

universe u

theorem completion_weakEquivalences_iff_proof {C : GlobularTheory.{u}}
    (hC : C.IsCoherator) {X Y : C.Model} (f : X ⟶ Y) :
    Completion.weakEquivalences (Afin C hC) ((restriction hC).map f) ↔ W hC f := by
  constructor
  · exact HomotopyHypothesis.Homotopy.WeakEquivalence.W_of_completionWeakEquivalence hC f
  · exact HomotopyHypothesis.Homotopy.WeakEquivalence.completionWeakEquivalence_of_W hC f

#print axioms completion_weakEquivalences_iff_proof

end HomotopyHypothesis.Blueprint.Packages
