import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.Approximation
import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.Main.Part1
import HomotopyHypothesis.Blueprint.Henry.Packages.General.SliceObjForgetIsAcyclicIff
import HomotopyHypothesis.Blueprint.Henry.Packages.General.SliceObjIsLiftingTarget
import HomotopyHypothesis.Blueprint.Henry.Packages.General.WeakEquivalenceIff
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
/-!
# Homotopy terminal objects in homotopy slices

Formal consequences of the h-terminality results in Henry's theory of cylinder categories.
-/

universe v u v' u'

open CategoryTheory Limits HomotopicalAlgebra HomotopyHypothesis.Henry

namespace HomotopyHypothesis.Cylinder.HomotopyTerminalSlice

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C]

theorem homotopic_weakEquivalences [IsCylinderCategory C] {X Y : C} {f g : X ⟶ Y}
    (hfg : Homotopic f g) : weakEquivalences C f ↔ weakEquivalences C g := by
  rcases hfg with ⟨I, hI, cyl, H, h₀, h₁⟩
  have hj₀ : weakEquivalences C (cyl.j₀ ≫ cyl.c) := by
    have hcomp : (cyl.j₀ ≫ cyl.c) ≫ cyl.p = 𝟙 X := by
      simpa [Category.assoc] using cyl.j₀_c_p
    have hs := (IsCylinderCategory.twoOutOfSix (C := C)
      (cyl.j₀ ≫ cyl.c) cyl.p (𝟙 X) (by simpa [hcomp] using
        (IsCylinderCategory.weakEquivalences_isMultiplicative (C := C)).id_mem X)
      (by simpa using cyl.p_mem)).1
    exact hs
  have hj₁ : weakEquivalences C (cyl.j₁ ≫ cyl.c) := by
    have hcomp : (cyl.j₁ ≫ cyl.c) ≫ cyl.p = 𝟙 X := by
      simpa [Category.assoc] using cyl.j₁_c_p
    have hs := (IsCylinderCategory.twoOutOfSix (C := C)
      (cyl.j₁ ≫ cyl.c) cyl.p (𝟙 X) (by simpa [hcomp] using
        (IsCylinderCategory.weakEquivalences_isMultiplicative (C := C)).id_mem X)
      (by simpa using cyl.p_mem)).1
    exact hs
  constructor
  · intro hf
    have h₀' : weakEquivalences C ((cyl.j₀ ≫ cyl.c) ≫ H) := by simpa [h₀] using hf
    have hH := (IsCylinderCategory.twoOutOfSix (C := C)
      (𝟙 X) (cyl.j₀ ≫ cyl.c) H
      (by simpa using hj₀)
      (by simpa [Category.assoc] using h₀')).2.2.1
    have hg' : weakEquivalences C ((cyl.j₁ ≫ cyl.c) ≫ H) :=
      (IsCylinderCategory.weakEquivalences_isMultiplicative (C := C)).comp_mem _ _ hj₁ hH
    simpa [h₁, Category.assoc] using hg'
  · intro hg
    have h₁' : weakEquivalences C ((cyl.j₁ ≫ cyl.c) ≫ H) := by simpa [h₁] using hg
    have hH := (IsCylinderCategory.twoOutOfSix (C := C)
      (𝟙 X) (cyl.j₁ ≫ cyl.c) H
      (by simpa using hj₁)
      (by simpa [Category.assoc] using h₁')).2.2.1
    have hf' : weakEquivalences C ((cyl.j₀ ≫ cyl.c) ≫ H) :=
      (IsCylinderCategory.weakEquivalences_isMultiplicative (C := C)).comp_mem _ _ hj₀ hH
    simpa [h₀, Category.assoc] using hf'

end HomotopyHypothesis.Cylinder.HomotopyTerminalSlice

namespace HomotopyHypothesis.Cylinder.HomotopyTerminalSlice

open Opposite

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]

theorem completion_yoneda_cofibration {A B : C} (i : A ⟶ B)
    (hi : cofibrations C i) :
    Completion.cofibrations C ((Completion.yoneda C).map i) := by
  change MorphismProperty.llp (Completion.trivialFibrations C) _
  intro P Q p hp
  refine ⟨fun {top bottom} sq => ?_⟩
  have hOA : ((Completion.yoneda C).obj A).obj = CategoryTheory.yoneda.obj A := rfl
  have hOB : ((Completion.yoneda C).obj B).obj = CategoryTheory.yoneda.obj B := rfl
  let eA : ((Completion.yoneda C).obj A).obj ≅ CategoryTheory.yoneda.obj A := Iso.refl _
  let eB : ((Completion.yoneda C).obj B).obj ≅ CategoryTheory.yoneda.obj B := Iso.refl _
  have hmap : ((Completion.yoneda C).map i).hom = CategoryTheory.yoneda.map i := rfl
  have hnat : eA.inv ≫ ((Completion.yoneda C).map i).hom =
      CategoryTheory.yoneda.map i ≫ eB.inv := by
    rw [hmap]
    cases hOA
    cases hOB
    change 𝟙 (CategoryTheory.yoneda.obj A) ≫ CategoryTheory.yoneda.map i =
      CategoryTheory.yoneda.map i ≫ 𝟙 (CategoryTheory.yoneda.obj B)
    simp [eA, eB]
  have hnat' : ((Completion.yoneda C).map i).hom ≫ eB.hom =
      eA.hom ≫ CategoryTheory.yoneda.map i := by
    rw [hmap]
    cases hOA
    cases hOB
    change CategoryTheory.yoneda.map i ≫ 𝟙 (CategoryTheory.yoneda.obj B) =
      𝟙 (CategoryTheory.yoneda.obj A) ≫ CategoryTheory.yoneda.map i
    simp [eA, eB]
  let top' := eA.inv ≫ top.hom
  let bottom' := eB.inv ≫ bottom.hom
  let a := CategoryTheory.yonedaEquiv top'
  let b := CategoryTheory.yonedaEquiv bottom'
  have hab : p.hom.app (op A) a = Q.obj.map i.op b := by
    have hs0 := congrArg (fun z => z.hom) sq.w
    change top.hom ≫ p.hom = ((Completion.yoneda C).map i).hom ≫ bottom.hom at hs0
    have hs : top' ≫ p.hom = CategoryTheory.yoneda.map i ≫ bottom' := by
      dsimp [top', bottom']
      calc
        eA.inv ≫ top.hom ≫ p.hom = eA.inv ≫ (top.hom ≫ p.hom) :=
          rfl
        _ = eA.inv ≫ (((Completion.yoneda C).map i).hom ≫ bottom.hom) := by rw [hs0]
        _ = (eA.inv ≫ ((Completion.yoneda C).map i).hom) ≫ bottom.hom :=
          (Category.assoc _ _ _).symm
        _ = (CategoryTheory.yoneda.map i ≫ eB.inv) ≫ bottom.hom := by rw [hnat]
        _ = CategoryTheory.yoneda.map i ≫ eB.inv ≫ bottom.hom := Category.assoc _ _ _
    calc
      p.hom.app (op A) a = CategoryTheory.yonedaEquiv (top' ≫ p.hom) := by
        simp [a, CategoryTheory.yonedaEquiv_comp]
      _ = CategoryTheory.yonedaEquiv (CategoryTheory.yoneda.map i ≫ bottom') :=
        congrArg CategoryTheory.yonedaEquiv hs
      _ = Q.obj.map i.op b := by
        rw [← CategoryTheory.yonedaEquiv_naturality]
  obtain ⟨l, hli, hlp⟩ := hp i hi a b hab
  let ell := CategoryTheory.yonedaEquiv.symm l
  let ellActual := eB.hom ≫ ell
  have hleftRaw : CategoryTheory.yoneda.map i ≫ ell = top' := by
    apply CategoryTheory.yonedaEquiv.injective
    rw [← CategoryTheory.yonedaEquiv_naturality]
    simpa [ell, a] using hli
  have hrightRaw : ell ≫ p.hom = bottom' := by
    apply CategoryTheory.yonedaEquiv.injective
    rw [CategoryTheory.yonedaEquiv_comp]
    simpa [ell, b] using hlp
  have hleft : (Completion.yoneda C).map i ≫ ObjectProperty.homMk ellActual = top := by
    apply ObjectProperty.hom_ext
    change ((Completion.yoneda C).map i).hom ≫ ellActual = top.hom
    dsimp [ellActual]
    calc
      (((Completion.yoneda C).map i).hom ≫ eB.hom) ≫ ell =
          (eA.hom ≫ CategoryTheory.yoneda.map i) ≫ ell := by rw [hnat']
      _ = eA.hom ≫ (CategoryTheory.yoneda.map i ≫ ell) :=
        by simp [Category.assoc]
      _ = eA.hom ≫ top' := by rw [hleftRaw]
      _ = top.hom := by simp [top', Category.assoc]
  have hright : ObjectProperty.homMk ellActual ≫ p = bottom := by
    apply ObjectProperty.hom_ext
    change ellActual ≫ p.hom = bottom.hom
    dsimp [ellActual]
    calc
      eB.hom ≫ ell ≫ p.hom = eB.hom ≫ bottom' := by rw [hrightRaw]
      _ = bottom.hom := by simp [bottom', Category.assoc]
  exact ⟨⟨{ l := ObjectProperty.homMk ellActual, fac_left := hleft, fac_right := hright }⟩⟩

variable {C : Type (u + 1)} [Category.{u} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C]

theorem brown_factorization [IsCylinderCategory C] {A B : C} (f : A ⟶ B) :
    ∃ (Q : C) (i : A ⟶ Q) (p : Q ⟶ B), cofibrations C i ∧
      weakEquivalences C p ∧ i ≫ p = f := by
  obtain ⟨I, ⟨hI⟩⟩ := IsCofibrationCategory.exists_initial (C := C)
  let cyl : RelativeCylinder (hI.to A) := Classical.choice
    (IsCylinderCategory.exists_cylinder (C := C) hI A)
  have h0A : cofibrations C (hI.to A) :=
    IsCofibrationCategory.initial_cofibration hI A
  have h0B : cofibrations C (hI.to B) :=
    IsCofibrationCategory.initial_cofibration hI B
  have hcof := (inferInstance : IsCofibrationCategory C)
  letI : (cofibrations C).IsStableUnderCobaseChange := hcof.isStableUnderCobaseChange
  letI : (cofibrations C).IsMultiplicative := hcof.isMultiplicative
  letI : HasPushout (hI.to B) (hI.to A) := hcof.hasPushout _ _ h0B
  let E := pushout (hI.to B) (hI.to A)
  let inA : A ⟶ E := pushout.inr (hI.to B) (hI.to A)
  let inB : B ⟶ E := pushout.inl (hI.to B) (hI.to A)
  let e : cyl.P ⟶ E := cyl.isPushout.desc (pushout.inr (hI.to B) (hI.to A))
      (f ≫ pushout.inl (hI.to B) (hI.to A)) (by apply hI.hom_ext)
  have he0 : cyl.j₀ ≫ e = inA := by
    dsimp [e, inA]
    simp
  have he1 : cyl.j₁ ≫ e = f ≫ inB := by
    dsimp [e, inB]
    simp
  letI : HasPushout cyl.c e := hcof.hasPushout cyl.c e cyl.c_mem
  let Q := pushout cyl.c e
  let qI : cyl.I ⟶ Q := pushout.inl cyl.c e
  let qE : E ⟶ Q := pushout.inr cyl.c e
  let i : A ⟶ Q := inA ≫ qE
  let jB : B ⟶ Q := inB ≫ qE
  let j0a : A ⟶ cyl.I := cyl.j₀ ≫ cyl.c
  let a1 : A ⟶ cyl.I := cyl.j₁ ≫ cyl.c
  let qEtoB : E ⟶ B := pushout.desc (𝟙 B) f (by
    apply hI.hom_ext)
  have hqE_A : inA ≫ qEtoB = f := by
    simp [qEtoB, inA, pushout.inr_desc]
  have hqE_B : inB ≫ qEtoB = 𝟙 B := by
    simp [qEtoB, inB, pushout.inl_desc]
  have hqcond : cyl.c ≫ (cyl.p ≫ f) = e ≫ qEtoB := by
    apply cyl.isPushout.hom_ext
    · calc
        cyl.j₀ ≫ cyl.c ≫ cyl.p ≫ f = f := by
          simpa [Category.assoc] using congrArg (fun z => z ≫ f) cyl.j₀_c_p
        _ = cyl.j₀ ≫ e ≫ qEtoB := by
          calc
            f = inA ≫ qEtoB := hqE_A.symm
            _ = (cyl.j₀ ≫ e) ≫ qEtoB := by rw [← he0]
            _ = cyl.j₀ ≫ e ≫ qEtoB := by simp [Category.assoc]
    · calc
        cyl.j₁ ≫ cyl.c ≫ cyl.p ≫ f = f := by
          simpa [Category.assoc] using congrArg (fun z => z ≫ f) cyl.j₁_c_p
        _ = cyl.j₁ ≫ e ≫ qEtoB := by
          calc
            f = f ≫ (inB ≫ qEtoB) := by rw [hqE_B]; simp
            _ = (f ≫ inB) ≫ qEtoB := by simp [Category.assoc]
            _ = (cyl.j₁ ≫ e) ≫ qEtoB := by rw [← he1]
            _ = cyl.j₁ ≫ e ≫ qEtoB := by simp [Category.assoc]
  let q : Q ⟶ B := pushout.desc (cyl.p ≫ f) qEtoB hqcond
  have hInA : cofibrations C inA := by
    exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout
      (IsPushout.of_hasPushout (hI.to B) (hI.to A)).flip h0B
  have hQE : cofibrations C qE := by
    exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout
      (IsPushout.of_hasPushout cyl.c e).flip cyl.c_mem
  have hi : cofibrations C i := hcof.isMultiplicative.comp_mem inA qE hInA hQE
  have ha1cof : cofibrations C a1 := by
    have hj₁ : cofibrations C cyl.j₁ := by
      exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout
        cyl.isPushout.flip h0A
    exact hcof.isMultiplicative.comp_mem cyl.j₁ cyl.c hj₁ cyl.c_mem
  have ha1we : weakEquivalences C a1 := by
    have hcomp : a1 ≫ cyl.p = 𝟙 A := by
      simpa [a1, Category.assoc] using cyl.j₁_c_p
    exact (IsCylinderCategory.twoOutOfSix (C := C) a1 cyl.p (𝟙 A)
      (by simpa [hcomp] using
        (IsCylinderCategory.weakEquivalences_isMultiplicative (C := C)).id_mem A)
      (by simpa using cyl.p_mem)).1
  have hcomm : a1 ≫ qI = f ≫ jB := by
    dsimp [a1, qI, jB]
    calc
      (cyl.j₁ ≫ cyl.c) ≫ pushout.inl cyl.c e =
          cyl.j₁ ≫ (cyl.c ≫ pushout.inl cyl.c e) := by simp [Category.assoc]
      _ = cyl.j₁ ≫ (e ≫ pushout.inr cyl.c e) := by rw [pushout.condition]
      _ = (cyl.j₁ ≫ e) ≫ pushout.inr cyl.c e := by simp [Category.assoc]
      _ = (f ≫ inB) ≫ pushout.inr cyl.c e := by rw [he1]
      _ = f ≫ (inB ≫ pushout.inr cyl.c e) := by simp [Category.assoc]
  have hpush : IsPushout a1 f qI jB := by
    have hcol : IsColimit (PushoutCocone.mk qI jB hcomm) := by
      let v (s : PushoutCocone a1 f) : E ⟶ s.pt :=
        pushout.desc s.inr (cyl.j₀ ≫ cyl.c ≫ s.inl) (by apply hI.hom_ext)
      have hvA (s : PushoutCocone a1 f) :
          inA ≫ v s = cyl.j₀ ≫ cyl.c ≫ s.inl := by
        dsimp [v, inA]
        exact pushout.inr_desc s.inr (cyl.j₀ ≫ cyl.c ≫ s.inl) (by apply hI.hom_ext)
      have hvB (s : PushoutCocone a1 f) : inB ≫ v s = s.inr := by
        dsimp [v, inB]
        exact pushout.inl_desc s.inr (cyl.j₀ ≫ cyl.c ≫ s.inl) (by apply hI.hom_ext)
      have hv (s : PushoutCocone a1 f) : cyl.c ≫ s.inl = e ≫ v s := by
        apply cyl.isPushout.hom_ext
        · calc
            cyl.j₀ ≫ cyl.c ≫ s.inl = inA ≫ v s := (hvA s).symm
            _ = (cyl.j₀ ≫ e) ≫ v s := by rw [← he0]
            _ = cyl.j₀ ≫ e ≫ v s := by simp [Category.assoc]
        · have h1 : cyl.j₁ ≫ cyl.c ≫ s.inl = f ≫ inB ≫ v s := by
            calc
              cyl.j₁ ≫ cyl.c ≫ s.inl = a1 ≫ s.inl := by simp [a1]
              _ = f ≫ s.inr := s.condition
              _ = f ≫ (inB ≫ v s) := by rw [hvB s]
          calc
            cyl.j₁ ≫ cyl.c ≫ s.inl = f ≫ inB ≫ v s := h1
            _ = (f ≫ inB) ≫ v s := by simp [Category.assoc]
            _ = (cyl.j₁ ≫ e) ≫ v s := by rw [← he1]
            _ = cyl.j₁ ≫ e ≫ v s := by simp [Category.assoc]
      let d (s : PushoutCocone a1 f) : Q ⟶ s.pt := by
        exact pushout.desc s.inl (v s) (hv s)
      have d_inl (s : PushoutCocone a1 f) : qI ≫ d s = s.inl := by
        dsimp [d, qI]
        exact pushout.inl_desc s.inl (v s) (hv s)
      have hqEd (s : PushoutCocone a1 f) : qE ≫ d s = v s := by
        dsimp [d, qE]
        exact pushout.inr_desc s.inl (v s) (hv s)
      have d_inr (s : PushoutCocone a1 f) : jB ≫ d s = s.inr := by
        calc
          jB ≫ d s = inB ≫ (qE ≫ d s) := by simp [jB, Category.assoc]
          _ = inB ≫ v s := by rw [hqEd s]
          _ = s.inr := hvB s
      refine PushoutCocone.IsColimit.mk hcomm d d_inl d_inr ?_
      intro s m hm₁ hm₂
      have hQcond : cyl.c ≫ qI = e ≫ qE := by
        change cyl.c ≫ pushout.inl cyl.c e = e ≫ pushout.inr cyl.c e
        exact pushout.condition
      have hinAqE : inA ≫ qE = j0a ≫ qI := by
        calc
          inA ≫ qE = (cyl.j₀ ≫ e) ≫ qE := by rw [← he0]
          _ = cyl.j₀ ≫ (e ≫ qE) := Category.assoc _ _ _
          _ = cyl.j₀ ≫ (cyl.c ≫ qI) := by rw [← hQcond]
          _ = j0a ≫ qI := by simp [j0a, Category.assoc]
      apply pushout.hom_ext
      · exact hm₁.trans (d_inl s).symm
      · apply pushout.hom_ext
        · simpa [jB, Category.assoc] using hm₂.trans (d_inr s).symm
        · calc
            inA ≫ qE ≫ m = (inA ≫ qE) ≫ m := (Category.assoc inA qE m).symm
            _ = (j0a ≫ qI) ≫ m := congrArg (fun g => g ≫ m) hinAqE
            _ = j0a ≫ (qI ≫ m) := Category.assoc j0a qI m
            _ = j0a ≫ s.inl := by rw [hm₁]
            _ = j0a ≫ (qI ≫ d s) := by rw [d_inl]
            _ = (j0a ≫ qI) ≫ d s := (Category.assoc j0a qI (d s)).symm
            _ = (inA ≫ qE) ≫ d s := congrArg (fun g => g ≫ d s) hinAqE.symm
            _ = inA ≫ qE ≫ d s := Category.assoc inA qE (d s)
    exact IsPushout.of_isColimit hcol
  have hjBwe : weakEquivalences C jB := by
    have h₁ := IsCylinderCategory.trivialCofibration_cobaseChange (C := C)
      a1 f qI jB hpush ha1cof ha1we
    exact h₁
  have hsection : jB ≫ q = 𝟙 B := by
    have hqE_q : qE ≫ q = qEtoB := by
      dsimp [q, qE]
      exact pushout.inr_desc (cyl.p ≫ f) qEtoB hqcond
    calc
      jB ≫ q = inB ≫ (qE ≫ q) := by simp [jB, Category.assoc]
      _ = inB ≫ qEtoB := by rw [hqE_q]
      _ = 𝟙 B := hqE_B
  have hqwe : weakEquivalences C q := by
    exact (IsCylinderCategory.twoOutOfSix (C := C) (𝟙 B) jB q
      (by simpa using hjBwe)
      (by simpa [hsection] using
        (IsCylinderCategory.weakEquivalences_isMultiplicative (C := C)).id_mem B)).2.2.1
  refine ⟨Q, i, q, hi, hqwe, ?_⟩
  have hqE_q : qE ≫ q = qEtoB := by
    dsimp [q, qE]
    exact pushout.inr_desc (cyl.p ≫ f) qEtoB hqcond
  calc
    i ≫ q = inA ≫ (qE ≫ q) := by simp [i, Category.assoc]
    _ = inA ≫ qEtoB := by rw [hqE_q]
    _ = f := hqE_A

theorem semilifting_exact [IsCylinderCategory C] {A B X Y : C} (i : A ⟶ B)
    (hi : cofibrations C i) (w : X ⟶ Y) (hw : weakEquivalences C w)
    (u : A ⟶ X) (v : B ⟶ Y) (hsq : i ≫ v = u ≫ w) :
    ∃ l : B ⟶ X, i ≫ l = u := by
  have hcof := (inferInstance : IsCofibrationCategory C)
  letI : (cofibrations C).IsStableUnderCobaseChange := hcof.isStableUnderCobaseChange
  letI : (cofibrations C).IsMultiplicative := hcof.isMultiplicative
  letI : HasPushout i u := hcof.hasPushout i u hi
  let P := pushout i u
  let inB : B ⟶ P := pushout.inl i u
  let inX : X ⟶ P := pushout.inr i u
  let k : P ⟶ Y := pushout.desc v w hsq
  obtain ⟨Q, j, q, hj, hq, hjq⟩ :=
    brown_factorization (C := C) k
  let cX : X ⟶ Q := inX ≫ j
  have hinc : cofibrations C inX := by
    exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout
      (IsPushout.of_hasPushout i u).flip hi
  have hcX : cofibrations C cX :=
    hcof.isMultiplicative.comp_mem inX j hinc hj
  have hcXq : cX ≫ q = w := by
    calc
      cX ≫ q = inX ≫ (j ≫ q) := by simp [cX, Category.assoc]
      _ = inX ≫ k := by rw [hjq]
      _ = w := by simp [k, inX, pushout.inr_desc]
  have hcXwe : weakEquivalences C cX := by
    exact (IsCylinderCategory.twoOutOfSix (C := C) cX q (𝟙 Y)
      (by rw [hcXq]; exact hw)
      (by simpa using hq)).1
  obtain ⟨r, hr⟩ := IsCylinderCategory.exists_retraction (C := C) cX hcX hcXwe
  refine ⟨inB ≫ j ≫ r, ?_⟩
  have hpo : i ≫ inB = u ≫ inX := by
    change i ≫ pushout.inl i u = u ≫ pushout.inr i u
    exact pushout.condition
  calc
    i ≫ inB ≫ j ≫ r = u ≫ inX ≫ j ≫ r := by
      simpa [Category.assoc] using congrArg (fun g => g ≫ j ≫ r) hpo
    _ = u ≫ (cX ≫ r) := by
      dsimp [cX]
      simp [Category.assoc]
    _ = u := by rw [hr]; simp

structure SliceCylinderData (X : C) where
  I : C
  hI : IsInitial I
  cyl : RelativeCylinder (hI.to X)

noncomputable def chooseSliceCylinder [IsCylinderCategory C] (X : C) :
    SliceCylinderData X := by
  let hEx := IsCofibrationCategory.exists_initial (C := C)
  let I := Classical.choose hEx
  let hI : IsInitial I := Classical.choice (Classical.choose_spec hEx)
  exact ⟨I, hI, Classical.choice (IsCylinderCategory.exists_cylinder (C := C) hI X)⟩

noncomputable abbrev cylinderSliceObjOfData [IsCylinderCategory C] (X : C)
    (d : SliceCylinderData X) : SliceObj X := by
  let cyl := d.cyl
  have hcof := (inferInstance : IsCofibrationCategory C)
  letI : (cofibrations C).IsStableUnderCobaseChange := hcof.isStableUnderCobaseChange
  letI : (cofibrations C).IsMultiplicative := hcof.isMultiplicative
  have hj₁ : cofibrations C cyl.j₁ := by
    exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout
      cyl.isPushout.flip (hcof.initial_cofibration d.hI X)
  have hₐ : cofibrations C (cyl.j₀ ≫ cyl.c) := by
    have hj₀ : cofibrations C cyl.j₀ := by
      exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout
        cyl.isPushout (hcof.initial_cofibration d.hI X)
    exact hcof.isMultiplicative.comp_mem cyl.j₀ cyl.c hj₀ cyl.c_mem
  have hₓ : cofibrations C (cyl.j₁ ≫ cyl.c) :=
    hcof.isMultiplicative.comp_mem cyl.j₁ cyl.c hj₁ cyl.c_mem
  have hₐwe : weakEquivalences C (cyl.j₀ ≫ cyl.c) := by
    have hc : (cyl.j₀ ≫ cyl.c) ≫ cyl.p = 𝟙 X := by
      simpa [Category.assoc] using cyl.j₀_c_p
    exact (IsCylinderCategory.twoOutOfSix (C := C)
      (cyl.j₀ ≫ cyl.c) cyl.p (𝟙 X)
      (by simpa [hc] using
        (IsCylinderCategory.weakEquivalences_isMultiplicative (C := C)).id_mem X)
      (by simpa using cyl.p_mem)).1
  have hₓwe : weakEquivalences C (cyl.j₁ ≫ cyl.c) := by
    have hc : (cyl.j₁ ≫ cyl.c) ≫ cyl.p = 𝟙 X := by
      simpa [Category.assoc] using cyl.j₁_c_p
    exact (IsCylinderCategory.twoOutOfSix (C := C)
      (cyl.j₁ ≫ cyl.c) cyl.p (𝟙 X)
      (by simpa [hc] using
        (IsCylinderCategory.weakEquivalences_isMultiplicative (C := C)).id_mem X)
      (by simpa using cyl.p_mem)).1
  exact
    { A₀ := X
      Af := cyl.I
      a := cyl.j₀ ≫ cyl.c
      x := cyl.j₁ ≫ cyl.c
      cofibrant := ⟨d.I, d.hI,
        ⟨cyl.P, cyl.j₀, cyl.j₁, cyl.isPushout, cyl.c, by simp, by simp, cyl.c_mem⟩⟩
      x_cofibration := hₓ
      x_weakEquivalence := hₓwe }

noncomputable abbrev cylinderSliceObj [IsCylinderCategory C] (X : C) : SliceObj X :=
  cylinderSliceObjOfData X (chooseSliceCylinder X)

theorem cylinderSliceData_isHTerminal [IsCylinderCategory C] (X : C)
    (d : SliceCylinderData X) : IsHTerminal (cylinderSliceObjOfData X d) := by
  letI : IsCylinderCategory (SliceObj X) :=
    (HomotopyHypothesis.Henry.Packages.sliceObj_isLiftingTarget X).1
  let cyl := d.cyl
  let aK : X ⟶ cyl.I := cyl.j₀ ≫ cyl.c
  let xK : X ⟶ cyl.I := cyl.j₁ ≫ cyl.c
  have hcof := (inferInstance : IsCofibrationCategory C)
  letI : (cofibrations C).IsStableUnderCobaseChange := hcof.isStableUnderCobaseChange
  letI : (cofibrations C).IsMultiplicative := hcof.isMultiplicative
  have hj₁ : cofibrations C cyl.j₁ := by
    exact MorphismProperty.IsStableUnderCobaseChange.of_isPushout
      cyl.isPushout.flip (hcof.initial_cofibration d.hI X)
  have hₓ : cofibrations C (cyl.j₁ ≫ cyl.c) :=
    hcof.isMultiplicative.comp_mem cyl.j₁ cyl.c hj₁ cyl.c_mem
  have hₓwe : weakEquivalences C (cyl.j₁ ≫ cyl.c) := by
    have hc : (cyl.j₁ ≫ cyl.c) ≫ cyl.p = 𝟙 X := by
      simpa [Category.assoc] using cyl.j₁_c_p
    exact (IsCylinderCategory.twoOutOfSix (C := C)
      (cyl.j₁ ≫ cyl.c) cyl.p (𝟙 X)
      (by simpa [hc] using
        (IsCylinderCategory.weakEquivalences_isMultiplicative (C := C)).id_mem X)
      (by simpa using cyl.p_mem)).1
  let K : SliceObj X :=
    { A₀ := X
      Af := cyl.I
      a := cyl.j₀ ≫ cyl.c
      x := cyl.j₁ ≫ cyl.c
      cofibrant := ⟨d.I, d.hI,
        ⟨cyl.P, cyl.j₀, cyl.j₁, cyl.isPushout, cyl.c, by simp, by simp, cyl.c_mem⟩⟩
      x_cofibration := hₓ
      x_weakEquivalence := hₓwe }
  have hK_a : K.a = aK := rfl
  have hK_x : K.x = xK := rfl
  have hK : K = cylinderSliceObjOfData X d := by rfl
  cases hK
  intro S T m hm g
  rcases hm with ⟨hm₀, hglue⟩
  rcases hglue with ⟨P, k, j, hP, latch, hk, hj, hlatch⟩
  have hvfcof : cofibrations C m.vf := by
    have hkcof : cofibrations C k :=
      MorphismProperty.IsStableUnderCobaseChange.of_isPushout hP hm₀
    simpa [hk] using hcof.isMultiplicative.comp_mem k latch hkcof hlatch
  have hmX : S.x ≫ m.vf = T.x := m.x_vf
  have hvfwe : weakEquivalences C m.vf := by
    exact (IsCylinderCategory.twoOutOfSix (C := C) (𝟙 X) S.x m.vf
      (by simpa using S.x_weakEquivalence)
      (by simpa [hmX] using T.x_weakEquivalence)).2.2.1
  obtain ⟨r, hr⟩ := IsCylinderCategory.exists_retraction (C := C) m.vf hvfcof hvfwe
  let b : T.Af ⟶ X := r ≫ g.vf ≫ cyl.p
  let l₀ : T.A₀ ⟶ X := T.a ≫ b
  have hKaP : aK ≫ cyl.p = 𝟙 X := by
    simpa [aK, Category.assoc] using cyl.j₀_c_p
  have hl₀ : l₀ ≫ aK ≫ cyl.p = l₀ := by
    calc
      l₀ ≫ aK ≫ cyl.p = l₀ ≫ (aK ≫ cyl.p) := by simp [Category.assoc]
      _ = l₀ ≫ 𝟙 X := by rw [hKaP]
      _ = l₀ := by simp
  have hm₀l₀ : m.v₀ ≫ l₀ = g.v₀ := by
    dsimp [l₀, b]
    have hma : m.v₀ ≫ T.a = S.a ≫ m.vf := m.a_vf.symm
    have hmr := congrArg (fun z => S.a ≫ z ≫ g.vf ≫ cyl.p) hr
    have hga := congrArg (fun z => z ≫ cyl.p) g.a_vf
    calc
      m.v₀ ≫ T.a ≫ r ≫ g.vf ≫ cyl.p = S.a ≫ m.vf ≫ r ≫ g.vf ≫ cyl.p := by
        simpa [Category.assoc] using congrArg (fun z => z ≫ r ≫ g.vf ≫ cyl.p) hma
      _ = S.a ≫ g.vf ≫ cyl.p := by simpa [Category.assoc] using hmr
      _ = g.v₀ ≫ aK ≫ cyl.p := by simpa [hK_a, aK, cyl, Category.assoc] using hga
      _ = g.v₀ ≫ (aK ≫ cyl.p) := by simp [Category.assoc]
      _ = g.v₀ ≫ 𝟙 X := by rw [hKaP]
      _ = g.v₀ := Category.comp_id g.v₀
  have htopCond : S.a ≫ g.vf = m.v₀ ≫ (l₀ ≫ aK) := by
    have hga : S.a ≫ g.vf = g.v₀ ≫ aK := by simpa [hK_a, aK, cyl] using g.a_vf
    calc
      S.a ≫ g.vf = g.v₀ ≫ aK := hga
      _ = (m.v₀ ≫ l₀) ≫ aK := by rw [hm₀l₀]
      _ = m.v₀ ≫ (l₀ ≫ aK) := by simp [Category.assoc]
  let top : P ⟶ cyl.I := hP.desc g.vf (l₀ ≫ aK) htopCond
  have htopK : k ≫ top = g.vf := by simp [top, hP.inl_desc]
  have htopJ : j ≫ top = l₀ ≫ aK := by simp [top, hP.inr_desc]
  have hsq : latch ≫ b = top ≫ cyl.p := by
    apply hP.hom_ext
    · have hkb := congrArg (fun z => z ≫ b) hk
      have hrb := congrArg (fun z => z ≫ g.vf ≫ cyl.p) hr
      have htopKp := congrArg (fun z : S.Af ⟶ cyl.I => z ≫ cyl.p) htopK
      calc
        k ≫ latch ≫ b = m.vf ≫ b := by simpa [Category.assoc] using hkb
        _ = g.vf ≫ cyl.p := by simpa [b, Category.assoc] using hrb
        _ = k ≫ top ≫ cyl.p := by simpa [Category.assoc] using htopKp.symm
    · have hjb := congrArg (fun z => z ≫ b) hj
      have htopJp := congrArg (fun z : T.A₀ ⟶ cyl.I => z ≫ cyl.p) htopJ
      calc
        j ≫ latch ≫ b = T.a ≫ b := by simpa [Category.assoc] using hjb
        _ = l₀ := rfl
        _ = l₀ ≫ aK ≫ cyl.p := by rw [hl₀]
        _ = j ≫ top ≫ cyl.p := by simpa [Category.assoc] using htopJp.symm
  obtain ⟨l_f, hlatch⟩ :=
    semilifting_exact (C := C) latch hlatch cyl.p cyl.p_mem top b hsq
  have hA_vf : T.a ≫ l_f = l₀ ≫ aK := by
    have hhj := congrArg (fun z => z ≫ l_f) hj
    have hhl := congrArg (fun z => j ≫ z) hlatch
    calc
      T.a ≫ l_f = j ≫ latch ≫ l_f := by simpa [Category.assoc] using hhj.symm
      _ = j ≫ top := by simpa [Category.assoc] using hhl
      _ = l₀ ≫ aK := htopJ
  have hX_vf : T.x ≫ l_f = xK := by
    have hhm := congrArg (fun z => z ≫ l_f) hmX
    have hhk := congrArg (fun z => S.x ≫ z ≫ l_f) hk.symm
    have hhl := congrArg (fun z => S.x ≫ k ≫ z) hlatch
    have htopX := congrArg (fun z => S.x ≫ z) htopK
    calc
      T.x ≫ l_f = S.x ≫ m.vf ≫ l_f := by simpa [Category.assoc] using hhm.symm
      _ = S.x ≫ k ≫ latch ≫ l_f := by simpa [Category.assoc] using hhk
      _ = S.x ≫ k ≫ top := by simpa [Category.assoc] using hhl
      _ = S.x ≫ g.vf := by simpa [Category.assoc] using htopX
      _ = xK := by simpa [hK_x] using g.x_vf
  refine ⟨⟨l₀, l_f, hA_vf, hX_vf⟩, ?_⟩
  apply SliceObj.Hom.ext
  · exact hm₀l₀
  · have hhk := congrArg (fun z => z ≫ l_f) hk.symm
    have hhl := congrArg (fun z => k ≫ z) hlatch
    calc
      m.vf ≫ l_f = k ≫ latch ≫ l_f := by simpa [Category.assoc] using hhk
      _ = k ≫ top := by simpa [Category.assoc] using hhl
      _ = g.vf := htopK

noncomputable def relativeCylinderOfCofibration [IsCylinderCategory C]
    {A B : C} (i : A ⟶ B) (hi : cofibrations C i) : RelativeCylinder i := by
  have hcof := (inferInstance : IsCofibrationCategory C)
  letI : HasPushout i i := hcof.hasPushout i i hi
  let P := pushout i i
  let j₀ : B ⟶ P := pushout.inl i i
  let j₁ : B ⟶ P := pushout.inr i i
  let diag : P ⟶ B := pushout.desc (𝟙 B) (𝟙 B) (by simp)
  let hfac := brown_factorization (C := C) diag
  let J := Classical.choose hfac
  have hfac₁ := Classical.choose_spec hfac
  let c := Classical.choose hfac₁
  have hfac₂ := Classical.choose_spec hfac₁
  let p := Classical.choose hfac₂
  have hfac₃ := Classical.choose_spec hfac₂
  have hc := hfac₃.1
  have hp := hfac₃.2.1
  have hcp : c ≫ p = diag := hfac₃.2.2
  refine ⟨P, j₀, j₁, IsPushout.of_hasPushout i i, J, c, p, hc, hp, ?_, ?_⟩
  · calc
      j₀ ≫ c ≫ p = j₀ ≫ diag := by rw [hcp]
      _ = 𝟙 B := by
        dsimp [diag, j₀]
        change pushout.inl i i ≫ pushout.desc (𝟙 B) (𝟙 B) _ = 𝟙 B
        exact pushout.inl_desc (𝟙 B) (𝟙 B) (by simp)
  · calc
      j₁ ≫ c ≫ p = j₁ ≫ diag := by rw [hcp]
      _ = 𝟙 B := by
        dsimp [diag, j₁]
        change pushout.inr i i ≫ pushout.desc (𝟙 B) (𝟙 B) _ = 𝟙 B
        exact pushout.inr_desc (𝟙 B) (𝟙 B) (by simp)

theorem homotopic_precomp [IsCylinderCategory C] {X Y Z : C} (k : X ⟶ Y)
    {f g : Y ⟶ Z} (hfg : Homotopic f g) : Homotopic (k ≫ f) (k ≫ g) := by
  rcases hfg with ⟨I, hI, cylY, H, h₀, h₁⟩
  obtain ⟨J, ⟨hJ⟩⟩ := IsCofibrationCategory.exists_initial (C := C)
  let cylX : RelativeCylinder (hJ.to X) := Classical.choice
    (IsCylinderCategory.exists_cylinder (C := C) hJ X)
  let top : cylX.P ⟶ cylY.I := cylX.isPushout.desc
    (k ≫ cylY.j₀ ≫ cylY.c) (k ≫ cylY.j₁ ≫ cylY.c) (by apply hJ.hom_ext)
  have htop₀ : cylX.j₀ ≫ top = k ≫ cylY.j₀ ≫ cylY.c := by
    exact cylX.isPushout.inl_desc _ _ _
  have htop₁ : cylX.j₁ ≫ top = k ≫ cylY.j₁ ≫ cylY.c := by
    exact cylX.isPushout.inr_desc _ _ _
  have hY₀ : cylY.j₀ ≫ cylY.c ≫ cylY.p = 𝟙 Y := by
    simpa [Category.assoc] using cylY.j₀_c_p
  have hY₁ : cylY.j₁ ≫ cylY.c ≫ cylY.p = 𝟙 Y := by
    simpa [Category.assoc] using cylY.j₁_c_p
  have hRight₀ : cylX.j₀ ≫ top ≫ cylY.p = k := by
    have h := congrArg (fun z => z ≫ cylY.p) htop₀
    have hk := congrArg (fun z => k ≫ z) hY₀
    calc
      cylX.j₀ ≫ top ≫ cylY.p = (cylX.j₀ ≫ top) ≫ cylY.p := by simp [Category.assoc]
      _ = (k ≫ cylY.j₀ ≫ cylY.c) ≫ cylY.p := by simpa [Category.assoc] using h
      _ = k := by simpa [Category.assoc] using hk
  have hRight₁ : cylX.j₁ ≫ top ≫ cylY.p = k := by
    have h := congrArg (fun z => z ≫ cylY.p) htop₁
    have hk := congrArg (fun z => k ≫ z) hY₁
    calc
      cylX.j₁ ≫ top ≫ cylY.p = (cylX.j₁ ≫ top) ≫ cylY.p := by simp [Category.assoc]
      _ = (k ≫ cylY.j₁ ≫ cylY.c) ≫ cylY.p := by simpa [Category.assoc] using h
      _ = k := by simpa [Category.assoc] using hk
  have hsq : cylX.c ≫ (cylX.p ≫ k) = top ≫ cylY.p := by
    apply cylX.isPushout.hom_ext
    · have hleft := congrArg (fun z => z ≫ k) cylX.j₀_c_p
      have hleft' : cylX.j₀ ≫ cylX.c ≫ (cylX.p ≫ k) = k := by
        simpa [Category.assoc] using hleft
      exact hleft'.trans hRight₀.symm
    · have hleft := congrArg (fun z => z ≫ k) cylX.j₁_c_p
      have hleft' : cylX.j₁ ≫ cylX.c ≫ (cylX.p ≫ k) = k := by
        simpa [Category.assoc] using hleft
      exact hleft'.trans hRight₁.symm
  obtain ⟨l, hl⟩ := semilifting_exact (C := C) cylX.c cylX.c_mem cylY.p
    cylY.p_mem top (cylX.p ≫ k) hsq
  refine ⟨J, hJ, cylX, l ≫ H, ?_, ?_⟩
  · have hleft : cylX.j₀ ≫ cylX.c ≫ l = cylX.j₀ ≫ top := by
      simpa [Category.assoc] using congrArg (fun z => cylX.j₀ ≫ z) hl
    have hleftH := congrArg (fun z => z ≫ H) hleft
    have htopH := congrArg (fun z => z ≫ H) htop₀
    calc
      cylX.j₀ ≫ cylX.c ≫ l ≫ H = (cylX.j₀ ≫ cylX.c ≫ l) ≫ H := by simp [Category.assoc]
      _ = (cylX.j₀ ≫ top) ≫ H := by simpa [Category.assoc] using hleftH
      _ = (k ≫ cylY.j₀ ≫ cylY.c) ≫ H := by simpa [Category.assoc] using htopH
      _ = k ≫ f := by
        calc
          (k ≫ cylY.j₀ ≫ cylY.c) ≫ H = k ≫ (cylY.j₀ ≫ cylY.c ≫ H) := by
            simp [Category.assoc]
          _ = k ≫ f := by rw [h₀]
  · have hright : cylX.j₁ ≫ cylX.c ≫ l = cylX.j₁ ≫ top := by
      simpa [Category.assoc] using congrArg (fun z => cylX.j₁ ≫ z) hl
    have hrightH := congrArg (fun z => z ≫ H) hright
    have htopH := congrArg (fun z => z ≫ H) htop₁
    calc
      cylX.j₁ ≫ cylX.c ≫ l ≫ H = (cylX.j₁ ≫ cylX.c ≫ l) ≫ H := by simp [Category.assoc]
      _ = (cylX.j₁ ≫ top) ≫ H := by simpa [Category.assoc] using hrightH
      _ = (k ≫ cylY.j₁ ≫ cylY.c) ≫ H := by simpa [Category.assoc] using htopH
      _ = k ≫ g := by
        calc
          (k ≫ cylY.j₁ ≫ cylY.c) ≫ H = k ≫ (cylY.j₁ ≫ cylY.c ≫ H) := by
            simp [Category.assoc]
          _ = k ≫ g := by rw [h₁]

theorem homotopy_extension [IsCylinderCategory C] {A B Y : C} (i : A ⟶ B)
    (hi : cofibrations C i) (f : B ⟶ Y) {g : A ⟶ Y}
    (h : Homotopic (i ≫ f) g) : ∃ f' : B ⟶ Y, i ≫ f' = g := by
  rcases h with ⟨I, hI, cyl, H, h₀, h₁⟩
  have hcof := (inferInstance : IsCofibrationCategory C)
  letI : (cofibrations C).IsStableUnderCobaseChange := hcof.isStableUnderCobaseChange
  have hj₀ : cofibrations C (cyl.j₀ ≫ cyl.c) := by
    have h0A := hcof.initial_cofibration hI A
    have hj₀' : cofibrations C cyl.j₀ :=
      MorphismProperty.IsStableUnderCobaseChange.of_isPushout cyl.isPushout h0A
    exact hcof.isMultiplicative.comp_mem cyl.j₀ cyl.c hj₀' cyl.c_mem
  have h₀we : weakEquivalences C (cyl.j₀ ≫ cyl.c) := by
    have hc : (cyl.j₀ ≫ cyl.c) ≫ cyl.p = 𝟙 A := by
      simpa [Category.assoc] using cyl.j₀_c_p
    exact (IsCylinderCategory.twoOutOfSix (C := C)
      (cyl.j₀ ≫ cyl.c) cyl.p (𝟙 A)
      (by simpa [hc] using
        (IsCylinderCategory.weakEquivalences_isMultiplicative (C := C)).id_mem A)
      (by simpa using cyl.p_mem)).1
  letI : HasPushout (cyl.j₀ ≫ cyl.c) i := hcof.hasPushout _ _ hj₀
  let P := pushout (cyl.j₀ ≫ cyl.c) i
  let inI : cyl.I ⟶ P := pushout.inl (cyl.j₀ ≫ cyl.c) i
  let inB : B ⟶ P := pushout.inr (cyl.j₀ ≫ cyl.c) i
  have hInB : cofibrations C inB :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout
      (IsPushout.of_hasPushout (cyl.j₀ ≫ cyl.c) i).flip hj₀
  have hInBwe : weakEquivalences C inB :=
    IsCylinderCategory.trivialCofibration_cobaseChange (C := C)
      (cyl.j₀ ≫ cyl.c) i inI inB (IsPushout.of_hasPushout (cyl.j₀ ≫ cyl.c) i)
      hj₀ h₀we
  have hcyl₀ : (cyl.j₀ ≫ cyl.c) ≫ cyl.p = 𝟙 A := by
    simpa [Category.assoc] using cyl.j₀_c_p
  have hcompat : (cyl.j₀ ≫ cyl.c) ≫ (cyl.p ≫ i) = i ≫ 𝟙 B := by
    calc
      (cyl.j₀ ≫ cyl.c) ≫ (cyl.p ≫ i) = ((cyl.j₀ ≫ cyl.c) ≫ cyl.p) ≫ i := by
        simp [Category.assoc]
      _ = (𝟙 A) ≫ i := by rw [hcyl₀]
      _ = i ≫ 𝟙 B := by simp
  let r : P ⟶ B := pushout.desc (cyl.p ≫ i) (𝟙 B) (by
    exact hcompat)
  have hr : inB ≫ r = 𝟙 B := by
    dsimp [r, inB]
    exact pushout.inr_desc (cyl.p ≫ i) (𝟙 B) hcompat
  have hInIr : inI ≫ r = cyl.p ≫ i := by
    dsimp [r, inI]
    exact pushout.inl_desc (cyl.p ≫ i) (𝟙 B) hcompat
  have hrwe : weakEquivalences C r := by
    exact (IsCylinderCategory.twoOutOfSix (C := C) (𝟙 B) inB r
      (by simpa using hInBwe)
      (by simpa [hr] using
        (IsCylinderCategory.weakEquivalences_isMultiplicative (C := C)).id_mem B)).2.2.1
  let u : A ⟶ P := (cyl.j₁ ≫ cyl.c) ≫ inI
  have hcyl₁ : (cyl.j₁ ≫ cyl.c) ≫ cyl.p = 𝟙 A := by
    simpa [Category.assoc] using cyl.j₁_c_p
  have hui : u ≫ r = i := by
    dsimp [u]
    calc
      ((cyl.j₁ ≫ cyl.c) ≫ inI) ≫ r =
          (cyl.j₁ ≫ cyl.c) ≫ (inI ≫ r) := Category.assoc _ _ _
      _ = (cyl.j₁ ≫ cyl.c) ≫ (cyl.p ≫ i) := by rw [hInIr]
      _ = ((cyl.j₁ ≫ cyl.c) ≫ cyl.p) ≫ i := by simp [Category.assoc]
      _ = (𝟙 A) ≫ i := by rw [hcyl₁]
      _ = i := by simp
  obtain ⟨s, hsi⟩ := semilifting_exact (C := C) i hi r hrwe u (𝟙 B) (by
    simpa [hui])
  have h₀' : (cyl.j₀ ≫ cyl.c) ≫ H = i ≫ f := by
    simpa [Category.assoc] using h₀
  let extObj : P ⟶ Y := pushout.desc H f h₀'
  have hInIExt : inI ≫ extObj = H := by
    dsimp [extObj, inI]
    exact pushout.inl_desc H f h₀'
  refine ⟨s ≫ extObj, ?_⟩
  have hExt : i ≫ s ≫ extObj = u ≫ extObj := by
    simpa [Category.assoc] using congrArg (fun z => z ≫ extObj) hsi
  calc
    i ≫ s ≫ extObj = u ≫ extObj := hExt
    _ = ((cyl.j₁ ≫ cyl.c) ≫ inI) ≫ extObj := by rfl
    _ = (cyl.j₁ ≫ cyl.c) ≫ (inI ≫ extObj) := by simp [Category.assoc]
    _ = (cyl.j₁ ≫ cyl.c) ≫ H := by rw [hInIExt]
    _ = g := by simpa [Category.assoc] using h₁

theorem isHTerminal_of_weakEquivalence [IsCylinderCategory C] {X Y : C}
    (f : X ⟶ Y) (hf : weakEquivalences C f) (hX : IsHTerminal X) :
    IsHTerminal Y := by
  obtain ⟨g, hfg, hgf⟩ :=
    (HomotopyHypothesis.Henry.Packages.weakEquivalence_iff (C := C) f).mp hf
  intro A B i hi u
  obtain ⟨v, hiv⟩ := hX i hi (u ≫ g)
  have hhom : Homotopic (i ≫ (v ≫ f)) u := by
    have hp := homotopic_precomp u hgf
    have hdom : i ≫ (v ≫ f) = u ≫ g ≫ f := by
      calc
        i ≫ (v ≫ f) = (i ≫ v) ≫ f := by simp [Category.assoc]
        _ = (u ≫ g) ≫ f := by rw [hiv]
        _ = u ≫ g ≫ f := by simp [Category.assoc]
    rw [hdom]
    simpa using hp
  exact homotopy_extension i hi (v ≫ f) hhom

theorem homotopic_of_isHTerminal [IsCylinderCategory C] {X Y : C}
    (hY : IsHTerminal Y) (f g : X ⟶ Y) : Homotopic f g := by
  obtain ⟨I, ⟨hI⟩⟩ := IsCofibrationCategory.exists_initial (C := C)
  let cyl : RelativeCylinder (hI.to X) := Classical.choice
    (IsCylinderCategory.exists_cylinder (C := C) hI X)
  have hcof := (inferInstance : IsCofibrationCategory C)
  letI : (cofibrations C).IsStableUnderCobaseChange := hcof.isStableUnderCobaseChange
  letI : (cofibrations C).IsMultiplicative := hcof.isMultiplicative
  let boundary : cyl.P ⟶ Y := cyl.isPushout.desc f g (by apply hI.hom_ext)
  obtain ⟨H, hH⟩ := hY cyl.c cyl.c_mem boundary
  refine ⟨I, hI, cyl, H, ?_, ?_⟩
  · calc
      cyl.j₀ ≫ cyl.c ≫ H = cyl.j₀ ≫ (cyl.c ≫ H) := by simp [Category.assoc]
      _ = cyl.j₀ ≫ boundary := by rw [hH]
      _ = f := by simpa [boundary] using cyl.isPushout.inl_desc f g (by apply hI.hom_ext)
  · calc
      cyl.j₁ ≫ cyl.c ≫ H = cyl.j₁ ≫ (cyl.c ≫ H) := by simp [Category.assoc]
      _ = cyl.j₁ ≫ boundary := by rw [hH]
      _ = g := by simpa [boundary] using cyl.isPushout.inr_desc f g (by apply hI.hom_ext)

theorem weakEquivalence_of_isHTerminal [IsCylinderCategory C] {X Y : C}
    (f : X ⟶ Y) (hX : IsHTerminal X) (hY : IsHTerminal Y) :
    weakEquivalences C f := by
  obtain ⟨I, ⟨hI⟩⟩ := IsCofibrationCategory.exists_initial (C := C)
  have hi : cofibrations C (hI.to Y) :=
    (inferInstance : IsCofibrationCategory C).initial_cofibration hI Y
  obtain ⟨g, _⟩ := hX (hI.to Y) hi (hI.to X)
  exact (HomotopyHypothesis.Henry.Packages.weakEquivalence_iff (C := C) f).2
    ⟨g, homotopic_of_isHTerminal hX (f ≫ g) (𝟙 X),
      homotopic_of_isHTerminal hY (g ≫ f) (𝟙 Y)⟩

theorem sliceObj_map_isWeakEquivalence_of_isHTerminal [IsCylinderCategory C]
    {X : C} (A : SliceObj X) (hA : IsHTerminal A) : weakEquivalences C A.a := by
  letI : IsCylinderCategory (SliceObj X) :=
    (HomotopyHypothesis.Henry.Packages.sliceObj_isLiftingTarget X).1
  let d := chooseSliceCylinder X
  let J := cylinderSliceObjOfData X d
  have hJ : IsHTerminal J := cylinderSliceData_isHTerminal X d
  obtain ⟨I, ⟨hI⟩⟩ := IsCofibrationCategory.exists_initial (C := SliceObj X)
  have hi : cofibrations (SliceObj X) (hI.to A) :=
    (inferInstance : IsCofibrationCategory (SliceObj X)).initial_cofibration hI A
  obtain ⟨m, _⟩ := hJ (hI.to A) hi (hI.to J)
  have hm : weakEquivalences (SliceObj X) m :=
    weakEquivalence_of_isHTerminal (C := SliceObj X) m hA hJ
  have hm₀ : weakEquivalences C m.v₀ := hm
  have hJa : weakEquivalences C J.a := by
    change weakEquivalences C (d.cyl.j₀ ≫ d.cyl.c)
    have hcomp : (d.cyl.j₀ ≫ d.cyl.c) ≫ d.cyl.p = 𝟙 X := by
      simpa [Category.assoc] using d.cyl.j₀_c_p
    exact (IsCylinderCategory.twoOutOfSix (C := C)
      (d.cyl.j₀ ≫ d.cyl.c) d.cyl.p (𝟙 X)
      (by simpa [hcomp] using
        (IsCylinderCategory.weakEquivalences_isMultiplicative (C := C)).id_mem X)
      (by simpa using d.cyl.p_mem)).1
  have hJx : weakEquivalences C J.x := J.x_weakEquivalence
  have hmvf : weakEquivalences C m.vf := by
    have hcomp : weakEquivalences C (A.x ≫ m.vf) := by rw [m.x_vf]; exact hJx
    exact (IsCylinderCategory.twoOutOfSix (C := C)
      (𝟙 X) A.x m.vf
      (by simpa using A.x_weakEquivalence)
      hcomp).2.2.1
  have hrhs : weakEquivalences C (m.v₀ ≫ J.a) :=
    (IsCylinderCategory.weakEquivalences_isMultiplicative (C := C)).comp_mem _ _ hm₀ hJa
  have hcomp : weakEquivalences C (A.a ≫ m.vf) := by rw [m.a_vf]; exact hrhs
  have hmvfId : weakEquivalences C (m.vf ≫ 𝟙 J.Af) := by simpa using hmvf
  exact (IsCylinderCategory.twoOutOfSix (C := C)
    A.a m.vf (𝟙 J.Af) hcomp
    hmvfId).1

theorem map_isCofibrantPair [IsCofibrationCategory C] {D : Type u'} [Category.{v'} D]
    [CategoryWithCofibrations D] [CategoryWithWeakEquivalences D]
    {F : C ⥤ D} (hF : IsCylinderMorphism F) {B X T : C}
    {u : B ⟶ T} {w : X ⟶ T} (h : IsCofibrantPair u w) :
    IsCofibrantPair (F.map u) (F.map w) := by
  rcases h with ⟨I, hI, P, k, j, hP, m, hkm, hjm, hm⟩
  obtain ⟨hFI⟩ := hF.map_initial hI
  have hIB : hFI.to (F.obj B) = F.map (hI.to B) := by
    apply hFI.hom_ext
  have hIX : hFI.to (F.obj X) = F.map (hI.to X) := by
    apply hFI.hom_ext
  have hP' := hF.map_isPushout (hI.to B) (hI.to X) k j hP
    ((inferInstance : IsCofibrationCategory C).initial_cofibration hI B)
  refine ⟨F.obj I, hFI, F.obj P, F.map k, F.map j, ?_, F.map m, ?_, ?_,
    hF.map_cofibration m hm⟩
  · simpa [hIB, hIX] using hP'
  · calc
      F.map k ≫ F.map m = F.map (k ≫ m) := (F.map_comp _ _).symm
      _ = F.map u := congrArg F.map hkm
  · calc
      F.map j ≫ F.map m = F.map (j ≫ m) := (F.map_comp _ _).symm
      _ = F.map w := congrArg F.map hjm

theorem cofibrations_left_of_isCofibrantPair [IsCofibrationCategory C]
    {B X T : C} {u : B ⟶ T} {w : X ⟶ T} (h : IsCofibrantPair u w) :
    cofibrations C u := by
  rcases h with ⟨I, hI, P, k, j, hP, m, hkm, hjm, hm⟩
  have hcof := (inferInstance : IsCofibrationCategory C)
  letI : (cofibrations C).IsStableUnderCobaseChange := hcof.isStableUnderCobaseChange
  letI : (cofibrations C).IsMultiplicative := hcof.isMultiplicative
  have hk : cofibrations C k :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout hP
      (hcof.initial_cofibration hI X)
  simpa [hkm] using hcof.isMultiplicative.comp_mem k m hk hm

theorem cofibrations_right_of_isCofibrantPair [IsCofibrationCategory C]
    {B X T : C} {u : B ⟶ T} {w : X ⟶ T} (h : IsCofibrantPair u w) :
    cofibrations C w := by
  rcases h with ⟨I, hI, P, k, j, hP, m, hkm, hjm, hm⟩
  have hcof := (inferInstance : IsCofibrationCategory C)
  letI : (cofibrations C).IsStableUnderCobaseChange := hcof.isStableUnderCobaseChange
  letI : (cofibrations C).IsMultiplicative := hcof.isMultiplicative
  have hj : cofibrations C j :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout hP.flip
      (hcof.initial_cofibration hI B)
  simpa [hjm] using hcof.isMultiplicative.comp_mem j m hj hm

theorem map_isCofibrantGluing {D : Type u'} [Category.{v'} D]
    [CategoryWithCofibrations D] [CategoryWithWeakEquivalences D]
    {F : C ⥤ D} (hF : IsCylinderMorphism F) {A B X T : C}
    {i : A ⟶ B} {f : A ⟶ X} {k : B ⟶ T} {j : X ⟶ T}
    (hi : cofibrations C i)
    (h : IsCofibrantGluing i f k j) :
    IsCofibrantGluing (F.map i) (F.map f) (F.map k) (F.map j) := by
  rcases h with ⟨P, k', j', hP, m, hkm, hjm, hm⟩
  have hP' := hF.map_isPushout i f k' j' hP hi
  refine ⟨F.obj P, F.map k', F.map j', hP', F.map m, ?_, ?_, hF.map_cofibration m hm⟩
  · calc
      F.map k' ≫ F.map m = F.map (k' ≫ m) := (F.map_comp _ _).symm
      _ = F.map k := congrArg F.map hkm
  · calc
      F.map j' ≫ F.map m = F.map (j' ≫ m) := (F.map_comp _ _).symm
      _ = F.map j := congrArg F.map hjm

noncomputable def initialSliceObjOfInitial [IsCylinderCategory C] {X I : C}
    (hI : IsInitial I) : SliceObj X := by
  have hId : hI.to I = 𝟙 I := hI.hom_ext _ _
  haveI : IsIso (hI.to I) := by rw [hId]; infer_instance
  letI : HasPushout (hI.to I) (hI.to X) := hasPushout_of_left_iso _ _
  let P := pushout (hI.to I) (hI.to X)
  let k := pushout.inl (hI.to I) (hI.to X)
  let j := pushout.inr (hI.to I) (hI.to X)
  let m := inv j
  have hP : IsPushout (hI.to I) (hI.to X) k j := IsPushout.of_hasPushout _ _
  have hkm : k ≫ m = hI.to X := by
    dsimp [m, k]
    rw [pushout_inl_inv_inr_of_right_isIso]
    simpa [hId]
  have hjm : j ≫ m = 𝟙 X := by simp [m, j]
  have hmcof : cofibrations C m :=
    (inferInstance : IsCofibrationCategory C).isomorphisms_le m (by infer_instance)
  have hPair : IsCofibrantPair (hI.to X) (𝟙 X) := by
    exact ⟨I, hI, P, k, j, hP, m, hkm, hjm, hmcof⟩
  exact
    { A₀ := I
      Af := X
      a := hI.to X
      x := 𝟙 X
      cofibrant := hPair
      x_cofibration :=
        (inferInstance : IsCofibrationCategory C).isomorphisms_le (𝟙 X) (by infer_instance)
      x_weakEquivalence :=
        (IsCylinderCategory.weakEquivalences_isMultiplicative (C := C)).id_mem X }

noncomputable def initialSliceObjOfInitial_isInitial [IsCylinderCategory C] {X I : C}
    (hI : IsInitial I) : IsInitial (initialSliceObjOfInitial (X := X) hI) := by
  let homOut (A : SliceObj X) : initialSliceObjOfInitial (X := X) hI ⟶ A :=
    ⟨hI.to A.A₀, A.x, hI.hom_ext _ _, by simp [initialSliceObjOfInitial]⟩
  exact IsInitial.ofUniqueHom homOut (by
    intro A m
    apply SliceObj.Hom.ext
    · exact hI.hom_ext _ _
    · have hm : m.vf = A.x := by
        simpa [initialSliceObjOfInitial] using m.x_vf
      have hto : (homOut A).vf = A.x := rfl
      exact hm.trans hto.symm)

def sliceMap {D : Type u'} [Category.{v'} D] [CategoryWithCofibrations D]
    [CategoryWithWeakEquivalences D] [IsCylinderCategory C] {F : C ⥤ D}
    (hF : IsCylinderMorphism F) (X : C) : SliceObj X ⥤ SliceObj (F.obj X) where
  obj A :=
    { A₀ := F.obj A.A₀
      Af := F.obj A.Af
      a := F.map A.a
      x := F.map A.x
      cofibrant := map_isCofibrantPair hF A.cofibrant
      x_cofibration := hF.map_cofibration A.x A.x_cofibration
      x_weakEquivalence := hF.map_weakEquivalence A.x A.x_weakEquivalence }
  map {A B} f :=
    { v₀ := F.map f.v₀
      vf := F.map f.vf
      a_vf := by simpa only [Functor.map_comp] using congrArg F.map f.a_vf
      x_vf := by simpa only [Functor.map_comp] using congrArg F.map f.x_vf }
  map_id A := by
    apply SliceObj.Hom.ext
    · change F.map (𝟙 A.A₀) = 𝟙 (F.obj A.A₀)
      simp
    · change F.map (𝟙 A.Af) = 𝟙 (F.obj A.Af)
      simp
  map_comp f g := by
    apply SliceObj.Hom.ext
    · change F.map (f.v₀ ≫ g.v₀) = F.map f.v₀ ≫ F.map g.v₀
      simp
    · change F.map (f.vf ≫ g.vf) = F.map f.vf ≫ F.map g.vf
      simp

theorem sliceMap_mapInitial [IsCylinderCategory C] {D : Type (u + 1)} [Category.{u} D]
    [CategoryWithCofibrations D] [CategoryWithWeakEquivalences D] [IsCylinderCategory D]
    {F : C ⥤ D} (hF : IsCylinderMorphism F) (X : C) {I : SliceObj X}
    (hI : IsInitial I) : Nonempty (IsInitial ((sliceMap hF X).obj I)) := by
  obtain ⟨J, hJ⟩ := IsCofibrationCategory.exists_initial (C := C)
  obtain ⟨hJ⟩ := hJ
  obtain ⟨hFJ⟩ := hF.map_initial hJ
  let S := initialSliceObjOfInitial (X := X) hJ
  have hS : IsInitial S := initialSliceObjOfInitial_isInitial hJ
  let U := (sliceMap hF X).obj S
  let t : U.Af ⟶ F.obj X := F.map (𝟙 X)
  have hUx : U.x ≫ t = 𝟙 (F.obj X) := by
    simp [t, U, sliceMap, S, initialSliceObjOfInitial]
  have htU : t ≫ U.x = 𝟙 U.Af := by
    simp [t, U, sliceMap, S, initialSliceObjOfInitial]
  have hU : IsInitial U := by
    have ha : U.a ≫ t = hFJ.to (F.obj X) := hFJ.hom_ext _ _
    let homOut (A : SliceObj (F.obj X)) : U ⟶ A :=
      { v₀ := hFJ.to A.A₀
        vf := t ≫ A.x
        a_vf := by
          rw [← Category.assoc, ha]
          exact hFJ.hom_ext _ _
        x_vf := by
          rw [← Category.assoc, hUx]
          simp }
    exact IsInitial.ofUniqueHom homOut (by
      intro A m
      apply SliceObj.Hom.ext
      · exact hFJ.hom_ext _ _
      · calc
          m.vf = 𝟙 U.Af ≫ m.vf := by simp
          _ = (t ≫ U.x) ≫ m.vf := by rw [htU]
          _ = t ≫ (U.x ≫ m.vf) := by simp [Category.assoc]
          _ = t ≫ A.x := by rw [m.x_vf]
          _ = (homOut A).vf := rfl)
  let e1 : U ≅ (sliceMap hF X).obj I :=
    (sliceMap hF X).mapIso (hS.uniqueUpToIso hI)
  exact ⟨IsInitial.ofIso hU e1⟩

theorem sliceObj_isPushout_of_componentwise {X : C}
    {A₁ B₁ C₁ P₁ : SliceObj X} (i : A₁ ⟶ B₁) (f : A₁ ⟶ C₁)
    (k : B₁ ⟶ P₁) (j : C₁ ⟶ P₁) (hcomm : i ≫ k = f ≫ j)
    (h₀ : IsPushout i.v₀ f.v₀ k.v₀ j.v₀)
    (h_f : IsPushout i.vf f.vf k.vf j.vf) : IsPushout i f k j := by
  let desc (s : PushoutCocone i f) : P₁ ⟶ s.pt := by
    have hs₀ : i.v₀ ≫ s.inl.v₀ = f.v₀ ≫ s.inr.v₀ := by
      change (i ≫ s.inl).v₀ = (f ≫ s.inr).v₀
      exact congrArg SliceObj.Hom.v₀ s.condition
    have hsf : i.vf ≫ s.inl.vf = f.vf ≫ s.inr.vf := by
      change (i ≫ s.inl).vf = (f ≫ s.inr).vf
      exact congrArg SliceObj.Hom.vf s.condition
    let v₀ := h₀.desc s.inl.v₀ s.inr.v₀ hs₀
    let vf := h_f.desc s.inl.vf s.inr.vf hsf
    refine ⟨v₀, vf, ?_, ?_⟩
    · apply h₀.hom_ext
      · calc
          k.v₀ ≫ P₁.a ≫ vf = (k.v₀ ≫ P₁.a) ≫ vf := by simp [Category.assoc]
          _ = (B₁.a ≫ k.vf) ≫ vf := by rw [k.a_vf]
          _ = B₁.a ≫ (k.vf ≫ vf) := by simp [Category.assoc]
          _ = B₁.a ≫ s.inl.vf := by rw [h_f.inl_desc]
          _ = s.inl.v₀ ≫ s.pt.a := s.inl.a_vf
          _ = (k.v₀ ≫ v₀) ≫ s.pt.a := by rw [h₀.inl_desc]
          _ = k.v₀ ≫ v₀ ≫ s.pt.a := by simp [Category.assoc]
      · calc
          j.v₀ ≫ P₁.a ≫ vf = (j.v₀ ≫ P₁.a) ≫ vf := by simp [Category.assoc]
          _ = (C₁.a ≫ j.vf) ≫ vf := by rw [j.a_vf]
          _ = C₁.a ≫ (j.vf ≫ vf) := by simp [Category.assoc]
          _ = C₁.a ≫ s.inr.vf := by rw [h_f.inr_desc]
          _ = s.inr.v₀ ≫ s.pt.a := s.inr.a_vf
          _ = (j.v₀ ≫ v₀) ≫ s.pt.a := by rw [h₀.inr_desc]
          _ = j.v₀ ≫ v₀ ≫ s.pt.a := by simp [Category.assoc]
    · calc
        P₁.x ≫ vf = (B₁.x ≫ k.vf) ≫ vf := by rw [← k.x_vf]
        _ = B₁.x ≫ (k.vf ≫ vf) := by simp [Category.assoc]
        _ = B₁.x ≫ s.inl.vf := by rw [h_f.inl_desc]
        _ = s.pt.x := s.inl.x_vf
  have hfac₀ (s : PushoutCocone i f) : k.v₀ ≫ (desc s).v₀ = s.inl.v₀ := by
    dsimp [desc]
    exact h₀.inl_desc _ _ _
  have hfac₀' (s : PushoutCocone i f) : j.v₀ ≫ (desc s).v₀ = s.inr.v₀ := by
    dsimp [desc]
    exact h₀.inr_desc _ _ _
  have hfacf (s : PushoutCocone i f) : k.vf ≫ (desc s).vf = s.inl.vf := by
    dsimp [desc]
    exact h_f.inl_desc _ _ _
  have hfacf' (s : PushoutCocone i f) : j.vf ≫ (desc s).vf = s.inr.vf := by
    dsimp [desc]
    exact h_f.inr_desc _ _ _
  refine ⟨⟨hcomm⟩, ⟨PushoutCocone.IsColimit.mk hcomm desc ?_ ?_ ?_⟩⟩
  · intro s
    apply SliceObj.Hom.ext
    · exact hfac₀ s
    · exact hfacf s
  · intro s
    apply SliceObj.Hom.ext
    · exact hfac₀' s
    · exact hfacf' s
  · intro s m hm₀ hm₁
    apply SliceObj.Hom.ext
    · apply h₀.hom_ext
      · calc
          k.v₀ ≫ m.v₀ = s.inl.v₀ := by
            change (k ≫ m).v₀ = s.inl.v₀
            exact congrArg SliceObj.Hom.v₀ hm₀
          _ = k.v₀ ≫ (desc s).v₀ := (hfac₀ s).symm
      · calc
          j.v₀ ≫ m.v₀ = s.inr.v₀ := by
            change (j ≫ m).v₀ = s.inr.v₀
            exact congrArg SliceObj.Hom.v₀ hm₁
          _ = j.v₀ ≫ (desc s).v₀ := (hfac₀' s).symm
    · apply h_f.hom_ext
      · calc
          k.vf ≫ m.vf = s.inl.vf := by
            change (k ≫ m).vf = s.inl.vf
            exact congrArg SliceObj.Hom.vf hm₀
          _ = k.vf ≫ (desc s).vf := (hfacf s).symm
      · calc
          j.vf ≫ m.vf = s.inr.vf := by
            change (j ≫ m).vf = s.inr.vf
            exact congrArg SliceObj.Hom.vf hm₁
          _ = j.vf ≫ (desc s).vf := (hfacf' s).symm

theorem pushout_coproduct_baseChange [IsCylinderCategory C]
    {I C₀ P₀ X Q₀ Q : C} (hI : IsInitial I)
    (k : C₀ ⟶ Q) (j : X ⟶ Q) (hQ : IsPushout (hI.to C₀) (hI.to X) k j)
    (k₀ : P₀ ⟶ Q₀) (j₀ : X ⟶ Q₀)
    (hQ₀ : IsPushout (hI.to P₀) (hI.to X) k₀ j₀) (e : C₀ ⟶ P₀) :
    ∃ q : Q ⟶ Q₀, IsPushout k e q k₀ ∧ k ≫ q = e ≫ k₀ ∧ j ≫ q = j₀ := by
  have hcompat : hI.to C₀ ≫ e ≫ k₀ = hI.to X ≫ j₀ := hI.hom_ext _ _
  let q := hQ.desc (e ≫ k₀) j₀ hcompat
  have hcomm : k ≫ q = e ≫ k₀ := hQ.inl_desc _ _ hcompat
  have hjq : j ≫ q = j₀ := hQ.inr_desc _ _ hcompat
  have hcol : IsColimit (PushoutCocone.mk q k₀ hcomm) := by
    let desc (s : PushoutCocone k e) : Q₀ ⟶ s.pt :=
      hQ₀.desc s.inr (j ≫ s.inl) (by apply hI.hom_ext)
    have hfac₀ (s : PushoutCocone k e) : k₀ ≫ desc s = s.inr := by
      dsimp [desc]
      exact hQ₀.inl_desc _ _ _
    have hfac₁ (s : PushoutCocone k e) : j₀ ≫ desc s = j ≫ s.inl := by
      dsimp [desc]
      exact hQ₀.inr_desc _ _ _
    have hdesc (s : PushoutCocone k e) : q ≫ desc s = s.inl := by
      apply hQ.hom_ext
      · calc
          k ≫ q ≫ desc s = (k ≫ q) ≫ desc s := (Category.assoc _ _ _).symm
          _ = (e ≫ k₀) ≫ desc s := by rw [hcomm]
          _ = e ≫ s.inr := by simp [Category.assoc, hfac₀]
          _ = k ≫ s.inl := by rw [s.condition]
      · calc
          j ≫ q ≫ desc s = (j ≫ q) ≫ desc s := (Category.assoc _ _ _).symm
          _ = j₀ ≫ desc s := by rw [hjq]
          _ = j ≫ s.inl := hfac₁ s
    refine PushoutCocone.IsColimit.mk hcomm desc ?_ ?_ ?_
    · intro s
      exact hdesc s
    · intro s
      exact hfac₀ s
    · intro s m hm₀ hm₁
      apply hQ₀.hom_ext
      · calc
          k₀ ≫ m = s.inr := hm₁
          _ = k₀ ≫ desc s := (hfac₀ s).symm
      · calc
          j₀ ≫ m = (j ≫ q) ≫ m := by rw [hjq]
          _ = j ≫ (q ≫ m) := Category.assoc _ _ _
          _ = j ≫ s.inl := by rw [hm₀]
          _ = j₀ ≫ desc s := (hfac₁ s).symm
  refine ⟨q, ⟨⟨hcomm⟩, ⟨hcol⟩⟩, hcomm, hjq⟩

theorem sliceMap_isPushout_of_components [IsCylinderCategory C]
    {D : Type (u + 1)} [Category.{u} D] [CategoryWithCofibrations D]
    [CategoryWithWeakEquivalences D] [IsCylinderCategory D]
    {F : C ⥤ D} (hF : IsCylinderMorphism F) {X : C}
    {A B C₁ P : SliceObj X} (i : A ⟶ B) (f : A ⟶ C₁)
    (k : B ⟶ P) (j : C₁ ⟶ P) (hcomm : i ≫ k = f ≫ j)
    (h₀ : IsPushout i.v₀ f.v₀ k.v₀ j.v₀) (h_f : IsPushout i.vf f.vf k.vf j.vf)
    (hi₀ : cofibrations C i.v₀) (hi_f : cofibrations C i.vf) :
    IsPushout ((sliceMap hF X).map i) ((sliceMap hF X).map f)
      ((sliceMap hF X).map k) ((sliceMap hF X).map j) := by
  have h₀' := hF.map_isPushout i.v₀ f.v₀ k.v₀ j.v₀ h₀ hi₀
  have h_f' := hF.map_isPushout i.vf f.vf k.vf j.vf h_f hi_f
  have hcomm' : (sliceMap hF X).map i ≫ (sliceMap hF X).map k =
      (sliceMap hF X).map f ≫ (sliceMap hF X).map j := by
    apply SliceObj.Hom.ext
    · change F.map i.v₀ ≫ F.map k.v₀ = F.map f.v₀ ≫ F.map j.v₀
      rw [← F.map_comp, ← F.map_comp]
      exact congrArg F.map (congrArg SliceObj.Hom.v₀ hcomm)
    · change F.map i.vf ≫ F.map k.vf = F.map f.vf ≫ F.map j.vf
      rw [← F.map_comp, ← F.map_comp]
      exact congrArg F.map (congrArg SliceObj.Hom.vf hcomm)
  exact sliceObj_isPushout_of_componentwise _ _ _ _ hcomm' h₀' h_f'

theorem sliceObjHom_vf_cofibration [IsCylinderCategory C] {X : C}
    {A B : SliceObj X} (f : A ⟶ B) (hf : cofibrations (SliceObj X) f) :
    cofibrations C f.vf := by
  rcases hf with ⟨hf₀, hglue⟩
  rcases hglue with ⟨P, k, j, hP, m, hkm, hjm, hm⟩
  have hcof := (inferInstance : IsCofibrationCategory C)
  letI : (cofibrations C).IsStableUnderCobaseChange := hcof.isStableUnderCobaseChange
  letI : (cofibrations C).IsMultiplicative := hcof.isMultiplicative
  have hk : cofibrations C k :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout hP hf₀
  simpa [hkm] using hcof.isMultiplicative.comp_mem k m hk hm

theorem sliceObjHom_vf_weakEquivalence [IsCylinderCategory C] {X : C}
    {A B : SliceObj X} (f : A ⟶ B) :
    weakEquivalences C f.vf := by
  have hcomp : weakEquivalences C (A.x ≫ f.vf) := by rw [f.x_vf]; exact B.x_weakEquivalence
  exact (IsCylinderCategory.twoOutOfSix (C := C)
    (𝟙 X) A.x f.vf
    (by simpa using A.x_weakEquivalence) hcomp).2.2.1

theorem sliceObj_pushout_data [IsCylinderCategory C] {X : C}
    {A B D : SliceObj X} (i : A ⟶ B) (f : A ⟶ D)
    (hi : cofibrations (SliceObj X) i) :
    ∃ (P : SliceObj X) (k : B ⟶ P) (j : D ⟶ P),
      IsPushout i f k j ∧ IsPushout i.v₀ f.v₀ k.v₀ j.v₀ ∧
        IsPushout i.vf f.vf k.vf j.vf := by
  rcases hi with ⟨hi₀, hglue⟩
  rcases hglue with ⟨R, kR, jR, hR, m, hmk, hmj, hm⟩
  have hcof := (inferInstance : IsCofibrationCategory C)
  letI : (cofibrations C).IsStableUnderCobaseChange := hcof.isStableUnderCobaseChange
  letI : (cofibrations C).IsMultiplicative := hcof.isMultiplicative
  have hif : cofibrations C i.vf := sliceObjHom_vf_cofibration i ⟨hi₀, ⟨R, kR, jR, hR, m, hmk, hmj, hm⟩⟩
  have hifwe : weakEquivalences C i.vf := sliceObjHom_vf_weakEquivalence i
  letI : HasPushout i.v₀ f.v₀ := hcof.hasPushout i.v₀ f.v₀ hi₀
  let P₀ := pushout i.v₀ f.v₀
  let b₀ := pushout.inl i.v₀ f.v₀
  let c₀ := pushout.inr i.v₀ f.v₀
  have h₀ : IsPushout i.v₀ f.v₀ b₀ c₀ := IsPushout.of_hasPushout _ _
  letI : HasPushout i.vf f.vf := hcof.hasPushout i.vf f.vf hif
  let P_f := pushout i.vf f.vf
  let b_f := pushout.inl i.vf f.vf
  let c_f := pushout.inr i.vf f.vf
  have h_f : IsPushout i.vf f.vf b_f c_f := IsPushout.of_hasPushout _ _
  have hpaCompat : i.v₀ ≫ (B.a ≫ b_f) = f.v₀ ≫ (D.a ≫ c_f) := by
    calc
      i.v₀ ≫ (B.a ≫ b_f) = (i.v₀ ≫ B.a) ≫ b_f := (Category.assoc _ _ _).symm
      _ = (A.a ≫ i.vf) ≫ b_f := by rw [← i.a_vf]
      _ = A.a ≫ (i.vf ≫ b_f) := Category.assoc _ _ _
      _ = A.a ≫ (f.vf ≫ c_f) := by rw [h_f.w]
      _ = (A.a ≫ f.vf) ≫ c_f := (Category.assoc _ _ _).symm
      _ = (f.v₀ ≫ D.a) ≫ c_f := by rw [f.a_vf]
      _ = f.v₀ ≫ (D.a ≫ c_f) := Category.assoc _ _ _
  let p_a := h₀.desc (B.a ≫ b_f) (D.a ≫ c_f) hpaCompat
  have hpxCompat : B.x ≫ b_f = D.x ≫ c_f := by
    calc
      B.x ≫ b_f = (A.x ≫ i.vf) ≫ b_f := by rw [← i.x_vf]
      _ = A.x ≫ (i.vf ≫ b_f) := Category.assoc _ _ _
      _ = A.x ≫ (f.vf ≫ c_f) := by rw [h_f.w]
      _ = (A.x ≫ f.vf) ≫ c_f := (Category.assoc _ _ _).symm
      _ = D.x ≫ c_f := by rw [f.x_vf]
  let p_x := D.x ≫ c_f
  have hc_f_cof : cofibrations C c_f :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout h_f.flip hif
  have hc_f_we : weakEquivalences C c_f :=
    IsCylinderCategory.trivialCofibration_cobaseChange (C := C)
      i.vf f.vf b_f c_f h_f hif hifwe
  have hpx_cof : cofibrations C p_x :=
    hcof.isMultiplicative.comp_mem D.x c_f D.x_cofibration hc_f_cof
  have hpx_we : weakEquivalences C p_x :=
    (IsCylinderCategory.weakEquivalences_isMultiplicative (C := C)).comp_mem _ _
      D.x_weakEquivalence hc_f_we
  rcases D.cofibrant with ⟨I, hI, P_C, k_C, j_C, hPC, m_C, hkm_C, hjm_C, hm_C⟩
  letI : HasPushout (hI.to P₀) (hI.to X) :=
    hcof.hasPushout (hI.to P₀) (hI.to X) (hcof.initial_cofibration hI P₀)
  let L := pushout (hI.to P₀) (hI.to X)
  let l₀ := pushout.inl (hI.to P₀) (hI.to X)
  let lₓ := pushout.inr (hI.to P₀) (hI.to X)
  have hL : IsPushout (hI.to P₀) (hI.to X) l₀ lₓ := IsPushout.of_hasPushout _ _
  obtain ⟨q, hq, hkq, hjq⟩ :=
    pushout_coproduct_baseChange hI k_C j_C hPC l₀ lₓ hL c₀
  letI : HasPushout m_C q := hcof.hasPushout m_C q hm_C
  let Q := pushout m_C q
  let c_Q := pushout.inl m_C q
  let l_Q := pushout.inr m_C q
  have hCQ : IsPushout m_C q c_Q l_Q := IsPushout.of_hasPushout _ _
  have hCglue : IsPushout D.a c₀ c_Q (l₀ ≫ l_Q) := by
    simpa [hkm_C] using hq.paste_horiz hCQ
  have hBcf : IsPushout i.v₀ (f.v₀ ≫ D.a) (b₀ ≫ l₀ ≫ l_Q) c_Q :=
    h₀.paste_vert hCglue.flip
  have hpaCompat' : i.v₀ ≫ (B.a ≫ b_f) = (f.v₀ ≫ D.a) ≫ c_f := by
    simpa [Category.assoc] using hpaCompat
  let d_Q := hBcf.desc (B.a ≫ b_f) c_f hpaCompat'
  have hbQd : (b₀ ≫ l₀ ≫ l_Q) ≫ d_Q = B.a ≫ b_f :=
    hBcf.inl_desc (B.a ≫ b_f) c_f hpaCompat'
  have hcQd : c_Q ≫ d_Q = c_f := hBcf.inr_desc (B.a ≫ b_f) c_f hpaCompat'
  have hpaQ : l₀ ≫ l_Q ≫ d_Q = p_a := by
    apply h₀.hom_ext
    · calc
        b₀ ≫ (l₀ ≫ l_Q ≫ d_Q) = (b₀ ≫ l₀ ≫ l_Q) ≫ d_Q := by
          simp [Category.assoc]
        _ = B.a ≫ b_f := hbQd
        _ = b₀ ≫ p_a := (h₀.inl_desc (B.a ≫ b_f) (D.a ≫ c_f) hpaCompat).symm
    · calc
        c₀ ≫ (l₀ ≫ l_Q ≫ d_Q) = (c₀ ≫ l₀ ≫ l_Q) ≫ d_Q := by
          simp [Category.assoc]
        _ = (D.a ≫ c_Q) ≫ d_Q := by rw [← hCglue.w]
        _ = D.a ≫ c_f := by
          calc
            (D.a ≫ c_Q) ≫ d_Q = D.a ≫ (c_Q ≫ d_Q) := Category.assoc _ _ _
            _ = D.a ≫ c_f := congrArg (fun z => D.a ≫ z) hcQd
        _ = c₀ ≫ p_a := (h₀.inr_desc (B.a ≫ b_f) (D.a ≫ c_f) hpaCompat).symm
  have hRcompat : A.a ≫ (f.vf ≫ c_Q) = i.v₀ ≫ (b₀ ≫ l₀ ≫ l_Q) := by
    calc
      A.a ≫ (f.vf ≫ c_Q) = (A.a ≫ f.vf) ≫ c_Q := (Category.assoc _ _ _).symm
      _ = (f.v₀ ≫ D.a) ≫ c_Q := by rw [f.a_vf]
      _ = f.v₀ ≫ (D.a ≫ c_Q) := Category.assoc _ _ _
      _ = f.v₀ ≫ (c₀ ≫ l₀ ≫ l_Q) := by rw [← hCglue.w]
      _ = (f.v₀ ≫ c₀) ≫ l₀ ≫ l_Q := by simp [Category.assoc]
      _ = (i.v₀ ≫ b₀) ≫ l₀ ≫ l_Q := by rw [← h₀.w]
      _ = i.v₀ ≫ (b₀ ≫ l₀ ≫ l_Q) := by simp [Category.assoc]
  let r_Q := hR.desc (f.vf ≫ c_Q) (b₀ ≫ l₀ ≫ l_Q) hRcompat
  have hkr : kR ≫ r_Q = f.vf ≫ c_Q :=
    hR.inl_desc (f.vf ≫ c_Q) (b₀ ≫ l₀ ≫ l_Q) hRcompat
  have hjr : jR ≫ r_Q = b₀ ≫ l₀ ≫ l_Q :=
    hR.inr_desc (f.vf ≫ c_Q) (b₀ ≫ l₀ ≫ l_Q) hRcompat
  have hfinalComm : m ≫ b_f = r_Q ≫ d_Q := by
    apply hR.hom_ext
    · calc
        kR ≫ (m ≫ b_f) = (kR ≫ m) ≫ b_f := (Category.assoc _ _ _).symm
        _ = i.vf ≫ b_f := congrArg (fun z => z ≫ b_f) hmk
        _ = f.vf ≫ c_f := h_f.w
        _ = f.vf ≫ (c_Q ≫ d_Q) := congrArg (fun z => f.vf ≫ z) hcQd.symm
        _ = (f.vf ≫ c_Q) ≫ d_Q := (Category.assoc _ _ _).symm
        _ = (kR ≫ r_Q) ≫ d_Q := congrArg (fun z => z ≫ d_Q) hkr.symm
        _ = kR ≫ (r_Q ≫ d_Q) := Category.assoc _ _ _
    · calc
        jR ≫ (m ≫ b_f) = (jR ≫ m) ≫ b_f := (Category.assoc _ _ _).symm
        _ = B.a ≫ b_f := congrArg (fun z => z ≫ b_f) hmj
        _ = (b₀ ≫ l₀ ≫ l_Q) ≫ d_Q := hbQd.symm
        _ = (jR ≫ r_Q) ≫ d_Q := congrArg (fun z => z ≫ d_Q) hjr.symm
        _ = jR ≫ (r_Q ≫ d_Q) := Category.assoc _ _ _
  have hfinalCol : IsColimit (PushoutCocone.mk b_f d_Q hfinalComm) := by
    let desc (s : PushoutCocone m r_Q) : P_f ⟶ s.pt := by
      have hcompat : i.vf ≫ s.inl = f.vf ≫ (c_Q ≫ s.inr) := by
        calc
          i.vf ≫ s.inl = (kR ≫ m) ≫ s.inl := congrArg (fun z => z ≫ s.inl) hmk.symm
          _ = kR ≫ (m ≫ s.inl) := Category.assoc _ _ _
          _ = kR ≫ (r_Q ≫ s.inr) := congrArg (fun z => kR ≫ z) s.condition
          _ = (kR ≫ r_Q) ≫ s.inr := (Category.assoc _ _ _).symm
          _ = (f.vf ≫ c_Q) ≫ s.inr := by rw [hkr]
          _ = f.vf ≫ (c_Q ≫ s.inr) := Category.assoc _ _ _
      exact h_f.desc s.inl (c_Q ≫ s.inr) hcompat
    have hfacB (s : PushoutCocone m r_Q) : b_f ≫ desc s = s.inl := by
      dsimp [desc]
      exact h_f.inl_desc _ _ _
    have hfacQ (s : PushoutCocone m r_Q) : d_Q ≫ desc s = s.inr := by
      apply hBcf.hom_ext
      · calc
          (b₀ ≫ l₀ ≫ l_Q) ≫ d_Q ≫ desc s =
              ((b₀ ≫ l₀ ≫ l_Q) ≫ d_Q) ≫ desc s := (Category.assoc _ _ _).symm
          _ = (B.a ≫ b_f) ≫ desc s := congrArg (fun z => z ≫ desc s) hbQd
          _ = B.a ≫ (b_f ≫ desc s) := Category.assoc _ _ _
          _ = B.a ≫ s.inl := congrArg (fun z => B.a ≫ z) (hfacB s)
          _ = (jR ≫ m) ≫ s.inl := congrArg (fun z => z ≫ s.inl) hmj.symm
          _ = jR ≫ (m ≫ s.inl) := Category.assoc _ _ _
          _ = jR ≫ (r_Q ≫ s.inr) := congrArg (fun z => jR ≫ z) s.condition
          _ = (jR ≫ r_Q) ≫ s.inr := (Category.assoc _ _ _).symm
          _ = (b₀ ≫ l₀ ≫ l_Q) ≫ s.inr := by rw [hjr]
      · calc
          c_Q ≫ d_Q ≫ desc s = c_f ≫ desc s := by
            calc
              c_Q ≫ d_Q ≫ desc s = (c_Q ≫ d_Q) ≫ desc s :=
                (Category.assoc _ _ _).symm
              _ = c_f ≫ desc s := congrArg (fun z => z ≫ desc s) hcQd
          _ = c_Q ≫ s.inr := by
            dsimp [desc]
            exact h_f.inr_desc _ _ _
    refine PushoutCocone.IsColimit.mk hfinalComm desc ?_ ?_ ?_
    · intro s
      exact hfacB s
    · intro s
      exact hfacQ s
    · intro s t htB htQ
      apply h_f.hom_ext
      · exact htB.trans (hfacB s).symm
      · calc
          c_f ≫ t = c_Q ≫ d_Q ≫ t := by
            calc
              c_f ≫ t = (c_Q ≫ d_Q) ≫ t := congrArg (fun z => z ≫ t) hcQd.symm
              _ = c_Q ≫ d_Q ≫ t := Category.assoc _ _ _
          _ = c_Q ≫ s.inr := by rw [htQ]
          _ = c_f ≫ desc s := by dsimp [desc]; exact (h_f.inr_desc _ _ _).symm
  have hfinal : IsPushout m r_Q b_f d_Q := IsPushout.of_isColimit hfinalCol
  have hdQcof : cofibrations C d_Q :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout hfinal.flip hm
  have hlQcof : cofibrations C l_Q :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout hCQ.flip hm_C
  have hwLcof : cofibrations C (l_Q ≫ d_Q) :=
    hcof.isMultiplicative.comp_mem l_Q d_Q hlQcof hdQcof
  have hwLcompat : hI.to P₀ ≫ p_a = hI.to X ≫ p_x := by
    apply hI.hom_ext
  let w_L := hL.desc p_a p_x hwLcompat
  have hwL : w_L = l_Q ≫ d_Q := by
    apply hL.hom_ext
    · calc
        l₀ ≫ w_L = p_a := hL.inl_desc _ _ hwLcompat
        _ = l₀ ≫ (l_Q ≫ d_Q) := by simpa [Category.assoc] using hpaQ.symm
    · calc
        lₓ ≫ w_L = p_x := hL.inr_desc _ _ hwLcompat
        _ = lₓ ≫ (l_Q ≫ d_Q) := by
          calc
            p_x = D.x ≫ c_f := rfl
            _ = j_C ≫ m_C ≫ c_Q ≫ d_Q := by
              rw [← hjm_C, ← hcQd]
              simp [Category.assoc]
            _ = j_C ≫ q ≫ l_Q ≫ d_Q := by
              simpa [Category.assoc] using
                congrArg (fun z => j_C ≫ z ≫ d_Q) hCQ.w
            _ = (j_C ≫ q) ≫ (l_Q ≫ d_Q) := by simp [Category.assoc]
            _ = lₓ ≫ (l_Q ≫ d_Q) := congrArg (fun z => z ≫ (l_Q ≫ d_Q)) hjq
  have hpair : IsCofibrantPair p_a p_x := by
    refine ⟨I, hI, L, l₀, lₓ, hL, w_L, ?_, ?_, ?_⟩
    · exact hL.inl_desc _ _ hwLcompat
    · exact hL.inr_desc _ _ hwLcompat
    · rw [hwL]
      exact hwLcof
  let P : SliceObj X :=
    { A₀ := P₀
      Af := P_f
      a := p_a
      x := p_x
      cofibrant := hpair
      x_cofibration := hpx_cof
      x_weakEquivalence := hpx_we }
  have hka : B.a ≫ b_f = b₀ ≫ p_a := by
    simpa [p_a] using h₀.inl_desc (B.a ≫ b_f) (D.a ≫ c_f) hpaCompat
  have hja : D.a ≫ c_f = c₀ ≫ p_a := by
    simpa [p_a] using h₀.inr_desc (B.a ≫ b_f) (D.a ≫ c_f) hpaCompat
  have hkb : B.x ≫ b_f = p_x := hpxCompat
  let k : B ⟶ P := ⟨b₀, b_f, hka, hkb⟩
  let j : D ⟶ P := ⟨c₀, c_f, hja, rfl⟩
  have hcomm : i ≫ k = f ≫ j := by
    apply SliceObj.Hom.ext
    · change i.v₀ ≫ b₀ = f.v₀ ≫ c₀
      exact h₀.w
    · change i.vf ≫ b_f = f.vf ≫ c_f
      exact h_f.w
  have hpush : IsPushout i f k j :=
    sliceObj_isPushout_of_componentwise i f k j hcomm h₀ h_f
  exact ⟨P, k, j, hpush, h₀, h_f⟩

theorem sliceObj_pushout_components [IsCylinderCategory C] {X : C}
    {A B D P : SliceObj X} (i : A ⟶ B) (f : A ⟶ D) (k : B ⟶ P) (j : D ⟶ P)
    (hi : cofibrations (SliceObj X) i) (hP : IsPushout i f k j) :
    IsPushout i.v₀ f.v₀ k.v₀ j.v₀ ∧ IsPushout i.vf f.vf k.vf j.vf := by
  obtain ⟨P', k', j', hP', h₀, h_f⟩ := sliceObj_pushout_data i f hi
  let e := hP'.isoIsPushout B D hP
  let e₀ : P'.A₀ ≅ P.A₀ :=
    { hom := e.hom.v₀
      inv := e.inv.v₀
      hom_inv_id := by
        exact congrArg SliceObj.Hom.v₀ e.hom_inv_id
      inv_hom_id := by
        exact congrArg SliceObj.Hom.v₀ e.inv_hom_id }
  let e_f : P'.Af ≅ P.Af :=
    { hom := e.hom.vf
      inv := e.inv.vf
      hom_inv_id := by
        exact congrArg SliceObj.Hom.vf e.hom_inv_id
      inv_hom_id := by
        exact congrArg SliceObj.Hom.vf e.inv_hom_id }
  have hk₀ : k'.v₀ ≫ e₀.hom = k.v₀ := by
    exact congrArg SliceObj.Hom.v₀ (hP'.inl_isoIsPushout_hom B D hP)
  have hj₀ : j'.v₀ ≫ e₀.hom = j.v₀ := by
    exact congrArg SliceObj.Hom.v₀ (hP'.inr_isoIsPushout_hom B D hP)
  have hk_f : k'.vf ≫ e_f.hom = k.vf := by
    exact congrArg SliceObj.Hom.vf (hP'.inl_isoIsPushout_hom B D hP)
  have hj_f : j'.vf ≫ e_f.hom = j.vf := by
    exact congrArg SliceObj.Hom.vf (hP'.inr_isoIsPushout_hom B D hP)
  constructor
  · exact h₀.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e₀ (by simp) (by simp)
      (by simpa using hk₀) (by simpa using hj₀)
  · exact h_f.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e_f (by simp) (by simp)
      (by simpa using hk_f) (by simpa using hj_f)

theorem sliceMap_isPushout [IsCylinderCategory C]
    {D : Type (u + 1)} [Category.{u} D] [CategoryWithCofibrations D]
    [CategoryWithWeakEquivalences D] [IsCylinderCategory D]
    {F : C ⥤ D} (hF : IsCylinderMorphism F) {X : C}
    {A B C₁ P : SliceObj X} (i : A ⟶ B) (f : A ⟶ C₁)
    (k : B ⟶ P) (j : C₁ ⟶ P) (hi : cofibrations (SliceObj X) i)
    (hP : IsPushout i f k j) :
    IsPushout ((sliceMap hF X).map i) ((sliceMap hF X).map f)
      ((sliceMap hF X).map k) ((sliceMap hF X).map j) := by
  obtain ⟨h₀, h_f⟩ := sliceObj_pushout_components i f k j hi hP
  have hi₀ : cofibrations C i.v₀ := hi.1
  have hi_f : cofibrations C i.vf := sliceObjHom_vf_cofibration i hi
  exact sliceMap_isPushout_of_components hF i f k j hP.w h₀ h_f hi₀ hi_f

theorem sliceMap_isCylinderMorphism [IsCylinderCategory C]
    {D : Type (u + 1)} [Category.{u} D] [CategoryWithCofibrations D]
    [CategoryWithWeakEquivalences D] [IsCylinderCategory D]
    {F : C ⥤ D} (hF : IsCylinderMorphism F) (X : C) :
    IsCylinderMorphism (sliceMap hF X) := by
  refine
    { map_cofibration := ?_
      map_initial := ?_
      map_isPushout := ?_
      map_weakEquivalence := ?_ }
  · intro A B f hf
    rcases hf with ⟨hf₀, hglue⟩
    refine ⟨hF.map_cofibration f.v₀ hf₀, ?_⟩
    exact map_isCofibrantGluing hF
      (cofibrations_left_of_isCofibrantPair A.cofibrant) hglue
  · intro I hI
    exact sliceMap_mapInitial hF X hI
  · intro A B C₁ P i f k j hP hi
    exact sliceMap_isPushout hF i f k j hi hP
  · intro A B f hf
    exact hF.map_weakEquivalence f.v₀ hf

theorem sliceObj_isHTerminal_proof [IsCylinderCategory C] {X : C}
    (A : SliceObj X) (hA : weakEquivalences C A.a) : IsHTerminal A := by
  letI : IsCylinderCategory (SliceObj X) :=
    (HomotopyHypothesis.Henry.Packages.sliceObj_isLiftingTarget X).1
  obtain ⟨r, hAr, hRa⟩ :=
    (HomotopyHypothesis.Henry.Packages.weakEquivalence_iff (C := C) A.a).mp hA
  have hId : weakEquivalences C (𝟙 A.A₀) :=
    (IsCylinderCategory.weakEquivalences_isMultiplicative (C := C)).id_mem A.A₀
  have hArWe : weakEquivalences C (A.a ≫ r) :=
    (homotopic_weakEquivalences (C := C) hAr).2 hId
  have hrWe : weakEquivalences C r :=
    (IsCylinderCategory.twoOutOfSix (C := C) (𝟙 A.A₀) A.a r
      (by simpa using hA) hArWe).2.2.1
  have hv₀We : weakEquivalences C (A.x ≫ r) :=
    (IsCylinderCategory.weakEquivalences_isMultiplicative (C := C)).comp_mem _ _
      A.x_weakEquivalence hrWe
  have hhom : Homotopic ((A.x ≫ r) ≫ A.a) A.x := by
    simpa [Category.assoc] using homotopic_precomp (C := C) A.x hRa
  rcases hhom with ⟨I, hI, cyl, H, h₀, h₁⟩
  let d : SliceCylinderData X := ⟨I, hI, cyl⟩
  let K := cylinderSliceObjOfData X d
  have hKa : K.a = cyl.j₀ ≫ cyl.c := rfl
  have hKx : K.x = cyl.j₁ ≫ cyl.c := rfl
  have hK : IsHTerminal K := cylinderSliceData_isHTerminal X d
  have h₀K : K.a ≫ H = (A.x ≫ r) ≫ A.a := by simpa [hKa] using h₀
  have h₁K : K.x ≫ H = A.x := by simpa [hKx] using h₁
  let φ : K ⟶ A := ⟨A.x ≫ r, H, h₀K, h₁K⟩
  have hφ : weakEquivalences (SliceObj X) φ := hv₀We
  exact isHTerminal_of_weakEquivalence (C := SliceObj X) φ hφ hK

#print axioms HomotopyHypothesis.Cylinder.HomotopyTerminalSlice.sliceObj_isHTerminal_proof

theorem lift_to_sliceObj_canonical
    {𝒜 : Type (u + 1)} [Category.{u} 𝒜] [CategoryWithCofibrations 𝒜]
    [CategoryWithWeakEquivalences 𝒜] [IsCylinderCategory 𝒜] {o : 𝒜}
    (hcof : IsCofibrantAt.{u + 1, u} 𝒜 o) (ho : IsHTerminal o)
    {D : Type (u + 1)} [Category.{u} D] [CategoryWithCofibrations D]
    [CategoryWithWeakEquivalences D] [IsCylinderCategory D] {f : 𝒜 ⥤ D}
    (hf : IsCylinderMorphism f) :
    ∃ l : 𝒜 ⥤ SliceObj (f.obj o), IsCylinderMorphism l ∧
      l ⋙ SliceObj.forget (f.obj o) = f ∧
      l.obj o = (sliceMap hf o).obj (cylinderSliceObj o) := by
  letI : IsCylinderCategory (SliceObj o) :=
    (HomotopyHypothesis.Henry.Packages.sliceObj_isLiftingTarget o).1
  have hforget := HomotopyHypothesis.Henry.Packages.sliceObj_isLiftingTarget o
  have hforgetAcyclic :=
    (HomotopyHypothesis.Henry.Packages.sliceObj_forget_isAcyclic_iff o).2 ho
  have htarget :
      IsLiftingTarget true (SliceObj o) 𝒜 (SliceObj.forget o) := by
    rcases hforget with ⟨hCylS, hCyl𝒜, hF, hp, hIso, _⟩
    exact ⟨hCylS, hCyl𝒜, hF, hp, hIso, fun _ => hforgetAcyclic⟩
  let K := cylinderSliceObj o
  obtain ⟨g, hg, hgp, hgo⟩ := hcof (SliceObj o) 𝒜 (SliceObj.forget o)
    htarget K trivial (𝟭 𝒜) HomotopyHypothesis.Henry.IsCylinderMorphism.id (by rfl)
  let l := g ⋙ sliceMap hf o
  have hforgetMap : sliceMap hf o ⋙ SliceObj.forget (f.obj o) =
      SliceObj.forget o ⋙ f := rfl
  have hcomp : l ⋙ SliceObj.forget (f.obj o) = f := by
    change g ⋙ (sliceMap hf o ⋙ SliceObj.forget (f.obj o)) = f
    rw [hforgetMap]
    change (g ⋙ SliceObj.forget o) ⋙ f = f
    rw [hgp]
    rfl
  refine ⟨l,
    HomotopyHypothesis.Henry.IsCylinderMorphism.comp hg (sliceMap_isCylinderMorphism hf o),
    hcomp, ?_⟩
  change (sliceMap hf o).obj (g.obj o) = (sliceMap hf o).obj K
  rw [hgo]

end HomotopyHypothesis.Cylinder.HomotopyTerminalSlice
