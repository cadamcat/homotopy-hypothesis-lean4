import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.All
import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.Main.Part2
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Blueprint.Henry.Topology
open CategoryTheory Limits HomotopicalAlgebra HomotopyHypothesis.Henry

universe v u

namespace HomotopyHypothesis.CylinderCategoryTheory


private lemma relativeCylinder_endpoint_properties {C : Type u} [Category.{v} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
    [IsCylinderCategory C] {A B : C} {i : A ⟶ B} (hi : cofibrations C i)
    (cyl : RelativeCylinder i) :
    (cofibrations C (cyl.j₀ ≫ cyl.c) ∧ weakEquivalences C (cyl.j₀ ≫ cyl.c)) ∧
    (cofibrations C (cyl.j₁ ≫ cyl.c) ∧ weakEquivalences C (cyl.j₁ ≫ cyl.c)) := by
  have hcof := (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout
    cyl.isPushout hi
  have hcof₀ := (IsCofibrationCategory.isMultiplicative (C := C)).comp_mem
    cyl.j₀ cyl.c hcof cyl.c_mem
  have hcof₁ := (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout
    cyl.isPushout.flip hi
  have hcof₁' := (IsCofibrationCategory.isMultiplicative (C := C)).comp_mem
    cyl.j₁ cyl.c hcof₁ cyl.c_mem
  have hid : weakEquivalences C (𝟙 B) := by
    exact IsCylinderCategory.isomorphisms_le_weakEquivalences (C := C) (𝟙 B)
      (MorphismProperty.isomorphisms.infer_property (𝟙 B))
  have hw₀ := IsCylinderCategory.twoOutOfSix (C := C) (cyl.j₀ ≫ cyl.c) cyl.p (𝟙 B)
    (by simpa [Category.assoc, cyl.j₀_c_p] using hid) (by simpa using cyl.p_mem)
  have hw₁ := IsCylinderCategory.twoOutOfSix (C := C) (cyl.j₁ ≫ cyl.c) cyl.p (𝟙 B)
    (by simpa [Category.assoc, cyl.j₁_c_p] using hid) (by simpa using cyl.p_mem)
  exact ⟨⟨hcof₀, hw₀.1⟩, ⟨hcof₁', hw₁.1⟩⟩

end HomotopyHypothesis.CylinderCategoryTheory

namespace HomotopyHypothesis.CylinderCategoryTheory

private theorem brown_factorization {C : Type u} [Category.{v} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
    [IsCylinderCategory C] {A B : C} (f : A ⟶ B) :
    ∃ (M : C) (i : A ⟶ M) (p : M ⟶ B),
      cofibrations C i ∧ weakEquivalences C p ∧ i ≫ p = f := by
  classical
  obtain ⟨O, hO_nonempty⟩ := IsCofibrationCategory.exists_initial (C := C)
  let hO : IsInitial O := Classical.choice hO_nonempty
  have hA0 : cofibrations C (hO.to A) :=
    IsCofibrationCategory.initial_cofibration hO A
  have hB0 : cofibrations C (hO.to B) :=
    IsCofibrationCategory.initial_cofibration hO B
  let cyl := Classical.choice (IsCylinderCategory.exists_cylinder (C := C) hO A)
  have hPAB : HasPushout (hO.to A) (hO.to B) :=
    IsCofibrationCategory.hasPushout (C := C) (hO.to A) (hO.to B) hA0
  letI := hPAB
  let PAB := pushout (hO.to A) (hO.to B)
  let a : A ⟶ PAB := pushout.inl (hO.to A) (hO.to B)
  let b : B ⟶ PAB := pushout.inr (hO.to A) (hO.to B)
  let hAB : IsPushout (hO.to A) (hO.to B) a b :=
    IsPushout.of_hasPushout (hO.to A) (hO.to B)
  have hP0 : HasPushout (hO.to A) (hO.to A) := by
    exact cyl.isPushout.hasPushout
  letI := hP0
  have hdcond : (hO.to A) ≫ a = (hO.to A) ≫ (f ≫ b) := by
    exact hO.hom_ext _ _
  let d : cyl.P ⟶ PAB := cyl.isPushout.desc a (f ≫ b) hdcond
  have hM : HasPushout cyl.c d :=
    IsCofibrationCategory.hasPushout (C := C) cyl.c d cyl.c_mem
  letI := hM
  let M := pushout cyl.c d
  let mI : cyl.I ⟶ M := pushout.inl cyl.c d
  let mAB : PAB ⟶ M := pushout.inr cyl.c d
  have hMpo : IsPushout cyl.c d mI mAB := IsPushout.of_hasPushout cyl.c d
  let qAB : PAB ⟶ B := hAB.desc f (𝟙 B) (by
    apply hO.hom_ext)
  have hqABa : a ≫ qAB = f := by simp [qAB, hAB]
  have hqABb : b ≫ qAB = 𝟙 B := by simp [qAB, hAB]
  have hcomm : cyl.c ≫ (cyl.p ≫ f) = d ≫ qAB := by
    apply cyl.isPushout.hom_ext
    · calc
        cyl.j₀ ≫ cyl.c ≫ cyl.p ≫ f = (cyl.j₀ ≫ cyl.c ≫ cyl.p) ≫ f := by simp [Category.assoc]
        _ = f := by rw [cyl.j₀_c_p]; simp
        _ = cyl.j₀ ≫ d ≫ qAB := by simp [d, qAB]
    · calc
        cyl.j₁ ≫ cyl.c ≫ cyl.p ≫ f = (cyl.j₁ ≫ cyl.c ≫ cyl.p) ≫ f := by simp [Category.assoc]
        _ = f := by rw [cyl.j₁_c_p]; simp
        _ = cyl.j₁ ≫ d ≫ qAB := by simp [d, qAB]
  let qM : M ⟶ B := hMpo.desc (cyl.p ≫ f) qAB hcomm
  have hqMI : mI ≫ qM = cyl.p ≫ f := by simp [qM, hMpo]
  have hqMAB : mAB ≫ qM = qAB := by simp [qM, hMpo]
  have hinc : IsPushout (cyl.j₁ ≫ cyl.c) f mI (b ≫ mAB) := by
    let e₀ : A ⟶ cyl.I := cyl.j₀ ≫ cyl.c
    let e₁ : A ⟶ cyl.I := cyl.j₁ ≫ cyl.c
    have hsq : e₁ ≫ mI = f ≫ (b ≫ mAB) := by
      calc
        e₁ ≫ mI = cyl.j₁ ≫ (cyl.c ≫ mI) := by simp [e₁, Category.assoc]
        _ = cyl.j₁ ≫ (d ≫ mAB) := by rw [hMpo.w]
        _ = (cyl.j₁ ≫ d) ≫ mAB := by simp [Category.assoc]
        _ = f ≫ (b ≫ mAB) := by simp [d, Category.assoc]
    let t : PushoutCocone e₁ f := PushoutCocone.mk mI (b ≫ mAB) hsq
    have ht : IsColimit t := by
      apply PushoutCocone.isColimitAux' t
      intro s
      have hinit : (hO.to A) ≫ (e₀ ≫ s.inl) = (hO.to B) ≫ s.inr := by
        exact hO.hom_ext _ _
      let q : PAB ⟶ s.pt := hAB.desc (e₀ ≫ s.inl) s.inr hinit
      have hcompat : d ≫ q = cyl.c ≫ s.inl := by
        apply cyl.isPushout.hom_ext
        · simp [q, d, hAB, e₀]
        · calc
            cyl.j₁ ≫ d ≫ q = f ≫ b ≫ q := by simp [d, Category.assoc]
            _ = f ≫ s.inr := by simp [q]
            _ = e₁ ≫ s.inl := s.condition.symm
            _ = cyl.j₁ ≫ cyl.c ≫ s.inl := by simpa [e₁]
      let m := hMpo.desc s.inl q hcompat.symm
      have hmI : mI ≫ m = s.inl := by
        dsimp [m]
        exact hMpo.inl_desc s.inl q hcompat.symm
      have hmAB : mAB ≫ m = q := by
        dsimp [m]
        exact hMpo.inr_desc s.inl q hcompat.symm
      refine ⟨m, ?_, ?_, ?_⟩
      · exact hmI
      · calc
          (b ≫ mAB) ≫ m = b ≫ (mAB ≫ m) := by simp [Category.assoc]
          _ = b ≫ q := by rw [hmAB]
          _ = s.inr := by simp [q]
      · intro m' hm'I hm'B
        change M ⟶ s.pt at m'
        change mI ≫ m' = s.inl at hm'I
        have hmAB' : mAB ≫ m' = q := by
          apply hAB.hom_ext
          · calc
              a ≫ mAB ≫ m' = cyl.j₀ ≫ d ≫ mAB ≫ m' := by simp [d, Category.assoc]
              _ = cyl.j₀ ≫ (d ≫ mAB) ≫ m' := by simp [Category.assoc]
              _ = cyl.j₀ ≫ (cyl.c ≫ mI) ≫ m' := by rw [← hMpo.w]
              _ = cyl.j₀ ≫ cyl.c ≫ s.inl := by simp [Category.assoc, hm'I]
              _ = a ≫ q := by simp [q, e₀]
          · calc
              b ≫ mAB ≫ m' = (b ≫ mAB) ≫ m' := by simp [Category.assoc]
              _ = s.inr := hm'B
              _ = b ≫ q := by simp [q]
        apply hMpo.hom_ext
        · calc
            mI ≫ m' = s.inl := hm'I
            _ = mI ≫ m := hmI.symm
        · exact hmAB'.trans hmAB.symm
    exact IsPushout.of_isColimit ht
  have hend := relativeCylinder_endpoint_properties hA0 cyl
  have hincW : weakEquivalences C (b ≫ mAB) :=
    IsCylinderCategory.trivialCofibration_cobaseChange (C := C)
      (cyl.j₁ ≫ cyl.c) f mI (b ≫ mAB) hinc hend.2.1 hend.2.2
  have hid : weakEquivalences C (𝟙 B) :=
    IsCylinderCategory.isomorphisms_le_weakEquivalences (C := C) (𝟙 B)
      (MorphismProperty.isomorphisms.infer_property (𝟙 B))
  have hsqW : weakEquivalences C ((b ≫ mAB) ≫ qM) := by
    rw [Category.assoc, hqMAB, hqABb]
    exact hid
  have hqW := IsCylinderCategory.twoOutOfSix (C := C) (𝟙 B) (b ≫ mAB) qM
    (by simpa using hincW) hsqW
  have hiW : weakEquivalences C qM := hqW.2.2.1
  have hia : cofibrations C (a ≫ mAB) :=
    (IsCofibrationCategory.isMultiplicative (C := C)).comp_mem a mAB
      ((IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout hAB hB0)
      ((IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout hMpo.flip cyl.c_mem)
  refine ⟨M, a ≫ mAB, qM, hia, hiW, ?_⟩
  calc
    (a ≫ mAB) ≫ qM = a ≫ (mAB ≫ qM) := by simp [Category.assoc]
    _ = a ≫ qAB := by rw [hqMAB]
    _ = f := hqABa

end HomotopyHypothesis.CylinderCategoryTheory

namespace HomotopyHypothesis.CylinderCategoryTheory

private lemma exists_relativeCylinder {C : Type u} [Category.{v} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
    [IsCylinderCategory C] {A B : C} (i : A ⟶ B) (hi : cofibrations C i) :
    Nonempty (RelativeCylinder i) := by
  classical
  letI : HasPushout i i := IsCofibrationCategory.hasPushout (C := C) i i hi
  let P := pushout i i
  let hP : IsPushout i i (pushout.inl i i) (pushout.inr i i) := IsPushout.of_hasPushout i i
  let d : P ⟶ B := hP.desc (𝟙 B) (𝟙 B) (by simp)
  obtain ⟨I, c, p, hc, hp, hcp⟩ := brown_factorization d
  refine ⟨⟨P, pushout.inl i i, pushout.inr i i, hP, I, c, p, hc, hp, ?_, ?_⟩⟩
  · calc
      pushout.inl i i ≫ c ≫ p = pushout.inl i i ≫ (c ≫ p) := by simp [Category.assoc]
      _ = pushout.inl i i ≫ d := by rw [hcp]
      _ = 𝟙 B := by simp [d]
  · calc
      pushout.inr i i ≫ c ≫ p = pushout.inr i i ≫ (c ≫ p) := by simp [Category.assoc]
      _ = pushout.inr i i ≫ d := by rw [hcp]
      _ = 𝟙 B := by simp [d]

end HomotopyHypothesis.CylinderCategoryTheory

namespace HomotopyHypothesis.CylinderCategoryTheory

private lemma cofibration_lifts_against_weak_equivalence {C : Type u} [Category.{v} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
    [IsCylinderCategory C] {A B X Y : C} (i : A ⟶ B) (hi : cofibrations C i)
    (f : A ⟶ X) (w : X ⟶ Y) (g : B ⟶ Y)
    (hsq : i ≫ g = f ≫ w) (hw : weakEquivalences C w) :
    ∃ l : B ⟶ X, i ≫ l = f := by
  classical
  letI : HasPushout i f := IsCofibrationCategory.hasPushout (C := C) i f hi
  let P := pushout i f
  let k : B ⟶ P := pushout.inl i f
  let j : X ⟶ P := pushout.inr i f
  let hP : IsPushout i f k j := IsPushout.of_hasPushout i f
  let q : P ⟶ Y := hP.desc g w hsq
  obtain ⟨Z, c, e, hc, he, hce⟩ := brown_factorization q
  have hjcof : cofibrations C j :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout hP.flip hi
  have hJcof : cofibrations C (j ≫ c) :=
    (IsCofibrationCategory.isMultiplicative (C := C)).comp_mem j c hjcof hc
  have hcomp : (j ≫ c) ≫ e = w := by
    calc
      (j ≫ c) ≫ e = j ≫ (c ≫ e) := by simp [Category.assoc]
      _ = j ≫ q := by rw [hce]
      _ = w := by simp [q]
  have hJwcomp : weakEquivalences C ((j ≫ c) ≫ e) := by rw [hcomp]; exact hw
  have hid : weakEquivalences C (𝟙 Y) :=
    IsCylinderCategory.isomorphisms_le_weakEquivalences (C := C) (𝟙 Y)
      (MorphismProperty.isomorphisms.infer_property (𝟙 Y))
  have hjw := IsCylinderCategory.twoOutOfSix (C := C) (j ≫ c) e (𝟙 Y)
    (by simpa using hJwcomp) (by simpa using he)
  have hJw : weakEquivalences C (j ≫ c) := hjw.1
  obtain ⟨r, hr⟩ := IsCylinderCategory.exists_retraction (C := C) (j ≫ c) hJcof hJw
  refine ⟨k ≫ c ≫ r, ?_⟩
  calc
    i ≫ (k ≫ c ≫ r) = (i ≫ k) ≫ c ≫ r := by simp [Category.assoc]
    _ = (f ≫ j) ≫ c ≫ r := by rw [hP.w]
    _ = f := by
      calc
        (f ≫ j) ≫ c ≫ r = f ≫ ((j ≫ c) ≫ r) := by simp [Category.assoc]
        _ = f ≫ 𝟙 X := by rw [hr]
        _ = f := by simp

end HomotopyHypothesis.CylinderCategoryTheory

namespace HomotopyHypothesis.CylinderCategoryTheory

private lemma relHomotopic_precomp {C : Type u} [Category.{v} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
    [IsCylinderCategory C] {A B X A' B' : C}
    (i : A ⟶ B) (i' : A' ⟶ B') (a : A' ⟶ A) (v : B' ⟶ B)
    (hsq : i' ≫ v = a ≫ i) (hi' : cofibrations C i')
    {f g : B ⟶ X} (h : RelHomotopic i f g) :
    RelHomotopic i' (v ≫ f) (v ≫ g) := by
  classical
  obtain ⟨src, H, h₀, h₁⟩ := h
  let tgt := Classical.choice (exists_relativeCylinder i' hi')
  have hbase : i' ≫ (v ≫ src.j₀ ≫ src.c) = i' ≫ (v ≫ src.j₁ ≫ src.c) := by
    calc
      i' ≫ (v ≫ src.j₀ ≫ src.c) = (i' ≫ v) ≫ src.j₀ ≫ src.c := by simp [Category.assoc]
      _ = (a ≫ i) ≫ src.j₀ ≫ src.c := by rw [hsq]
      _ = (a ≫ i) ≫ src.j₁ ≫ src.c := by
        calc
          (a ≫ i) ≫ src.j₀ ≫ src.c = a ≫ (i ≫ src.j₀) ≫ src.c := by simp [Category.assoc]
          _ = a ≫ (i ≫ src.j₁) ≫ src.c := by rw [src.isPushout.w]
          _ = (a ≫ i) ≫ src.j₁ ≫ src.c := by simp [Category.assoc]
      _ = i' ≫ (v ≫ src.j₁ ≫ src.c) := by rw [← hsq]; simp [Category.assoc]
  let top : tgt.P ⟶ src.I := tgt.isPushout.desc
    (v ≫ src.j₀ ≫ src.c) (v ≫ src.j₁ ≫ src.c) hbase
  have hsq' : tgt.c ≫ (tgt.p ≫ v) = top ≫ src.p := by
    apply tgt.isPushout.hom_ext
    · calc
        tgt.j₀ ≫ tgt.c ≫ (tgt.p ≫ v) = v := by
          calc
            tgt.j₀ ≫ tgt.c ≫ (tgt.p ≫ v) = (tgt.j₀ ≫ tgt.c ≫ tgt.p) ≫ v := by simp [Category.assoc]
            _ = 𝟙 B' ≫ v := by rw [tgt.j₀_c_p]
            _ = v := by simp
        _ = tgt.j₀ ≫ top ≫ src.p := by simp [top, Category.assoc, src.j₀_c_p]
    · calc
        tgt.j₁ ≫ tgt.c ≫ (tgt.p ≫ v) = v := by
          calc
            tgt.j₁ ≫ tgt.c ≫ (tgt.p ≫ v) = (tgt.j₁ ≫ tgt.c ≫ tgt.p) ≫ v := by simp [Category.assoc]
            _ = 𝟙 B' ≫ v := by rw [tgt.j₁_c_p]
            _ = v := by simp
        _ = tgt.j₁ ≫ top ≫ src.p := by simp [top, Category.assoc, src.j₁_c_p]
  obtain ⟨L, hL⟩ := cofibration_lifts_against_weak_equivalence
    tgt.c tgt.c_mem top src.p (tgt.p ≫ v) hsq' src.p_mem
  refine ⟨tgt, L ≫ H, ?_, ?_⟩
  · calc
      tgt.j₀ ≫ tgt.c ≫ (L ≫ H) = tgt.j₀ ≫ ((tgt.c ≫ L) ≫ H) := by
        simp [Category.assoc]
      _ = tgt.j₀ ≫ (top ≫ H) := by rw [hL]
      _ = v ≫ src.j₀ ≫ src.c ≫ H := by simp [top, Category.assoc]
      _ = v ≫ f := by rw [h₀]
  · calc
      tgt.j₁ ≫ tgt.c ≫ (L ≫ H) = tgt.j₁ ≫ ((tgt.c ≫ L) ≫ H) := by
        simp [Category.assoc]
      _ = tgt.j₁ ≫ (top ≫ H) := by rw [hL]
      _ = v ≫ src.j₁ ≫ src.c ≫ H := by simp [top, Category.assoc]
      _ = v ≫ g := by rw [h₁]

private lemma trivialCofibration_relHomotopic {C : Type u} [Category.{v} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
    [IsCylinderCategory C] {A B X : C} (i : A ⟶ B)
    (hi : cofibrations C i) (hw : weakEquivalences C i)
    (f g : B ⟶ X) (hfg : i ≫ f = i ≫ g) : RelHomotopic i f g := by
  classical
  letI : HasPushout i i := IsCofibrationCategory.hasPushout (C := C) i i hi
  let P := pushout i i
  let j₀ : B ⟶ P := pushout.inl i i
  let j₁ : B ⟶ P := pushout.inr i i
  let hP : IsPushout i i j₀ j₁ := IsPushout.of_hasPushout i i
  let d : P ⟶ B := hP.desc (𝟙 B) (𝟙 B) (by simp)
  have hj₀w : weakEquivalences C j₀ :=
    IsCylinderCategory.trivialCofibration_cobaseChange (C := C) i i j₁ j₀ hP.flip hi hw
  have hcomp : weakEquivalences C (j₀ ≫ d) := by
    rw [hP.inl_desc]
    exact IsCylinderCategory.isomorphisms_le_weakEquivalences (C := C) (𝟙 B)
      (MorphismProperty.isomorphisms.infer_property (𝟙 B))
  have hdw : weakEquivalences C d := by
    have htwo := IsCylinderCategory.twoOutOfSix (C := C) (𝟙 B) j₀ d
      (by simpa using hj₀w) (by simpa using hcomp)
    exact htwo.2.2.1
  let cyl : RelativeCylinder i :=
    { P := P
      j₀ := j₀
      j₁ := j₁
      isPushout := hP
      I := P
      c := 𝟙 P
      p := d
      c_mem := IsCofibrationCategory.isomorphisms_le (C := C) (𝟙 P)
        (MorphismProperty.isomorphisms.infer_property (𝟙 P))
      p_mem := hdw
      j₀_c_p := by simp [j₀, d, hP]
      j₁_c_p := by simp [j₁, d, hP] }
  refine ⟨cyl, hP.desc f g hfg, ?_, ?_⟩
  · simpa [cyl, j₀] using hP.inl_desc f g hfg
  · simpa [cyl, j₁] using hP.inr_desc f g hfg

private lemma cofibration_semilifts_against_weak_equivalence {C : Type u}
    [Category.{v} C] [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
    [IsCylinderCategory C] {A B X Y : C} (i : A ⟶ B) (hi : cofibrations C i)
    (f : A ⟶ X) (w : X ⟶ Y) (g : B ⟶ Y)
    (hsq : i ≫ g = f ≫ w) (hw : weakEquivalences C w) :
    ∃ l : B ⟶ X, i ≫ l = f ∧ RelHomotopic i (l ≫ w) g := by
  classical
  letI : HasPushout i f := IsCofibrationCategory.hasPushout (C := C) i f hi
  let P := pushout i f
  let k : B ⟶ P := pushout.inl i f
  let j : X ⟶ P := pushout.inr i f
  let hP : IsPushout i f k j := IsPushout.of_hasPushout i f
  let q : P ⟶ Y := hP.desc g w hsq
  obtain ⟨Z, c, e, hc, he, hce⟩ := brown_factorization q
  have hjcof : cofibrations C j :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout hP.flip hi
  have hJcof : cofibrations C (j ≫ c) :=
    (IsCofibrationCategory.isMultiplicative (C := C)).comp_mem j c hjcof hc
  have hcomp : (j ≫ c) ≫ e = w := by
    calc
      (j ≫ c) ≫ e = j ≫ (c ≫ e) := by simp [Category.assoc]
      _ = j ≫ q := by rw [hce]
      _ = w := by simp [q]
  have hJwcomp : weakEquivalences C ((j ≫ c) ≫ e) := by rw [hcomp]; exact hw
  have hid : weakEquivalences C (𝟙 Y) :=
    IsCylinderCategory.isomorphisms_le_weakEquivalences (C := C) (𝟙 Y)
      (MorphismProperty.isomorphisms.infer_property (𝟙 Y))
  have hjw := IsCylinderCategory.twoOutOfSix (C := C) (j ≫ c) e (𝟙 Y)
    (by simpa using hJwcomp) (by simpa using he)
  have hJw : weakEquivalences C (j ≫ c) := hjw.1
  obtain ⟨r, hr⟩ := IsCylinderCategory.exists_retraction (C := C) (j ≫ c) hJcof hJw
  let l : B ⟶ X := k ≫ c ≫ r
  have hl : i ≫ l = f := by
    calc
      i ≫ (k ≫ c ≫ r) = (i ≫ k) ≫ c ≫ r := by simp [Category.assoc]
      _ = (f ≫ j) ≫ c ≫ r := by rw [hP.w]
      _ = f ≫ ((j ≫ c) ≫ r) := by simp [Category.assoc]
      _ = f ≫ 𝟙 X := by rw [hr]
      _ = f := by simp
  have hAgree : (j ≫ c) ≫ (r ≫ j ≫ c) = (j ≫ c) ≫ 𝟙 Z := by
    calc
      (j ≫ c) ≫ (r ≫ j ≫ c) = ((j ≫ c) ≫ r) ≫ j ≫ c := by simp [Category.assoc]
      _ = 𝟙 X ≫ j ≫ c := by rw [hr]
      _ = (j ≫ c) ≫ 𝟙 Z := by simp
  have htriv := trivialCofibration_relHomotopic (j ≫ c) hJcof hJw
    (r ≫ j ≫ c) (𝟙 Z) hAgree
  have hpush : i ≫ (k ≫ c) = f ≫ (j ≫ c) := by
    calc
      i ≫ (k ≫ c) = (i ≫ k) ≫ c := by simp [Category.assoc]
      _ = (f ≫ j) ≫ c := by rw [hP.w]
      _ = f ≫ (j ≫ c) := by simp [Category.assoc]
  have hrel := relHomotopic_precomp (j ≫ c) i f (k ≫ c) hpush hi htriv
  have hpost : RelHomotopic i ((k ≫ c ≫ r ≫ j ≫ c) ≫ e)
      ((k ≫ c) ≫ e) := by
    obtain ⟨cyl, H, h₀, h₁⟩ := hrel
    refine ⟨cyl, H ≫ e, ?_, ?_⟩
    · simpa [Category.assoc] using congrArg (fun z => z ≫ e) h₀
    · simpa [Category.assoc] using congrArg (fun z => z ≫ e) h₁
  have hfirst : ((k ≫ c ≫ r ≫ j ≫ c) ≫ e) = l ≫ w := by
    simp [l, Category.assoc, hcomp]
  have hsecond : (k ≫ c) ≫ e = g := by
    calc
      (k ≫ c) ≫ e = k ≫ (c ≫ e) := by simp [Category.assoc]
      _ = k ≫ q := by rw [hce]
      _ = g := by simp [q]
  rw [hfirst, hsecond] at hpost
  exact ⟨l, hl, hpost⟩

end HomotopyHypothesis.CylinderCategoryTheory

namespace HomotopyHypothesis.CylinderCategoryTheory

private lemma relHomotopic_transfer {C : Type u} [Category.{v} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
    [IsCylinderCategory C] {A B X : C} (i : A ⟶ B) (hi : cofibrations C i)
    (cyl₁ cyl₂ : RelativeCylinder i) {f g : B ⟶ X}
    (h : RelHomotopic i f g) :
    ∃ H : cyl₂.I ⟶ X,
      cyl₂.j₀ ≫ cyl₂.c ≫ H = f ∧ cyl₂.j₁ ≫ cyl₂.c ≫ H = g := by
  classical
  obtain ⟨src, H, h₀, h₁⟩ := h
  have hbase : i ≫ (src.j₀ ≫ src.c) = i ≫ (src.j₁ ≫ src.c) := by
    calc
      i ≫ (src.j₀ ≫ src.c) = (i ≫ src.j₀) ≫ src.c := by simp [Category.assoc]
      _ = (i ≫ src.j₁) ≫ src.c := by rw [src.isPushout.w]
      _ = i ≫ (src.j₁ ≫ src.c) := by simp [Category.assoc]
  let top : cyl₂.P ⟶ src.I := cyl₂.isPushout.desc
    (src.j₀ ≫ src.c) (src.j₁ ≫ src.c) hbase
  have hsq : cyl₂.c ≫ cyl₂.p = top ≫ src.p := by
    apply cyl₂.isPushout.hom_ext
    · calc
        cyl₂.j₀ ≫ cyl₂.c ≫ cyl₂.p = 𝟙 B := cyl₂.j₀_c_p
        _ = src.j₀ ≫ src.c ≫ src.p := by rw [src.j₀_c_p]
        _ = cyl₂.j₀ ≫ top ≫ src.p := by simp [top]
    · calc
        cyl₂.j₁ ≫ cyl₂.c ≫ cyl₂.p = 𝟙 B := cyl₂.j₁_c_p
        _ = src.j₁ ≫ src.c ≫ src.p := by rw [src.j₁_c_p]
        _ = cyl₂.j₁ ≫ top ≫ src.p := by simp [top]
  obtain ⟨L, hL⟩ := cofibration_lifts_against_weak_equivalence
    cyl₂.c cyl₂.c_mem top src.p cyl₂.p hsq src.p_mem
  refine ⟨L ≫ H, ?_, ?_⟩
  · calc
      cyl₂.j₀ ≫ cyl₂.c ≫ (L ≫ H) = cyl₂.j₀ ≫ ((cyl₂.c ≫ L) ≫ H) := by
        simp [Category.assoc]
      _ = cyl₂.j₀ ≫ (top ≫ H) := by rw [hL]
      _ = src.j₀ ≫ src.c ≫ H := by simp [top, Category.assoc]
      _ = f := h₀
  · calc
      cyl₂.j₁ ≫ cyl₂.c ≫ (L ≫ H) = cyl₂.j₁ ≫ ((cyl₂.c ≫ L) ≫ H) := by
        simp [Category.assoc]
      _ = cyl₂.j₁ ≫ (top ≫ H) := by rw [hL]
      _ = src.j₁ ≫ src.c ≫ H := by simp [top, Category.assoc]
      _ = g := h₁

end HomotopyHypothesis.CylinderCategoryTheory

namespace HomotopyHypothesis.CylinderCategoryTheory

private lemma relHomotopic_trans {C : Type u} [Category.{v} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
    [IsCylinderCategory C] {A B X : C} (i : A ⟶ B) (hi : cofibrations C i)
    {f g h : B ⟶ X} (hfg : RelHomotopic i f g) (hgh : RelHomotopic i g h) :
    RelHomotopic i f h := by
  classical
  obtain ⟨cyl₁, H₁, h₀, h₁⟩ := hfg
  obtain ⟨cyl₂, H₂, h₂, h₃⟩ := hgh
  let e₀₁ : B ⟶ cyl₁.I := cyl₁.j₀ ≫ cyl₁.c
  let e₁₁ : B ⟶ cyl₁.I := cyl₁.j₁ ≫ cyl₁.c
  let e₀₂ : B ⟶ cyl₂.I := cyl₂.j₀ ≫ cyl₂.c
  let e₁₂ : B ⟶ cyl₂.I := cyl₂.j₁ ≫ cyl₂.c
  have hend₁ := relativeCylinder_endpoint_properties hi cyl₁
  have hend₂ := relativeCylinder_endpoint_properties hi cyl₂
  letI : HasPushout e₁₁ e₀₂ :=
    IsCofibrationCategory.hasPushout (C := C) e₁₁ e₀₂ hend₁.2.1
  let J := pushout e₁₁ e₀₂
  let inl : cyl₁.I ⟶ J := pushout.inl e₁₁ e₀₂
  let inr : cyl₂.I ⟶ J := pushout.inr e₁₁ e₀₂
  let hJ : IsPushout e₁₁ e₀₂ inl inr := IsPushout.of_hasPushout e₁₁ e₀₂
  have hseam : e₁₁ ≫ H₁ = e₀₂ ≫ H₂ := by
    simpa [e₁₁, e₀₂] using h₁.trans h₂.symm
  let HJ : J ⟶ X := hJ.desc H₁ H₂ hseam
  have hpcond : e₁₁ ≫ cyl₁.p = e₀₂ ≫ cyl₂.p := by
    have hp₁ : e₁₁ ≫ cyl₁.p = 𝟙 B := by
      simpa [e₁₁, Category.assoc] using cyl₁.j₁_c_p
    have hp₂ : e₀₂ ≫ cyl₂.p = 𝟙 B := by
      simpa [e₀₂, Category.assoc] using cyl₂.j₀_c_p
    exact hp₁.trans hp₂.symm
  let pJ : J ⟶ B := hJ.desc cyl₁.p cyl₂.p hpcond
  have hinlW : weakEquivalences C inl :=
    IsCylinderCategory.trivialCofibration_cobaseChange (C := C)
      e₀₂ e₁₁ inr inl hJ.flip hend₂.1.1 hend₂.1.2
  have hid : weakEquivalences C (𝟙 cyl₁.I) :=
    IsCylinderCategory.isomorphisms_le_weakEquivalences (C := C) (𝟙 cyl₁.I)
      (MorphismProperty.isomorphisms.infer_property (𝟙 cyl₁.I))
  have hinlComp : weakEquivalences C (inl ≫ pJ) := by
    rw [hJ.inl_desc cyl₁.p cyl₂.p hpcond]
    exact cyl₁.p_mem
  have hpJW := IsCylinderCategory.twoOutOfSix (C := C) (𝟙 cyl₁.I) inl pJ
    (show weakEquivalences C ((𝟙 cyl₁.I) ≫ inl) from by simpa using hinlW)
    (show weakEquivalences C (inl ≫ pJ) from hinlComp)
  have hpJW' : weakEquivalences C pJ := hpJW.2.2.1
  let start : B ⟶ J := e₀₁ ≫ inl
  let finish : B ⟶ J := e₁₂ ≫ inr
  have hrel₁ : i ≫ e₀₁ = i ≫ e₁₁ := by
    calc
      i ≫ e₀₁ = (i ≫ cyl₁.j₀) ≫ cyl₁.c := by simp [e₀₁, Category.assoc]
      _ = (i ≫ cyl₁.j₁) ≫ cyl₁.c := by rw [cyl₁.isPushout.w]
      _ = i ≫ e₁₁ := by simp [e₁₁, Category.assoc]
  have hrel₂ : i ≫ e₀₂ = i ≫ e₁₂ := by
    calc
      i ≫ e₀₂ = (i ≫ cyl₂.j₀) ≫ cyl₂.c := by simp [e₀₂, Category.assoc]
      _ = (i ≫ cyl₂.j₁) ≫ cyl₂.c := by rw [cyl₂.isPushout.w]
      _ = i ≫ e₁₂ := by simp [e₁₂, Category.assoc]
  have hboundary : i ≫ start = i ≫ finish := by
    calc
      i ≫ start = (i ≫ e₀₁) ≫ inl := by simp [start, Category.assoc]
      _ = (i ≫ e₁₁) ≫ inl := congrArg (fun z => z ≫ inl) hrel₁
      _ = i ≫ (e₁₁ ≫ inl) := by simp [Category.assoc]
      _ = i ≫ (e₀₂ ≫ inr) := by rw [hJ.w]
      _ = (i ≫ e₀₂) ≫ inr := by simp [Category.assoc]
      _ = (i ≫ e₁₂) ≫ inr := congrArg (fun z => z ≫ inr) hrel₂
      _ = i ≫ finish := by simp [finish, Category.assoc]
  let cyl : RelativeCylinder i := Classical.choice (exists_relativeCylinder i hi)
  let top : cyl.P ⟶ J := cyl.isPushout.desc start finish hboundary
  have hstartP : start ≫ pJ = 𝟙 B := by
    calc
      start ≫ pJ = e₀₁ ≫ (inl ≫ pJ) := by simp [start, Category.assoc]
      _ = e₀₁ ≫ cyl₁.p := by rw [hJ.inl_desc cyl₁.p cyl₂.p hpcond]
      _ = 𝟙 B := by simpa [e₀₁] using cyl₁.j₀_c_p
  have hfinishP : finish ≫ pJ = 𝟙 B := by
    calc
      finish ≫ pJ = e₁₂ ≫ (inr ≫ pJ) := by simp [finish, Category.assoc]
      _ = e₁₂ ≫ cyl₂.p := by rw [hJ.inr_desc cyl₁.p cyl₂.p hpcond]
      _ = 𝟙 B := by simpa [e₁₂] using cyl₂.j₁_c_p
  have hsq : cyl.c ≫ cyl.p = top ≫ pJ := by
    apply cyl.isPushout.hom_ext
    · calc
        cyl.j₀ ≫ cyl.c ≫ cyl.p = 𝟙 B := cyl.j₀_c_p
        _ = start ≫ pJ := hstartP.symm
        _ = cyl.j₀ ≫ top ≫ pJ := by simp [top]
    · calc
        cyl.j₁ ≫ cyl.c ≫ cyl.p = 𝟙 B := cyl.j₁_c_p
        _ = finish ≫ pJ := hfinishP.symm
        _ = cyl.j₁ ≫ top ≫ pJ := by simp [top]
  obtain ⟨L, hL⟩ := cofibration_lifts_against_weak_equivalence
    cyl.c cyl.c_mem top pJ cyl.p hsq hpJW'
  have hstartH : start ≫ HJ = f := by
    calc
      start ≫ HJ = e₀₁ ≫ H₁ := by simp [start, HJ]
      _ = f := by simpa [e₀₁, Category.assoc] using h₀
  have hfinishH : finish ≫ HJ = h := by
    calc
      finish ≫ HJ = e₁₂ ≫ H₂ := by simp [finish, HJ]
      _ = h := by simpa [e₁₂, Category.assoc] using h₃
  refine ⟨cyl, L ≫ HJ, ?_, ?_⟩
  · calc
      cyl.j₀ ≫ cyl.c ≫ (L ≫ HJ) = cyl.j₀ ≫ ((cyl.c ≫ L) ≫ HJ) := by
        simp [Category.assoc]
      _ = cyl.j₀ ≫ (top ≫ HJ) := by rw [hL]
      _ = start ≫ HJ := by simp [top]
      _ = f := hstartH
  · calc
      cyl.j₁ ≫ cyl.c ≫ (L ≫ HJ) = cyl.j₁ ≫ ((cyl.c ≫ L) ≫ HJ) := by
        simp [Category.assoc]
      _ = cyl.j₁ ≫ (top ≫ HJ) := by rw [hL]
      _ = finish ≫ HJ := by simp [top]
      _ = h := hfinishH

end HomotopyHypothesis.CylinderCategoryTheory

namespace HomotopyHypothesis.CylinderCategoryTheory

/-- Relative homotopy along a cofibration is an equivalence relation, independent of the chosen
relative cylinder object. -/
theorem relHomotopic_equivalence_proof {C : Type u} [Category.{v} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
    [IsCylinderCategory C] {A B X : C} (i : A ⟶ B) (hi : cofibrations C i) :
    Equivalence (RelHomotopic (X := X) i) ∧
      ∀ (cyl : RelativeCylinder i) (f g : B ⟶ X), RelHomotopic i f g →
        ∃ H : cyl.I ⟶ X, cyl.j₀ ≫ cyl.c ≫ H = f ∧ cyl.j₁ ≫ cyl.c ≫ H = g := by
  have heq : Equivalence (RelHomotopic (X := X) i) := by
    refine ⟨?_, ?_, ?_⟩
    · intro f
      obtain ⟨cyl⟩ := exists_relativeCylinder i hi
      exact ⟨cyl, cyl.p ≫ f,
        by simpa [Category.assoc] using congrArg (fun q => q ≫ f) cyl.j₀_c_p,
        by simpa [Category.assoc] using congrArg (fun q => q ≫ f) cyl.j₁_c_p⟩
    · intro f g hfg
      obtain ⟨cyl, H, h₀, h₁⟩ := hfg
      let swapped : RelativeCylinder i :=
        { P := cyl.P
          j₀ := cyl.j₁
          j₁ := cyl.j₀
          isPushout := cyl.isPushout.flip
          I := cyl.I
          c := cyl.c
          p := cyl.p
          c_mem := cyl.c_mem
          p_mem := cyl.p_mem
          j₀_c_p := cyl.j₁_c_p
          j₁_c_p := cyl.j₀_c_p }
      exact ⟨swapped, H, h₁, h₀⟩
    · intro f g h hfg hgh
      exact relHomotopic_trans i hi hfg hgh
  refine ⟨heq, ?_⟩
  intro cyl f g hfg
  exact relHomotopic_transfer i hi cyl cyl hfg

end HomotopyHypothesis.CylinderCategoryTheory

namespace HomotopyHypothesis.CylinderCategoryTheory

private lemma relHomotopic_symm {C : Type u} [Category.{v} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
    {A B X : C} {i : A ⟶ B} {f g : B ⟶ X}
    (h : RelHomotopic i f g) : RelHomotopic i g f := by
  obtain ⟨cyl, H, h₀, h₁⟩ := h
  let swapped : RelativeCylinder i :=
    { P := cyl.P
      j₀ := cyl.j₁
      j₁ := cyl.j₀
      isPushout := cyl.isPushout.flip
      I := cyl.I
      c := cyl.c
      p := cyl.p
      c_mem := cyl.c_mem
      p_mem := cyl.p_mem
      j₀_c_p := cyl.j₁_c_p
      j₁_c_p := cyl.j₀_c_p }
  exact ⟨swapped, H, h₁, h₀⟩

private lemma homotopic_normalize {C : Type u} [Category.{v} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
    [IsCylinderCategory C] {X Y : C} {f g : X ⟶ Y}
    (h : Homotopic f g) {O : C} (hO : IsInitial O) :
    RelHomotopic (hO.to X) f g := by
  classical
  obtain ⟨O', hO', hrel⟩ := h
  let a : O ⟶ O' := hO.to O'
  have hsq : hO.to X ≫ 𝟙 X = a ≫ hO'.to X := by
    apply hO.hom_ext
  simpa using relHomotopic_precomp (hO'.to X) (hO.to X) a (𝟙 X) hsq
    (IsCofibrationCategory.initial_cofibration hO X) hrel

private lemma homotopic_symm {C : Type u} [Category.{v} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
    [IsCylinderCategory C] {X Y : C} {f g : X ⟶ Y}
    (h : Homotopic f g) : Homotopic g f := by
  classical
  obtain ⟨O, hO_nonempty⟩ := IsCofibrationCategory.exists_initial (C := C)
  let hO : IsInitial O := Classical.choice hO_nonempty
  exact ⟨O, hO, relHomotopic_symm (homotopic_normalize h hO)⟩

private lemma homotopic_trans {C : Type u} [Category.{v} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
    [IsCylinderCategory C] {X Y : C} {f g h : X ⟶ Y}
    (hfg : Homotopic f g) (hgh : Homotopic g h) : Homotopic f h := by
  classical
  obtain ⟨O, hO_nonempty⟩ := IsCofibrationCategory.exists_initial (C := C)
  let hO : IsInitial O := Classical.choice hO_nonempty
  have hi : cofibrations C (hO.to X) :=
    IsCofibrationCategory.initial_cofibration hO X
  exact ⟨O, hO, relHomotopic_trans (hO.to X) hi
    (homotopic_normalize hfg hO) (homotopic_normalize hgh hO)⟩

private lemma homotopic_postcomp {C : Type u} [Category.{v} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
    {X Y Z : C} {f g : X ⟶ Y} (h : Homotopic f g) (u : Y ⟶ Z) :
    Homotopic (f ≫ u) (g ≫ u) := by
  obtain ⟨O, hO, hrel⟩ := h
  obtain ⟨cyl, H, h₀, h₁⟩ := hrel
  refine ⟨O, hO, cyl, H ≫ u, ?_, ?_⟩
  · simpa [Category.assoc] using congrArg (fun k => k ≫ u) h₀
  · simpa [Category.assoc] using congrArg (fun k => k ≫ u) h₁

private lemma homotopic_precomp {C : Type u} [Category.{v} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
    [IsCylinderCategory C] {X Y Z : C} {f g : Y ⟶ Z}
    (h : Homotopic f g) (v : X ⟶ Y) : Homotopic (v ≫ f) (v ≫ g) := by
  classical
  obtain ⟨O, hO, hrel⟩ := h
  let i := hO.to X
  have hi : cofibrations C i := IsCofibrationCategory.initial_cofibration hO X
  have hsq : i ≫ v = (𝟙 O) ≫ hO.to Y := by
    apply hO.hom_ext
  have hrel' := relHomotopic_precomp (hO.to Y) i (𝟙 O) v hsq hi hrel
  exact ⟨O, hO, hrel'⟩

private lemma homotopic_weak_left {C : Type u} [Category.{v} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
    [IsCylinderCategory C] {X Y : C} {f g : X ⟶ Y}
    (h : Homotopic f g) (hg : weakEquivalences C g) : weakEquivalences C f := by
  obtain ⟨O, hO, hrel⟩ := h
  obtain ⟨cyl, H, h₀, h₁⟩ := hrel
  have hi : cofibrations C (hO.to X) := IsCofibrationCategory.initial_cofibration hO X
  have hend := relativeCylinder_endpoint_properties hi cyl
  have hH : weakEquivalences C H := by
    have htwo := IsCylinderCategory.twoOutOfSix (C := C) (𝟙 X)
      (cyl.j₁ ≫ cyl.c) H
      (by simpa using hend.2.2)
      (by simpa [Category.assoc, h₁] using hg)
    exact htwo.2.2.1
  have hcomp := (IsCylinderCategory.weakEquivalences_isMultiplicative (C := C)).comp_mem
    (cyl.j₀ ≫ cyl.c) H hend.1.2 hH
  rw [← h₀]
  simpa [Category.assoc] using hcomp

private lemma exists_homotopy_inverse_of_weak {C : Type u} [Category.{v} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
    [IsCylinderCategory C] {X Y : C} (f : X ⟶ Y)
    (hf : weakEquivalences C f) :
    ∃ g : Y ⟶ X, Homotopic (f ≫ g) (𝟙 X) ∧ Homotopic (g ≫ f) (𝟙 Y) := by
  classical
  obtain ⟨O, hO_nonempty⟩ := IsCofibrationCategory.exists_initial (C := C)
  let hO : IsInitial O := Classical.choice hO_nonempty
  let iX : O ⟶ X := hO.to X
  let iY : O ⟶ Y := hO.to Y
  have hiX : cofibrations C iX := IsCofibrationCategory.initial_cofibration hO X
  have hiY : cofibrations C iY := IsCofibrationCategory.initial_cofibration hO Y
  have hsqY : iY ≫ 𝟙 Y = iX ≫ f := by apply hO.hom_ext
  obtain ⟨g, _, hgfRel⟩ := cofibration_semilifts_against_weak_equivalence
    iY hiY iX f (𝟙 Y) hsqY hf
  let hgf : Homotopic (g ≫ f) (𝟙 Y) := ⟨O, hO, hgfRel⟩
  have hidY : weakEquivalences C (𝟙 Y) :=
    IsCylinderCategory.isomorphisms_le_weakEquivalences (C := C) (𝟙 Y)
      (MorphismProperty.isomorphisms.infer_property (𝟙 Y))
  have hgfW := homotopic_weak_left hgf hidY
  have hgW : weakEquivalences C g := by
    have htwo := IsCylinderCategory.twoOutOfSix (C := C) g f (𝟙 Y)
      (by simpa using hgfW) (by simpa using hf)
    exact htwo.1
  have hsqX : iX ≫ 𝟙 X = iY ≫ g := by apply hO.hom_ext
  obtain ⟨h, _, hhgRel⟩ := cofibration_semilifts_against_weak_equivalence
    iX hiX iY g (𝟙 X) hsqX hgW
  let hhg : Homotopic (h ≫ g) (𝟙 X) := ⟨O, hO, hhgRel⟩
  have htriple_f : Homotopic ((h ≫ g) ≫ f) f := by
    simpa [Category.assoc] using homotopic_postcomp hhg f
  have htriple_h : Homotopic ((h ≫ g) ≫ f) h := by
    simpa [Category.assoc] using homotopic_precomp hgf h
  have hfh : Homotopic f h :=
    homotopic_trans (homotopic_symm htriple_f) htriple_h
  have hfg : Homotopic (f ≫ g) (h ≫ g) := homotopic_postcomp hfh g
  exact ⟨g, homotopic_trans hfg hhg, hgf⟩

/-- Weak equivalences in a cylinder category are precisely maps with homotopy inverses. -/
theorem weakEquivalence_iff_proof {C : Type u} [Category.{v} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
    [IsCylinderCategory C] {X Y : C} (f : X ⟶ Y) :
    weakEquivalences C f ↔ ∃ g : Y ⟶ X,
      Homotopic (f ≫ g) (𝟙 X) ∧ Homotopic (g ≫ f) (𝟙 Y) := by
  constructor
  · exact exists_homotopy_inverse_of_weak f
  · rintro ⟨g, hfg, hgf⟩
    have hidX : weakEquivalences C (𝟙 X) :=
      IsCylinderCategory.isomorphisms_le_weakEquivalences (C := C) (𝟙 X)
        (MorphismProperty.isomorphisms.infer_property (𝟙 X))
    have hfgW := homotopic_weak_left hfg hidX
    have hgfW := homotopic_weak_left hgf
      (IsCylinderCategory.isomorphisms_le_weakEquivalences (C := C) (𝟙 Y)
        (MorphismProperty.isomorphisms.infer_property (𝟙 Y)))
    have htwo := IsCylinderCategory.twoOutOfSix (C := C) f g f
      (by simpa using hfgW) (by simpa using hgfW)
    exact htwo.1

end HomotopyHypothesis.CylinderCategoryTheory

#print axioms HomotopyHypothesis.CylinderCategoryTheory.weakEquivalence_iff_proof

#print axioms HomotopyHypothesis.CylinderCategoryTheory.relHomotopic_equivalence_proof

namespace HomotopyHypothesis.CylinderCategoryTheory

/-- The identity functor of a cylinder category is acyclic. -/
theorem isAcyclic_id_proof {C : Type u} [Category.{v} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
    [IsCylinderCategory C] : IsAcyclic (𝟭 C) := by
  constructor
  · intro Y
    refine ⟨Y, 𝟙 Y, ?_⟩
    exact IsCylinderCategory.isomorphisms_le_weakEquivalences (C := C) (𝟙 Y)
      (MorphismProperty.isomorphisms.infer_property (𝟙 Y))
  · intro A B X i hi x v hsq
    refine ⟨v, ?_, ?_⟩
    · simpa using hsq
    · change RelHomotopic i v v
      exact (relHomotopic_equivalence_proof i hi).1.refl v

end HomotopyHypothesis.CylinderCategoryTheory

#print axioms HomotopyHypothesis.CylinderCategoryTheory.isAcyclic_id_proof

namespace HomotopyHypothesis.CylinderCategoryTheory

private theorem terminalCat_isCylinderCategory :
    IsCylinderCategory (TerminalCat.{u}) := by
  letI : CategoryWithCofibrations (TerminalCat.{u}) := inferInstance
  letI : CategoryWithWeakEquivalences (TerminalCat.{u}) := inferInstance
  refine
    { toIsCofibrationCategory := ?_
      isomorphisms_le_weakEquivalences := ?_
      weakEquivalences_isMultiplicative := ?_
      twoOutOfSix := ?_
      trivialCofibration_cobaseChange := ?_
      exists_cylinder := ?_
      exists_retraction := ?_ }
  · refine
      { isomorphisms_le := ?_
        isMultiplicative := ?_
        exists_initial := ?_
        initial_cofibration := ?_
        hasPushout := ?_
        isStableUnderCobaseChange := ?_ }
    · intro A B f hf
      trivial
    · change (⊤ : MorphismProperty (TerminalCat.{u})).IsMultiplicative
      infer_instance
    · refine ⟨PUnit.unit, ⟨?_⟩⟩
      exact IsInitial.ofUniqueHom (fun _ => PUnit.unit) (fun _ _ => rfl)
    · intro I hI X
      trivial
    · intro A B X i f hi
      let t : PushoutCocone i f :=
        PushoutCocone.mk (W := PUnit.unit) PUnit.unit PUnit.unit (by subsingleton)
      have ht : IsColimit t :=
        PushoutCocone.IsColimit.mk (by subsingleton) (fun _ => PUnit.unit)
          (fun _ => rfl) (fun _ => rfl) (fun _ _ _ _ => rfl)
      exact (IsPushout.of_isColimit ht).hasPushout
    · change (⊤ : MorphismProperty (TerminalCat.{u})).IsStableUnderCobaseChange
      constructor
      intro A A' B B' f g f' g' h hf
      trivial
  · intro A B f hf
    trivial
  · change (⊤ : MorphismProperty (TerminalCat.{u})).IsMultiplicative
    infer_instance
  · intro A B D E f g h hfg hgh
    exact ⟨by trivial, by trivial, by trivial, by trivial⟩
  · intro A B X P i f k j h hi hw
    trivial
  · intro I hI X
    let t : PushoutCocone (hI.to X) (hI.to X) :=
      PushoutCocone.mk (W := PUnit.unit) PUnit.unit PUnit.unit (by subsingleton)
    have ht : IsColimit t :=
      PushoutCocone.IsColimit.mk (by subsingleton) (fun _ => PUnit.unit)
        (fun _ => rfl) (fun _ => rfl) (fun _ _ _ _ => rfl)
    let cyl : RelativeCylinder (hI.to X) :=
      { P := t.pt
        j₀ := t.inl
        j₁ := t.inr
        isPushout := IsPushout.of_isColimit ht
        I := PUnit.unit
        c := PUnit.unit
        p := PUnit.unit
        c_mem := by trivial
        p_mem := by trivial
        j₀_c_p := by rfl
        j₁_c_p := by rfl }
    exact ⟨cyl⟩
  · intro A B i hi hw
    exact ⟨PUnit.unit, by rfl⟩

/-- The projection to the terminal cylinder category is a lifting target. -/
theorem toTerminalCat_isLiftingTarget_proof {C : Type (u + 1)} [Category.{u} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
    [IsCylinderCategory C] :
    IsLiftingTarget false C TerminalCat.{u} (toTerminalCat C) := by
  refine ⟨inferInstance, terminalCat_isCylinderCategory, ?_, ?_, ?_, ?_⟩
  · exact HomotopyHypothesis.Henry.toTerminalCat_isCylinderMorphism (C := C)
  · constructor
    · intro A B s hs hw r hsr
      obtain ⟨r', hr'⟩ := IsCylinderCategory.exists_retraction (C := C) s hs hw
      exact ⟨r', hr', rfl⟩
    · intro A B f Q i w hi hw hfactor
      obtain ⟨P, i', w', hi', hw', hcomp⟩ := brown_factorization f
      refine ⟨P, i', w', rfl, hi', hw', hcomp, ?_, ?_⟩
      · rfl
      · rfl
  · intro x y _
    exact ⟨x, Iso.refl x, rfl, rfl⟩
  · intro h
    cases h

end HomotopyHypothesis.CylinderCategoryTheory

#print axioms HomotopyHypothesis.CylinderCategoryTheory.toTerminalCat_isLiftingTarget_proof

namespace HomotopyHypothesis.CylinderCategoryTheory

/-- A homotopy slice contains the cylinder object determined by any cylinder of its base. -/
theorem sliceObj_exists_cylinder_proof {C : Type (u + 1)} [Category.{u} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
    [IsCylinderCategory C] (X : C) :
    ∃ A : SliceObj X, A.A₀ = X ∧ weakEquivalences C A.a := by
  classical
  obtain ⟨O, hO_nonempty⟩ := IsCofibrationCategory.exists_initial (C := C)
  let hO : IsInitial O := Classical.choice hO_nonempty
  obtain ⟨cyl⟩ := IsCylinderCategory.exists_cylinder (C := C) hO X
  have hend := relativeCylinder_endpoint_properties
    (IsCofibrationCategory.initial_cofibration hO X) cyl
  have hpair : IsCofibrantPair (cyl.j₀ ≫ cyl.c) (cyl.j₁ ≫ cyl.c) := by
    refine ⟨O, hO, ?_⟩
    refine ⟨cyl.P, cyl.j₀, cyl.j₁, cyl.isPushout, cyl.c, ?_, ?_, cyl.c_mem⟩
    · rfl
    · rfl
  let A : SliceObj X :=
    { A₀ := X
      Af := cyl.I
      a := cyl.j₀ ≫ cyl.c
      x := cyl.j₁ ≫ cyl.c
      cofibrant := hpair
      x_cofibration := hend.2.1
      x_weakEquivalence := hend.2.2 }
  exact ⟨A, rfl, hend.1.2⟩

end HomotopyHypothesis.CylinderCategoryTheory

#print axioms HomotopyHypothesis.CylinderCategoryTheory.sliceObj_exists_cylinder_proof

namespace HomotopyHypothesis.CylinderCategoryTheory

/-- A cellular realization preserves the cylinder category structure in finite cell complexes. -/
theorem isCylinderMorphism_toFinCell_proof {C : Type*} [Category C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
    {G : C ⥤ TopCat.{u}} (hG : IsCellularRealization G) :
    IsCylinderMorphism hG.toFinCell where
  map_cofibration _ _ f hf := hG.map_cofibration f hf
  map_initial _ hI := by
    obtain ⟨hI'⟩ := hG.map_initial hI
    refine ⟨IsInitial.ofUniqueHom (fun Y => ?_) (fun Y f => ?_)⟩
    · exact ObjectProperty.homMk (hI'.to Y.obj)
    · apply ObjectProperty.hom_ext
      exact hI'.hom_ext _ _
  map_isPushout _ _ _ _ i f k j h hi := by
    let F := ObjectProperty.ι Top.IsFiniteCellComplex
    have hTop : IsPushout (F.map (hG.toFinCell.map i)) (F.map (hG.toFinCell.map f))
        (F.map (hG.toFinCell.map k)) (F.map (hG.toFinCell.map j)) :=
      hG.map_isPushout i f k j h hi
    exact hTop.of_map_of_faithful F
  map_weakEquivalence _ _ f hf := hG.map_weakEquivalence f hf

end HomotopyHypothesis.CylinderCategoryTheory

#print axioms HomotopyHypothesis.CylinderCategoryTheory.isCylinderMorphism_toFinCell_proof

namespace HomotopyHypothesis.CylinderCategoryTheory

/-- A map between contractible spaces is a homotopy equivalence. -/
theorem homotopyEquivalence_of_contractibleSpace_proof {X Y : TopCat.{u}}
    [ContractibleSpace X] [ContractibleSpace Y] (f : X ⟶ Y) :
    Top.homotopyEquivalences f := by
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

end HomotopyHypothesis.CylinderCategoryTheory

#print axioms HomotopyHypothesis.CylinderCategoryTheory.homotopyEquivalence_of_contractibleSpace_proof

namespace HomotopyHypothesis.CylinderCategoryTheory

/-- The realization of the semisimplicial `0`-simplex is contractible. -/
theorem contractibleSpace_toTop_zero_proof :
    ContractibleSpace (HomotopyHypothesis.Henry.SemiSSet.toTop.{u}.obj
      (HomotopyHypothesis.Henry.SemiSimplexCategory.mk 0)) := by
  change ContractibleSpace (SimplexCategory.toTop.{u}.obj (SimplexCategory.mk 0))
  infer_instance

end HomotopyHypothesis.CylinderCategoryTheory

#print axioms HomotopyHypothesis.CylinderCategoryTheory.contractibleSpace_toTop_zero_proof
