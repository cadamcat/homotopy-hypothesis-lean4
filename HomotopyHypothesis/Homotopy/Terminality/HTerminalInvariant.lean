import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.CylinderCategoryTheory.Proofs
import HomotopyHypothesis.FiniteCategory.Lifting.HelperStatements
noncomputable section

universe v u

open CategoryTheory Limits HomotopicalAlgebra HomotopyHypothesis.Henry

namespace HomotopyHypothesis.Homotopy.Terminality

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

theorem hTerminalInvariantStatement_proof (X : Type u) [Category.{v} X]
    [CategoryWithCofibrations X] [CategoryWithWeakEquivalences X] [IsCylinderCategory X] :
    HomotopyHypothesis.FiniteCategory.Lifting.HTerminalInvariantStatement X := by
  change ∀ {A B : X} (w : A ⟶ B), weakEquivalences X w →
    (IsHTerminal A ↔ IsHTerminal B)
  intro A B w hw
  constructor
  · intro hA
    obtain ⟨g, hgw, hwg⟩ :=
      (HomotopyHypothesis.CylinderCategoryTheory.weakEquivalence_iff_proof w).1 hw
    have hg : weakEquivalences X g :=
      (HomotopyHypothesis.CylinderCategoryTheory.weakEquivalence_iff_proof g).2
        ⟨w, hwg, hgw⟩
    intro C D i hi a
    obtain ⟨b, hb⟩ := hA i hi (a ≫ g)
    exact cofibration_lifts_against_weak_equivalence i hi a g b hb hg
  · intro hB
    intro C D i hi a
    obtain ⟨b, hb⟩ := hB i hi (a ≫ w)
    exact cofibration_lifts_against_weak_equivalence i hi a w b hb hw

example {X : Type u} [Category.{v} X] [CategoryWithCofibrations X]
    [CategoryWithWeakEquivalences X] [IsCylinderCategory X] :
    HomotopyHypothesis.FiniteCategory.Lifting.HTerminalInvariantStatement X :=
  HomotopyHypothesis.Homotopy.Terminality.hTerminalInvariantStatement_proof X

#print axioms HomotopyHypothesis.Homotopy.Terminality.hTerminalInvariantStatement_proof

end HomotopyHypothesis.Homotopy.Terminality
