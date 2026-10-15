import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.CylinderCategoryTheory.Proofs
import HomotopyHypothesis.Cylinder.SliceCategory.ForgetSurjective
import HomotopyHypothesis.Cylinder.SliceCategory.Proofs
import HomotopyHypothesis.Category.SemiModelStructure.CylinderFacts
open CategoryTheory Limits HomotopicalAlgebra HomotopyHypothesis.Henry

universe u

namespace HomotopyHypothesis.Cylinder.SliceCategory

noncomputable section

private theorem relativeCylinder_exists_of_cofibration {C : Type (u + 1)}
    [Category.{u} C] [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
    [IsCylinderCategory C] {A B : C} (i : A ⟶ B) (hi : cofibrations C i) :
    Nonempty (RelativeCylinder i) := by
  classical
  letI : HasPushout i i := IsCofibrationCategory.hasPushout (C := C) i i hi
  let P := pushout i i
  let j₀ : B ⟶ P := pushout.inl i i
  let j₁ : B ⟶ P := pushout.inr i i
  let hP : IsPushout i i j₀ j₁ := IsPushout.of_hasPushout i i
  let d : P ⟶ B := hP.desc (𝟙 B) (𝟙 B) (by simp)
  obtain ⟨I, c, p, hc, hp, hcp⟩ :=
    HomotopyHypothesis.Category.SemiModelStructure.brown_factorization d
  refine ⟨⟨P, j₀, j₁, hP, I, c, p, hc, hp, ?_, ?_⟩⟩
  · calc
      j₀ ≫ c ≫ p = j₀ ≫ (c ≫ p) := by simp [Category.assoc]
      _ = j₀ ≫ d := by rw [hcp]
      _ = 𝟙 B := by simp [d, hP]
  · calc
      j₁ ≫ c ≫ p = j₁ ≫ (c ≫ p) := by simp [Category.assoc]
      _ = j₁ ≫ d := by rw [hcp]
      _ = 𝟙 B := by simp [d, hP]

private theorem cofibration_lifts_against_weakEquivalence {C : Type (u + 1)}
    [Category.{u} C] [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
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
  obtain ⟨Z, c, e, hc, he, hce⟩ :=
    HomotopyHypothesis.Category.SemiModelStructure.brown_factorization q
  have hjcof : cofibrations C j :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout hP.flip hi
  have hJcof : cofibrations C (j ≫ c) :=
    (IsCofibrationCategory.isMultiplicative (C := C)).comp_mem j c hjcof hc
  have hcomp : (j ≫ c) ≫ e = w := by
    calc
      (j ≫ c) ≫ e = j ≫ (c ≫ e) := by simp [Category.assoc]
      _ = j ≫ q := by rw [hce]
      _ = w := by simp [q]
  have hJwcomp : weakEquivalences C ((j ≫ c) ≫ e) := by
    rw [hcomp]
    exact hw
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

/-- Homotopy terminality is invariant under weak equivalence. -/
theorem isHTerminal_of_weakEquivalence {C : Type (u + 1)} [Category.{u} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [IsCylinderCategory C]
    {X Y : C} (hX : IsHTerminal X) (w : X ⟶ Y) (hw : weakEquivalences C w) :
    IsHTerminal Y := by
  obtain ⟨v, hXhom, hYhom⟩ :=
    (HomotopyHypothesis.CylinderCategoryTheory.weakEquivalence_iff_proof w).mp hw
  have hv : weakEquivalences C v :=
    (HomotopyHypothesis.CylinderCategoryTheory.weakEquivalence_iff_proof v).mpr
      ⟨w, hYhom, hXhom⟩
  intro A B i hi a
  obtain ⟨b, hb⟩ := hX i hi (a ≫ v)
  exact cofibration_lifts_against_weakEquivalence i hi a v b hb hv

/-- A cylinder on the base determines an h-terminal object in its homotopy slice. -/
theorem exists_hTerminal_sliceCylinder {C : Type (u + 1)} [Category.{u} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [IsCylinderCategory C]
    (X : C) : ∃ U : SliceObj X, U.A₀ = X ∧ IsHTerminal U := by
  classical
  obtain ⟨I, hIne⟩ := IsCofibrationCategory.exists_initial (C := C)
  let hI : IsInitial I := Classical.choice hIne
  have hIX : cofibrations C (hI.to X) :=
    IsCofibrationCategory.initial_cofibration hI X
  obtain ⟨cyl⟩ := IsCylinderCategory.exists_cylinder hI X
  have hend := HomotopyHypothesis.Category.SemiModelStructure.relativeCylinder_endpoint_properties hIX cyl
  have hPair : IsCofibrantPair (cyl.j₀ ≫ cyl.c) (cyl.j₁ ≫ cyl.c) := by
    refine ⟨I, hI, cyl.P, cyl.j₀, cyl.j₁, cyl.isPushout, cyl.c, ?_, ?_, cyl.c_mem⟩
    · rfl
    · rfl
  let U : SliceObj X :=
    { A₀ := X
      Af := cyl.I
      a := cyl.j₀ ≫ cyl.c
      x := cyl.j₁ ≫ cyl.c
      cofibrant := hPair
      x_cofibration := hend.2.1
      x_weakEquivalence := hend.2.2 }
  have hU : IsHTerminal U := by
    intro A B f hf s
    change cofibrations C f.v₀ ∧ IsCofibrantGluing A.a f.v₀ f.vf B.a at hf
    rcases hf with ⟨hf₀, ⟨P, k, j, hP, m, hkm, hjm, hm⟩⟩
    have hfvf : cofibrations C f.vf :=
      sliceHom_vf_cofibration f ⟨hf₀, ⟨P, k, j, hP, m, hkm, hjm, hm⟩⟩
    have hfvfwe : weakEquivalences C f.vf := sliceHom_vf_weakEquivalence f
    obtain ⟨r, hr⟩ := IsCylinderCategory.exists_retraction f.vf hfvf hfvfwe
    let gX : B.Af ⟶ X := r ≫ s.vf ≫ cyl.p
    let g₀ : B.A₀ ⟶ X := B.a ≫ gX
    have hg₀ : f.v₀ ≫ g₀ = s.v₀ := by
      calc
        f.v₀ ≫ g₀ = (f.v₀ ≫ B.a) ≫ (r ≫ (s.vf ≫ cyl.p)) := by
          simp [g₀, gX, Category.assoc]
        _ = (A.a ≫ f.vf) ≫ (r ≫ (s.vf ≫ cyl.p)) := by rw [← f.a_vf]
        _ = A.a ≫ ((f.vf ≫ r) ≫ (s.vf ≫ cyl.p)) := by simp [Category.assoc]
        _ = A.a ≫ (s.vf ≫ cyl.p) := by rw [hr]; simp [Category.assoc]
        _ = (A.a ≫ s.vf) ≫ cyl.p := by rw [Category.assoc]
        _ = (s.v₀ ≫ U.a) ≫ cyl.p := by rw [s.a_vf]
        _ = s.v₀ ≫ (U.a ≫ cyl.p) := by rw [Category.assoc]
        _ = s.v₀ := by simp [U, cyl.j₀_c_p]
    have hcompat : A.a ≫ s.vf = f.v₀ ≫ (g₀ ≫ U.a) := by
      calc
        A.a ≫ s.vf = s.v₀ ≫ U.a := s.a_vf
        _ = (f.v₀ ≫ g₀) ≫ U.a := by rw [hg₀]
        _ = f.v₀ ≫ (g₀ ≫ U.a) := by simp [Category.assoc]
    let g : P ⟶ U.Af := hP.desc s.vf (g₀ ≫ U.a) hcompat
    have hsq : m ≫ gX = g ≫ cyl.p := by
      apply hP.hom_ext
      · calc
          k ≫ (m ≫ gX) = (k ≫ m) ≫ gX := by rw [← Category.assoc]
          _ = f.vf ≫ gX := by rw [hkm]
          _ = f.vf ≫ (r ≫ (s.vf ≫ cyl.p)) := rfl
          _ = (f.vf ≫ r) ≫ (s.vf ≫ cyl.p) := by rw [Category.assoc]
          _ = s.vf ≫ cyl.p := by rw [hr]; simp [Category.assoc]
          _ = (k ≫ g) ≫ cyl.p := by
            rw [hP.inl_desc s.vf (g₀ ≫ U.a) hcompat]
          _ = k ≫ (g ≫ cyl.p) := by rw [Category.assoc]
      · calc
          j ≫ (m ≫ gX) = (j ≫ m) ≫ gX := by rw [← Category.assoc]
          _ = B.a ≫ gX := by rw [hjm]
          _ = g₀ := rfl
          _ = (j ≫ g) ≫ cyl.p := by
            rw [hP.inr_desc s.vf (g₀ ≫ U.a) hcompat]
            simp [U, cyl.j₀_c_p, Category.assoc]
          _ = j ≫ (g ≫ cyl.p) := by rw [Category.assoc]
    obtain ⟨v_f, hv_f⟩ :=
      cofibration_lifts_against_weakEquivalence m hm g cyl.p gX hsq cyl.p_mem
    have hva : B.a ≫ v_f = g₀ ≫ U.a := by
      calc
        B.a ≫ v_f = (j ≫ m) ≫ v_f := by rw [hjm]
        _ = j ≫ (m ≫ v_f) := by rw [Category.assoc]
        _ = j ≫ g := by rw [hv_f]
        _ = g₀ ≫ U.a := by simp [g, hP]
    have hvx : B.x ≫ v_f = U.x := by
      calc
        B.x ≫ v_f = (A.x ≫ f.vf) ≫ v_f := by rw [f.x_vf]
        _ = A.x ≫ (f.vf ≫ v_f) := by rw [Category.assoc]
        _ = A.x ≫ ((k ≫ m) ≫ v_f) := by rw [hkm]
        _ = A.x ≫ (k ≫ (m ≫ v_f)) := by rw [Category.assoc]
        _ = A.x ≫ (k ≫ g) := by rw [hv_f]
        _ = A.x ≫ s.vf := by
          rw [hP.inl_desc s.vf (g₀ ≫ U.a) hcompat]
        _ = U.x := s.x_vf
    let v : B ⟶ U := ⟨g₀, v_f, hva, hvx⟩
    have hcomp : f ≫ v = s := by
      apply SliceObj.Hom.ext
      · exact hg₀
      · calc
          f.vf ≫ v_f = (k ≫ m) ≫ v_f := by rw [← hkm]
          _ = k ≫ (m ≫ v_f) := by simp [Category.assoc]
          _ = k ≫ g := by rw [hv_f]
          _ = s.vf := hP.inl_desc s.vf (g₀ ≫ U.a) hcompat
    exact ⟨v, hcomp⟩
  exact ⟨U, rfl, hU⟩

/-- If the base is homotopy terminal, every map into the replacement of a slice object extends. -/
theorem sliceObj_forget_isHomotopyFullyFaithful_of_hTerminal
    {C : Type (u + 1)} [Category.{u} C] [CategoryWithCofibrations C]
    [CategoryWithWeakEquivalences C] [IsCylinderCategory C] (X : C)
    (hX : IsHTerminal X) : IsHomotopyFullyFaithful (SliceObj.forget X) := by
  intro A B Z f hf s x hsq
  change B.A₀ ⟶ Z.A₀ at x
  change cofibrations C f.v₀ ∧ IsCofibrantGluing A.a f.v₀ f.vf B.a at hf
  rcases hf with ⟨hf₀, ⟨P, k, j, hP, m, hkm, hjm, hm⟩⟩
  change f.v₀ ≫ x = s.v₀ at hsq
  have hZf : IsHTerminal Z.Af :=
    isHTerminal_of_weakEquivalence hX Z.x Z.x_weakEquivalence
  have hcompat : A.a ≫ s.vf = f.v₀ ≫ (x ≫ Z.a) := by
    calc
      A.a ≫ s.vf = s.v₀ ≫ Z.a := s.a_vf
      _ = (f.v₀ ≫ x) ≫ Z.a := by rw [hsq]
      _ = f.v₀ ≫ (x ≫ Z.a) := by simp [Category.assoc]
  let g : P ⟶ Z.Af := hP.desc s.vf (x ≫ Z.a) hcompat
  obtain ⟨v_f, hv_f⟩ := hZf m hm g
  have hva : B.a ≫ v_f = x ≫ Z.a := by
    calc
      B.a ≫ v_f = (j ≫ m) ≫ v_f := by rw [← hjm]
      _ = j ≫ (m ≫ v_f) := by simp [Category.assoc]
      _ = j ≫ g := by rw [hv_f]
      _ = x ≫ Z.a := by simp [g, hP]
  have hvx : B.x ≫ v_f = Z.x := by
    calc
      B.x ≫ v_f = (A.x ≫ f.vf) ≫ v_f := by rw [f.x_vf]
      _ = (A.x ≫ (k ≫ m)) ≫ v_f := by rw [hkm]
      _ = A.x ≫ k ≫ (m ≫ v_f) := by simp [Category.assoc]
      _ = A.x ≫ k ≫ g := by rw [hv_f]
      _ = A.x ≫ s.vf := by simp [g, hP, Category.assoc]
      _ = Z.x := s.x_vf
  let v' : B ⟶ Z := ⟨x, v_f, hva, hvx⟩
  have hcomp : f ≫ v' = s := by
    apply SliceObj.Hom.ext
    · exact hsq
    · calc
        f.vf ≫ v_f = (k ≫ m) ≫ v_f := by rw [← hkm]
        _ = k ≫ (m ≫ v_f) := by simp [Category.assoc]
        _ = k ≫ g := by rw [hv_f]
        _ = s.vf := by simp [g, hP]
  have hrel : RelHomotopic f.v₀ x x := by
    obtain ⟨cyl⟩ := relativeCylinder_exists_of_cofibration f.v₀ hf₀
    refine ⟨cyl, cyl.p ≫ x, ?_, ?_⟩
    · calc
        cyl.j₀ ≫ cyl.c ≫ (cyl.p ≫ x) = (cyl.j₀ ≫ cyl.c ≫ cyl.p) ≫ x := by
          simp [Category.assoc]
        _ = 𝟙 B.A₀ ≫ x := by rw [cyl.j₀_c_p]
        _ = x := by simp
    · calc
        cyl.j₁ ≫ cyl.c ≫ (cyl.p ≫ x) = (cyl.j₁ ≫ cyl.c ≫ cyl.p) ≫ x := by
          simp [Category.assoc]
        _ = 𝟙 B.A₀ ≫ x := by rw [cyl.j₁_c_p]
        _ = x := by simp
  exact ⟨v', hcomp, hrel⟩

/-- A homotopy-terminal base makes its slice forgetful functor acyclic. -/
theorem sliceObj_forget_isAcyclic_of_hTerminal {C : Type (u + 1)} [Category.{u} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [IsCylinderCategory C]
    (X : C) (hX : IsHTerminal X) : IsAcyclic (SliceObj.forget X) := by
  exact ⟨sliceForget_homotopySurjective_of_hTerminal X hX,
    sliceObj_forget_isHomotopyFullyFaithful_of_hTerminal X hX⟩

#print axioms HomotopyHypothesis.Cylinder.SliceCategory.isHTerminal_of_weakEquivalence
#print axioms HomotopyHypothesis.Cylinder.SliceCategory.sliceObj_forget_isHomotopyFullyFaithful_of_hTerminal
#print axioms HomotopyHypothesis.Cylinder.SliceCategory.sliceObj_forget_isAcyclic_of_hTerminal

end

end HomotopyHypothesis.Cylinder.SliceCategory
