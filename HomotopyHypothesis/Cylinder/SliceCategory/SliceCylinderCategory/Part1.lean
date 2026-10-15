import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Cylinder.SliceCategory.ForgetFactorization
import HomotopyHypothesis.Cylinder.SliceCategory.ForgetPreFibration
import HomotopyHypothesis.Cylinder.SliceCategory.ForgetRetraction
import HomotopyHypothesis.Cylinder.SliceCategory.Proofs
import HomotopyHypothesis.Cylinder.SliceCategory.SliceCofibrationCategory.Part1
import HomotopyHypothesis.Cylinder.SliceCategory.SliceInitialCofibration
import HomotopyHypothesis.Cylinder.SliceCategory.SlicePushout
import HomotopyHypothesis.Cylinder.SliceCategory.SliceWeakAxioms
import HomotopyHypothesis.Category.SemiModelStructure.CylinderFacts

/-!
# `HomotopyHypothesis.Cylinder.SliceCategory.SliceCylinderCategory`, part 1

Lines 15–148 of `HomotopyHypothesis.Cylinder.SliceCategory.SliceCylinderCategory`, split so that the modules of the development form an acyclic import graph.
-/

open CategoryTheory Limits HomotopicalAlgebra HomotopyHypothesis.Henry

universe u

namespace HomotopyHypothesis.Cylinder.SliceCategory

noncomputable section

/-- A homotopy-slice cofibration has a relative cylinder built by factoring its fold map. -/
theorem slice_relativeCylinder {C : Type (u + 1)} [Category.{u} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [IsCylinderCategory C]
    {X : C} {A B : SliceObj X} (i : A ⟶ B)
    (hi : cofibrations (SliceObj X) i) : Nonempty (RelativeCylinder i) := by
  obtain ⟨P, j₀, j₁, hP, _, _, _, _⟩ := slice_pushout_exists i i hi
  let d : P ⟶ B := hP.desc (𝟙 B) (𝟙 B) (by simp)
  obtain ⟨Q, c₀, p₀, hc₀, hp₀, hfactor⟩ :=
    HomotopyHypothesis.Category.SemiModelStructure.brown_factorization d.v₀
  obtain ⟨I, c, p, e, hc, hp, hcp, _, _⟩ :=
    sliceForget_lift_factorization X d c₀ p₀ hc₀ hp₀ hfactor
  refine ⟨{
    P := P
    j₀ := j₀
    j₁ := j₁
    isPushout := hP
    I := I
    c := c
    p := p
    c_mem := hc
    p_mem := hp
    j₀_c_p := ?_
    j₁_c_p := ?_ }⟩
  · calc
      j₀ ≫ c ≫ p = j₀ ≫ (c ≫ p) := by simp [Category.assoc]
      _ = j₀ ≫ d := by rw [hcp]
      _ = 𝟙 B := by simp [d, hP]
  · calc
      j₁ ≫ c ≫ p = j₁ ≫ (c ≫ p) := by simp [Category.assoc]
      _ = j₁ ≫ d := by rw [hcp]
      _ = 𝟙 B := by simp [d, hP]

/-- The standard initial slice object has an initial underlying object. -/
theorem slice_exists_initial_with_baseInitial {C : Type (u + 1)} [Category.{u} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [IsCylinderCategory C]
    (X : C) :
    ∃ J : SliceObj X, Nonempty (IsInitial J) ∧ Nonempty (IsInitial J.A₀) := by
  obtain ⟨I, hIne⟩ := IsCofibrationCategory.exists_initial (C := C)
  let hI : IsInitial I := Classical.choice hIne
  have hIdCof : cofibrations C (𝟙 X) :=
    IsCofibrationCategory.isomorphisms_le (𝟙 X)
      (MorphismProperty.isomorphisms.infer_property (𝟙 X))
  have hIdWE : weakEquivalences C (𝟙 X) :=
    IsCylinderCategory.isomorphisms_le_weakEquivalences (C := C) (𝟙 X)
      (MorphismProperty.isomorphisms.infer_property (𝟙 X))
  have hIid : hI.to I = 𝟙 I := hI.hom_ext _ _
  have hJpo : IsPushout (hI.to I) (hI.to X) (hI.to X) (𝟙 X) := by
    rw [hIid]
    exact IsPushout.of_id_fst
  have hPair : IsCofibrantPair (hI.to X) (𝟙 X) := by
    refine ⟨I, hI, X, hI.to X, 𝟙 X, hJpo, 𝟙 X, ?_, ?_, hIdCof⟩
    · simp
    · simp
  let J : SliceObj X :=
    { A₀ := I
      Af := X
      a := hI.to X
      x := 𝟙 X
      cofibrant := hPair
      x_cofibration := hIdCof
      x_weakEquivalence := hIdWE }
  have hJ : IsInitial J := by
    refine IsInitial.ofUniqueHom
      (fun Y => (⟨hI.to Y.A₀, Y.x, hI.hom_ext _ _, by simp [J]⟩ : J ⟶ Y)) ?_
    intro Y f
    apply SliceObj.Hom.ext
    · exact hI.hom_ext _ _
    · calc
        f.vf = 𝟙 X ≫ f.vf := by simp
        _ = J.x ≫ f.vf := rfl
        _ = Y.x := f.x_vf
  exact ⟨J, ⟨hJ⟩, ⟨hI⟩⟩

/-- The forgetful functor from a homotopy slice is a cylinder morphism. -/
theorem sliceForget_isCylinderMorphism {C : Type (u + 1)} [Category.{u} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [IsCylinderCategory C]
    (X : C) : IsCylinderMorphism (SliceObj.forget X) where
  map_cofibration := by
    intro A B f hf
    exact hf.1
  map_initial := by
    intro I hI
    obtain ⟨J, hJne, hJ₀⟩ := slice_exists_initial_with_baseInitial X
    let hJ : IsInitial J := Classical.choice hJne
    let hJ₀ : IsInitial J.A₀ := Classical.choice hJ₀
    let e : I ≅ J := hI.uniqueUpToIso hJ
    let e₀ : I.A₀ ≅ J.A₀ :=
      { hom := e.hom.v₀
        inv := e.inv.v₀
        hom_inv_id := congrArg (fun f : I ⟶ I => f.v₀) e.hom_inv_id
        inv_hom_id := congrArg (fun f : J ⟶ J => f.v₀) e.inv_hom_id }
    exact ⟨IsInitial.ofIso hJ₀ e₀.symm⟩
  map_isPushout := by
    intro A B D P i f k j h hi
    exact sliceForget_map_isPushout h hi
  map_weakEquivalence := by
    intro A B f hf
    exact hf

/-- Every homotopy slice is a cylinder category. -/
theorem slice_isCylinderCategory {C : Type (u + 1)} [Category.{u} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [IsCylinderCategory C]
    (X : C) : IsCylinderCategory (SliceObj X) where
  toIsCofibrationCategory := slice_isCofibrationCategory X
  isomorphisms_le_weakEquivalences := (sliceObj_weakEquivalence_axioms X).1
  weakEquivalences_isMultiplicative := (sliceObj_weakEquivalence_axioms X).2.1
  twoOutOfSix := (sliceObj_weakEquivalence_axioms X).2.2
  trivialCofibration_cobaseChange := by
    intro A B D P i f k j h hi hw
    exact sliceTrivialCofibration_cobaseChange i f k j h hi hw
  exists_cylinder := by
    intro I hI A
    exact slice_relativeCylinder (hI.to A) (sliceCofibration_initial hI A)
  exists_retraction := by
    intro A B i hi hw
    have hiSlice := hi
    have hwSlice := hw
    change cofibrations C i.v₀ ∧ IsCofibrantGluing A.a i.v₀ i.vf B.a at hi
    have hi₀ := hi.1
    change weakEquivalences C i.v₀ at hw
    obtain ⟨r₀, hr₀⟩ := IsCylinderCategory.exists_retraction (C := C) i.v₀ hi₀ hw
    obtain ⟨r, hri, _⟩ := sliceForget_lift_retraction X i hiSlice hwSlice r₀ hr₀
    exact ⟨r, hri⟩

/-- H Proposition 4.4.1: the forgetful map from a homotopy slice is a lifting target. -/
theorem sliceObj_isLiftingTarget_proof {C : Type (u + 1)} [Category.{u} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [IsCylinderCategory C]
    (X : C) :
    IsLiftingTarget false (SliceObj X) C (SliceObj.forget X) := by
  refine ⟨slice_isCylinderCategory X, inferInstance, sliceForget_isCylinderMorphism X,
    sliceForget_isPreFibration X, sliceForget_isIsofibration X, ?_⟩
  intro h
  cases h
