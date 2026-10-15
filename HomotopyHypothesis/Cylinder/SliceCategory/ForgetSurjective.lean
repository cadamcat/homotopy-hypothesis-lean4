import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Cylinder.SliceCategory.Proofs
import HomotopyHypothesis.Category.SemiModelStructure.CylinderFacts
open CategoryTheory Limits HomotopicalAlgebra HomotopyHypothesis.Henry

universe u

namespace HomotopyHypothesis.Cylinder.SliceCategory

/-- An h-terminal base makes the homotopy-slice forgetful functor homotopy surjective. -/
theorem sliceForget_homotopySurjective_of_hTerminal {C : Type (u + 1)} [Category.{u} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [IsCylinderCategory C]
    (X : C) (hX : IsHTerminal X) :
    IsHomotopySurjective (SliceObj.forget X) := by
  intro Y
  obtain ⟨I, hI_nonempty⟩ := IsCofibrationCategory.exists_initial (C := C)
  let hI : IsInitial I := Classical.choice hI_nonempty
  have hIY : cofibrations C (hI.to Y) :=
    IsCofibrationCategory.initial_cofibration hI Y
  have hIX : cofibrations C (hI.to X) :=
    IsCofibrationCategory.initial_cofibration hI X
  obtain ⟨f, hf⟩ := hX (hI.to Y) hIY (hI.to X)
  letI : HasPushout (hI.to Y) (hI.to X) :=
    IsCofibrationCategory.hasPushout (C := C) (hI.to Y) (hI.to X) hIY
  let P := pushout (hI.to Y) (hI.to X)
  let k : Y ⟶ P := pushout.inl (hI.to Y) (hI.to X)
  let j : X ⟶ P := pushout.inr (hI.to Y) (hI.to X)
  let hP : IsPushout (hI.to Y) (hI.to X) k j :=
    IsPushout.of_hasPushout (hI.to Y) (hI.to X)
  have hcompat : (hI.to Y) ≫ f = (hI.to X) ≫ 𝟙 X := by
    rw [hf]
    simp
  let q : P ⟶ X := hP.desc f (𝟙 X) hcompat
  obtain ⟨Z, c, w, hc, hw, hcw⟩ :=
    HomotopyHypothesis.Category.SemiModelStructure.brown_factorization q
  have hj : cofibrations C j :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout hP.flip hIY
  have hjc : cofibrations C (j ≫ c) :=
    (IsCofibrationCategory.isMultiplicative (C := C)).comp_mem j c hj hc
  have hXid_eq : (j ≫ c) ≫ w = 𝟙 X := by
    calc
      (j ≫ c) ≫ w = j ≫ (c ≫ w) := by simp [Category.assoc]
      _ = j ≫ q := by rw [hcw]
      _ = 𝟙 X := by simp [q, hP]
  have hid : weakEquivalences C (𝟙 X) :=
    IsCylinderCategory.isomorphisms_le_weakEquivalences (C := C) (𝟙 X)
      (MorphismProperty.isomorphisms.infer_property (𝟙 X))
  have hXid : weakEquivalences C ((j ≫ c) ≫ w) := by
    rw [hXid_eq]
    exact hid
  have hwid : weakEquivalences C (w ≫ 𝟙 X) := by simpa using hw
  have hxwe : weakEquivalences C (j ≫ c) :=
    (IsCylinderCategory.twoOutOfSix (C := C) (j ≫ c) w (𝟙 X) hXid hwid).1
  have hpairs : IsCofibrantPair (k ≫ c) (j ≫ c) := by
    refine ⟨I, hI, P, k, j, hP, c, ?_, ?_, hc⟩
    · rfl
    · rfl
  let A : SliceObj X :=
    { A₀ := Y
      Af := Z
      a := k ≫ c
      x := j ≫ c
      cofibrant := hpairs
      x_cofibration := hjc
      x_weakEquivalence := hxwe }
  have hidY : weakEquivalences C (𝟙 Y) :=
    IsCylinderCategory.isomorphisms_le_weakEquivalences (C := C) (𝟙 Y)
      (MorphismProperty.isomorphisms.infer_property (𝟙 Y))
  exact ⟨A, 𝟙 Y, hidY⟩

#print axioms HomotopyHypothesis.Cylinder.SliceCategory.sliceForget_homotopySurjective_of_hTerminal

end HomotopyHypothesis.Cylinder.SliceCategory
