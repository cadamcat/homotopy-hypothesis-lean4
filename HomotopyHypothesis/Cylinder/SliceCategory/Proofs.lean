import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiModel
open CategoryTheory Limits HomotopicalAlgebra HomotopyHypothesis.Henry

universe u

namespace HomotopyHypothesis.Cylinder.SliceCategory

variable {C : Type (u + 1)} [Category.{u} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [IsCylinderCategory C]

omit [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [IsCylinderCategory C] in
private lemma initial_arrow_iso {I B B' : C} (hI : IsInitial I) (e : B' ≅ B) :
    hI.to B' ≫ e.hom = hI.to B := by
  exact hI.hom_ext _ _

/-- Reindexing a cofibrant pair along isomorphisms preserves cofibrancy. -/
theorem cofibrantPair_transport {B B' X T T' : C} {u : B ⟶ T} {w : X ⟶ T}
    (h : IsCofibrantPair u w) (eB : B' ≅ B) (eT : T ≅ T') :
    IsCofibrantPair (eB.hom ≫ u ≫ eT.hom) (w ≫ eT.hom) := by
  obtain ⟨I, hI, P, k, j, hpo, m, hkm, hjm, hm⟩ := h
  refine ⟨I, hI, P, eB.hom ≫ k, j, ?_, m ≫ eT.hom, ?_, ?_, ?_⟩
  · apply hpo.of_iso (Iso.refl I) eB.symm (Iso.refl X) (Iso.refl P)
    · calc
        hI.to B ≫ eB.inv = (hI.to B' ≫ eB.hom) ≫ eB.inv := by rw [initial_arrow_iso hI eB]
        _ = (Iso.refl I).hom ≫ hI.to B' := by simp [Iso.refl]
    · simp [Iso.refl]
    · simp [Iso.refl]
    · simp [Iso.refl]
  · calc
      (eB.hom ≫ k) ≫ (m ≫ eT.hom) = eB.hom ≫ (k ≫ m) ≫ eT.hom := by simp [Category.assoc]
      _ = eB.hom ≫ u ≫ eT.hom := by rw [hkm]
  · calc
      j ≫ (m ≫ eT.hom) = (j ≫ m) ≫ eT.hom := by simp [Category.assoc]
      _ = w ≫ eT.hom := by rw [hjm]
  · have heT : cofibrations C eT.hom :=
      IsCofibrationCategory.isomorphisms_le eT.hom (inferInstanceAs (IsIso eT.hom))
    exact (IsCofibrationCategory.isMultiplicative (C := C)).comp_mem m eT.hom hm heT

/-- The second component of a morphism in a homotopy slice is a weak equivalence. -/
theorem sliceHom_vf_weakEquivalence {X : C} {A B : SliceObj X} (f : A ⟶ B) :
    weakEquivalences C f.vf := by
  have h₁ : weakEquivalences C ((𝟙 X) ≫ A.x) := by simpa using A.x_weakEquivalence
  have h₂ : weakEquivalences C (A.x ≫ f.vf) := by rw [f.x_vf]; exact B.x_weakEquivalence
  exact (IsCylinderCategory.twoOutOfSix (C := C) (𝟙 X) A.x f.vf h₁ h₂).2.2.1

/-- A cofibration in a homotopy slice has a cofibration as its second component. -/
theorem sliceHom_vf_cofibration {X : C} {A B : SliceObj X} (f : A ⟶ B)
    (hf : cofibrations (SliceObj X) f) : cofibrations C f.vf := by
  rcases hf with ⟨h₀, hglue⟩
  rcases hglue with ⟨P, k, j, hpo, m, hkm, hjm, hm⟩
  have hk : cofibrations C k :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout hpo h₀
  have hkm_cof := (IsCofibrationCategory.isMultiplicative (C := C)).comp_mem k m hk hm
  rw [hkm] at hkm_cof
  exact hkm_cof

/-- The first structure map of a homotopy-slice object is a cofibration. -/
theorem sliceObj_a_cofibration {X : C} (A : SliceObj X) : cofibrations C A.a := by
  obtain ⟨I, hI, P, k, j, hpo, m, hkm, hjm, hm⟩ := A.cofibrant
  have hX : cofibrations C (hI.to X) := IsCofibrationCategory.initial_cofibration hI X
  have hk : cofibrations C k :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout hpo hX
  have hcomp := (IsCofibrationCategory.isMultiplicative (C := C)).comp_mem k m hk hm
  rw [hkm] at hcomp
  exact hcomp

/-- The forgetful functor from a homotopy slice lifts isomorphisms. -/
theorem sliceForget_isIsofibration (X : C) : IsIsofibration (SliceObj.forget X) := by
  intro A Y e
  change A.A₀ ≅ Y at e
  let A' : SliceObj X :=
    { A₀ := Y
      Af := A.Af
      a := e.inv ≫ A.a
      x := A.x
      cofibrant := by
        convert cofibrantPair_transport A.cofibrant e.symm (Iso.refl A.Af) using 1 <;> simp
      x_cofibration := A.x_cofibration
      x_weakEquivalence := A.x_weakEquivalence }
  let e' : A ≅ A' :=
    { hom := (⟨e.hom, 𝟙 A.Af, by
          dsimp [A']
          rw [Category.comp_id]
          change A.a = e.hom ≫ (e.inv ≫ A.a)
          rw [← Category.assoc, e.hom_inv_id, Category.id_comp]
        , by simp [A']⟩ : A ⟶ A')
      inv := (⟨e.inv, 𝟙 A.Af, by
          simp [A']
        , by simp [A']⟩ : A' ⟶ A)
      hom_inv_id := by
        apply SliceObj.Hom.ext
        · exact e.hom_inv_id
        · change 𝟙 A.Af ≫ 𝟙 A.Af = 𝟙 A.Af
          simp
      inv_hom_id := by
        apply SliceObj.Hom.ext
        · exact e.inv_hom_id
        · change 𝟙 A.Af ≫ 𝟙 A.Af = 𝟙 A.Af
          simp }
  refine ⟨A', e', rfl, ?_⟩
  change e.hom = e.hom ≫ eqToHom rfl
  simp

end HomotopyHypothesis.Cylinder.SliceCategory

#print axioms HomotopyHypothesis.Cylinder.SliceCategory.cofibrantPair_transport
#print axioms HomotopyHypothesis.Cylinder.SliceCategory.sliceHom_vf_weakEquivalence
#print axioms HomotopyHypothesis.Cylinder.SliceCategory.sliceHom_vf_cofibration
#print axioms HomotopyHypothesis.Cylinder.SliceCategory.sliceObj_a_cofibration
#print axioms HomotopyHypothesis.Cylinder.SliceCategory.sliceForget_isIsofibration
