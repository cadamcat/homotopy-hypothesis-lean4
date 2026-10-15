import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Cylinder.SliceCategory.Proofs
open CategoryTheory Limits HomotopicalAlgebra HomotopyHypothesis.Henry

universe u

namespace HomotopyHypothesis.Cylinder.SliceCategory

/-- The map from an initial object of a homotopy slice is a cofibration. -/
theorem sliceCofibration_initial {C : Type (u + 1)} [Category.{u} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [IsCylinderCategory C]
    {X : C} {I : SliceObj X} (hI : IsInitial I) (A : SliceObj X) :
    cofibrations (SliceObj X) (hI.to A) := by
  obtain ⟨I_A, hI_A, P_A, k_A, j_A, hPA, m_A, hk_A, hj_A, hm_A⟩ := A.cofibrant
  have hIid : hI_A.to I_A = 𝟙 I_A := hI_A.hom_ext _ _
  have hIdCof : cofibrations C (𝟙 X) :=
    IsCofibrationCategory.isomorphisms_le (𝟙 X)
      (MorphismProperty.isomorphisms.infer_property (𝟙 X))
  have hIdWE : weakEquivalences C (𝟙 X) :=
    IsCylinderCategory.isomorphisms_le_weakEquivalences (C := C) (𝟙 X)
      (MorphismProperty.isomorphisms.infer_property (𝟙 X))
  have hJpo : IsPushout (hI_A.to I_A) (hI_A.to X) (hI_A.to X) (𝟙 X) := by
    rw [hIid]
    exact IsPushout.of_id_fst
  let J : SliceObj X :=
    { A₀ := I_A
      Af := X
      a := hI_A.to X
      x := 𝟙 X
      cofibrant := ⟨I_A, hI_A, X, hI_A.to X, 𝟙 X, hJpo, 𝟙 X, by simp, by simp, hIdCof⟩
      x_cofibration := hIdCof
      x_weakEquivalence := hIdWE }
  have hJ : IsInitial J := by
    refine IsInitial.ofUniqueHom
      (fun Y => (⟨hI_A.to Y.A₀, Y.x, hI_A.hom_ext _ _, by simp [J]⟩ : J ⟶ Y)) ?_
    intro Y g
    apply SliceObj.Hom.ext
    · exact hI_A.hom_ext _ _
    · calc
        g.vf = (𝟙 X) ≫ g.vf := by simp
        _ = J.x ≫ g.vf := rfl
        _ = Y.x := g.x_vf
  let e : I ≅ J := hI.uniqueUpToIso hJ
  let j : J ⟶ A :=
    { v₀ := hI_A.to A.A₀
      vf := A.x
      a_vf := hI_A.hom_ext _ _
      x_vf := by simp [J] }
  have he : e.hom ≫ j = hI.to A := hI.hom_ext _ _
  let e₀ : I.A₀ ≅ J.A₀ :=
    { hom := e.hom.v₀
      inv := e.inv.v₀
      hom_inv_id := congrArg (fun g : I ⟶ I => g.v₀) e.hom_inv_id
      inv_hom_id := congrArg (fun g : J ⟶ J => g.v₀) e.inv_hom_id }
  let e_f : I.Af ≅ J.Af :=
    { hom := e.hom.vf
      inv := e.inv.vf
      hom_inv_id := congrArg (fun g : I ⟶ I => g.vf) e.hom_inv_id
      inv_hom_id := congrArg (fun g : J ⟶ J => g.vf) e.inv_hom_id }
  haveI : IsIso e.hom.v₀ := e₀.isIso_hom
  haveI : IsIso e.hom.vf := e_f.isIso_hom
  have hE₀ : cofibrations C e.hom.v₀ :=
    IsCofibrationCategory.isomorphisms_le e.hom.v₀
      (MorphismProperty.isomorphisms.infer_property e.hom.v₀)
  have hJ₀ : cofibrations C j.v₀ := IsCofibrationCategory.initial_cofibration hI_A A.A₀
  have hI₀ : cofibrations C (hI.to A).v₀ := by
    have he₀ : e.hom.v₀ ≫ j.v₀ = (hI.to A).v₀ := congrArg (fun g : I ⟶ A => g.v₀) he
    have hc := (IsCofibrationCategory.isMultiplicative (C := C)).comp_mem
      e.hom.v₀ j.v₀ hE₀ hJ₀
    rw [he₀] at hc
    exact hc
  have hJpush : IsPushout J.a j.v₀ j_A k_A := hPA.flip
  have heInv : e.inv ≫ (hI.to A) = j := by
    calc
      e.inv ≫ (hI.to A) = e.inv ≫ (e.hom ≫ j) := by rw [he]
      _ = (e.inv ≫ e.hom) ≫ j := by simp [Category.assoc]
      _ = 𝟙 J ≫ j := by rw [e.inv_hom_id]
      _ = j := by simp
  have heInv₀ : e.inv.v₀ ≫ (hI.to A).v₀ = j.v₀ :=
    congrArg (fun g : J ⟶ A => g.v₀) heInv
  have hInvf : e.inv.vf ≫ e.hom.vf = 𝟙 J.Af :=
    congrArg (fun g : J ⟶ J => g.vf) e.inv_hom_id
  have hIpush : IsPushout I.a (hI.to A).v₀ (e.hom.vf ≫ j_A) k_A := by
    apply hJpush.of_iso e₀.symm e_f.symm (Iso.refl A.A₀) (Iso.refl P_A)
    · simpa [e₀, e_f, J] using e.inv.a_vf
    · simpa [e₀] using heInv₀.symm
    · calc
        j_A ≫ 𝟙 P_A = (e.inv.vf ≫ e.hom.vf) ≫ j_A := by rw [hInvf]; simp
        _ = e.inv.vf ≫ (e.hom.vf ≫ j_A) := by simp [Category.assoc]
    · simp
  have hTop : (e.hom.vf ≫ j_A) ≫ m_A = (hI.to A).vf := by
    calc
      (e.hom.vf ≫ j_A) ≫ m_A = e.hom.vf ≫ (j_A ≫ m_A) := by simp [Category.assoc]
      _ = e.hom.vf ≫ A.x := by rw [hj_A]
      _ = (e.hom ≫ j).vf := rfl
      _ = (hI.to A).vf := by rw [he]
  have hG : IsCofibrantGluing I.a (hI.to A).v₀ (hI.to A).vf A.a :=
    ⟨P_A, e.hom.vf ≫ j_A, k_A, hIpush, m_A, hTop, hk_A, hm_A⟩
  change cofibrations C (hI.to A).v₀ ∧
    IsCofibrantGluing I.a (hI.to A).v₀ (hI.to A).vf A.a
  exact ⟨hI₀, hG⟩

#print axioms HomotopyHypothesis.Cylinder.SliceCategory.sliceCofibration_initial

end HomotopyHypothesis.Cylinder.SliceCategory
