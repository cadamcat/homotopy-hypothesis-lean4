import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Cylinder.SliceCategory.Proofs
import HomotopyHypothesis.Cylinder.SliceCategory.SliceCofibrationAxioms
open CategoryTheory Limits HomotopicalAlgebra HomotopyHypothesis.Henry

universe u

namespace HomotopyHypothesis.Cylinder.SliceCategory

noncomputable section

/-- Pushouts along Reedy cofibrations exist in a homotopy slice. -/
theorem slice_pushout_exists {C : Type (u + 1)} [Category.{u} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [IsCylinderCategory C]
    {X : C} {A B D : SliceObj X} (f : A ⟶ B) (g : A ⟶ D)
    (hf : cofibrations (SliceObj X) f) :
    ∃ (P : SliceObj X) (u : B ⟶ P) (v : D ⟶ P),
      IsPushout f g u v ∧ IsPushout f.v₀ g.v₀ u.v₀ v.v₀ ∧
        IsPushout f.vf g.vf u.vf v.vf ∧ cofibrations (SliceObj X) v ∧
          (weakEquivalences C f.v₀ → weakEquivalences C v.v₀) := by
  classical
  rcases hf with ⟨hf₀, hfglue⟩
  rcases hfglue with ⟨Q, qAf, qB₀, hQ, m, hmAf, hmB₀, hm⟩
  obtain ⟨I, hIne⟩ := IsCofibrationCategory.exists_initial (C := C)
  let hI : IsInitial I := Classical.choice hIne
  letI : HasPushout f.v₀ g.v₀ :=
    IsCofibrationCategory.hasPushout (C := C) f.v₀ g.v₀ hf₀
  let P₀ := pushout f.v₀ g.v₀
  let k₀ : B.A₀ ⟶ P₀ := pushout.inl f.v₀ g.v₀
  let j₀ : D.A₀ ⟶ P₀ := pushout.inr f.v₀ g.v₀
  let hP₀ : IsPushout f.v₀ g.v₀ k₀ j₀ := IsPushout.of_hasPushout f.v₀ g.v₀
  have hfvf : cofibrations C f.vf := sliceHom_vf_cofibration f ⟨hf₀, ⟨Q, qAf, qB₀, hQ, m, hmAf, hmB₀, hm⟩⟩
  have hgvf : weakEquivalences C g.vf := sliceHom_vf_weakEquivalence g
  have hfvfwe : weakEquivalences C f.vf := sliceHom_vf_weakEquivalence f
  letI : HasPushout f.vf g.vf :=
    IsCofibrationCategory.hasPushout (C := C) f.vf g.vf hfvf
  let P_f := pushout f.vf g.vf
  let k_f : B.Af ⟶ P_f := pushout.inl f.vf g.vf
  let j_f : D.Af ⟶ P_f := pushout.inr f.vf g.vf
  let hP_f : IsPushout f.vf g.vf k_f j_f := IsPushout.of_hasPushout f.vf g.vf
  let aP : P₀ ⟶ P_f := hP₀.desc (B.a ≫ k_f) (D.a ≫ j_f) (by
    calc
      f.v₀ ≫ (B.a ≫ k_f) = (f.v₀ ≫ B.a) ≫ k_f := by simp [Category.assoc]
      _ = (A.a ≫ f.vf) ≫ k_f := by rw [f.a_vf]
      _ = A.a ≫ (f.vf ≫ k_f) := by simp [Category.assoc]
      _ = A.a ≫ (g.vf ≫ j_f) := by rw [hP_f.w]
      _ = (A.a ≫ g.vf) ≫ j_f := by simp [Category.assoc]
      _ = (g.v₀ ≫ D.a) ≫ j_f := by rw [g.a_vf]
      _ = g.v₀ ≫ (D.a ≫ j_f) := by simp [Category.assoc])
  let xP : X ⟶ P_f := D.x ≫ j_f
  have hxcompat : B.x ≫ k_f = xP := by
    calc
      B.x ≫ k_f = (A.x ≫ f.vf) ≫ k_f := by rw [f.x_vf]
      _ = A.x ≫ (f.vf ≫ k_f) := by simp [Category.assoc]
      _ = A.x ≫ (g.vf ≫ j_f) := by rw [hP_f.w]
      _ = (A.x ≫ g.vf) ≫ j_f := by simp [Category.assoc]
      _ = D.x ≫ j_f := by rw [g.x_vf]
  have hxcof : cofibrations C xP := by
    have hjf : cofibrations C j_f :=
      (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout hP_f.flip hfvf
    exact (IsCofibrationCategory.isMultiplicative (C := C)).comp_mem D.x j_f D.x_cofibration hjf
  have hjfwe : weakEquivalences C j_f :=
    IsCylinderCategory.trivialCofibration_cobaseChange (C := C)
      f.vf g.vf k_f j_f hP_f hfvf hfvfwe
  have hxwe : weakEquivalences C xP :=
    (IsCylinderCategory.weakEquivalences_isMultiplicative (C := C)).comp_mem D.x j_f
      D.x_weakEquivalence hjfwe
  let P : SliceObj X :=
    { A₀ := P₀
      Af := P_f
      a := aP
      x := xP
      cofibrant := by
        obtain ⟨I_A, hI_A, S_A, sA₀, sAX, hS_A, mA, hmA₀, hmAX, hmA⟩ := A.cofibrant
        obtain ⟨I_D, hI_D, S_D, sD₀, sDX, hS_D, mD, hmD₀, hmDX, hmD⟩ := D.cofibrant
        letI : HasPushout (hI.to P₀) (hI.to X) :=
          IsCofibrationCategory.hasPushout (C := C) (hI.to P₀) (hI.to X)
            (IsCofibrationCategory.initial_cofibration hI P₀)
        let S_P := pushout (hI.to P₀) (hI.to X)
        let sP₀ : P₀ ⟶ S_P := pushout.inl (hI.to P₀) (hI.to X)
        let sPX : X ⟶ S_P := pushout.inr (hI.to P₀) (hI.to X)
        let hS_P : IsPushout (hI.to P₀) (hI.to X) sP₀ sPX :=
          IsPushout.of_hasPushout (hI.to P₀) (hI.to X)
        let sD : S_D ⟶ S_P := hS_D.desc (j₀ ≫ sP₀) sPX (by
          exact hI_D.hom_ext _ _)
        have hsD₀ : sD₀ ≫ sD = j₀ ≫ sP₀ := by simp [sD, hS_D]
        have hsDX : sDX ≫ sD = sPX := by simp [sD, hS_D]
        letI : HasPushout mD sD :=
          IsCofibrationCategory.hasPushout (C := C) mD sD hmD
        let R₁ := pushout mD sD
        let rS : S_P ⟶ R₁ := pushout.inr mD sD
        let rDf : D.Af ⟶ R₁ := pushout.inl mD sD
        let hR₁ : IsPushout mD sD rDf rS := IsPushout.of_hasPushout mD sD
        let qR₁ : Q ⟶ R₁ := hQ.desc (g.vf ≫ rDf) (k₀ ≫ sP₀ ≫ rS) (by
          calc
            A.a ≫ (g.vf ≫ rDf) = (A.a ≫ g.vf) ≫ rDf := by simp [Category.assoc]
            _ = (g.v₀ ≫ D.a) ≫ rDf := by rw [g.a_vf]
            _ = g.v₀ ≫ (D.a ≫ rDf) := by simp [Category.assoc]
            _ = g.v₀ ≫ ((sD₀ ≫ mD) ≫ rDf) := by rw [← hmD₀]
            _ = (g.v₀ ≫ sD₀) ≫ (mD ≫ rDf) := by simp [Category.assoc]
            _ = g.v₀ ≫ sD₀ ≫ (sD ≫ rS) := by rw [hR₁.w]; simp [Category.assoc]
            _ = g.v₀ ≫ (sD₀ ≫ sD) ≫ rS := by simp [Category.assoc]
            _ = g.v₀ ≫ (j₀ ≫ sP₀) ≫ rS := by rw [hsD₀]
            _ = (g.v₀ ≫ j₀) ≫ sP₀ ≫ rS := by simp [Category.assoc]
            _ = (f.v₀ ≫ k₀) ≫ sP₀ ≫ rS := by rw [hP₀.w]
            _ = f.v₀ ≫ (k₀ ≫ sP₀ ≫ rS) := by simp [Category.assoc])
        have hqR₁k : qAf ≫ qR₁ = g.vf ≫ rDf := by simp [qR₁, hQ]
        have hqR₁j : qB₀ ≫ qR₁ = k₀ ≫ sP₀ ≫ rS := by simp [qR₁, hQ]
        letI : HasPushout m qR₁ :=
          IsCofibrationCategory.hasPushout (C := C) m qR₁ hm
        let R := pushout m qR₁
        let r₁ : R₁ ⟶ R := pushout.inr m qR₁
        let rBf : B.Af ⟶ R := pushout.inl m qR₁
        let hR : IsPushout m qR₁ rBf r₁ := IsPushout.of_hasPushout m qR₁
        let sPf : S_P ⟶ P_f := hS_P.desc aP xP (by exact hI.hom_ext _ _)
        have hsPf₀ : sP₀ ≫ sPf = aP := by simp [sPf, hS_P]
        have hsPfX : sPX ≫ sPf = xP := by simp [sPf, hS_P]
        let rPf : R₁ ⟶ P_f := hR₁.desc j_f sPf (by
          apply hS_D.hom_ext
          · calc
              sD₀ ≫ mD ≫ j_f = (sD₀ ≫ mD) ≫ j_f := by simp [Category.assoc]
              _ = D.a ≫ j_f := by rw [hmD₀]
              _ = j₀ ≫ aP := by simp [aP]
              _ = j₀ ≫ sP₀ ≫ sPf := by rw [← hsPf₀]
              _ = (j₀ ≫ sP₀) ≫ sPf := by simp [Category.assoc]
              _ = (sD₀ ≫ sD) ≫ sPf := by rw [← hsD₀]
              _ = sD₀ ≫ sD ≫ sPf := by simp [Category.assoc]
          · calc
              sDX ≫ mD ≫ j_f = (sDX ≫ mD) ≫ j_f := by simp [Category.assoc]
              _ = D.x ≫ j_f := by rw [hmDX]
              _ = xP := rfl
              _ = sPX ≫ sPf := by rw [← hsPfX]
              _ = (sDX ≫ sD) ≫ sPf := by rw [← hsDX]
              _ = sDX ≫ sD ≫ sPf := by simp [Category.assoc])
        have hrPfS : rS ≫ rPf = sPf := by simp [rPf, hR₁]
        have hrPfD : rDf ≫ rPf = j_f := by simp [rPf, hR₁]
        have hqRpf : qR₁ ≫ rPf = m ≫ k_f := by
          apply hQ.hom_ext
          · calc
              qAf ≫ qR₁ ≫ rPf = (qAf ≫ qR₁) ≫ rPf := by simp [Category.assoc]
              _ = (g.vf ≫ rDf) ≫ rPf := by rw [hqR₁k]
              _ = g.vf ≫ rDf ≫ rPf := by simp [Category.assoc]
              _ = g.vf ≫ j_f := by rw [hrPfD]
              _ = f.vf ≫ k_f := by rw [hP_f.w]
              _ = (qAf ≫ m) ≫ k_f := by rw [← hmAf]
              _ = qAf ≫ m ≫ k_f := by simp [Category.assoc]
              _ = qAf ≫ (m ≫ k_f) := by simp [Category.assoc]
          · calc
              qB₀ ≫ qR₁ ≫ rPf = (qB₀ ≫ qR₁) ≫ rPf := by simp [Category.assoc]
              _ = (k₀ ≫ sP₀ ≫ rS) ≫ rPf := by rw [hqR₁j]
              _ = k₀ ≫ sP₀ ≫ rS ≫ rPf := by simp [Category.assoc]
              _ = k₀ ≫ sP₀ ≫ sPf := by rw [hrPfS]
              _ = k₀ ≫ aP := by rw [hsPf₀]
              _ = B.a ≫ k_f := by simp [aP]
              _ = (qB₀ ≫ m) ≫ k_f := by rw [← hmB₀]
              _ = qB₀ ≫ m ≫ k_f := by simp [Category.assoc]
              _ = qB₀ ≫ (m ≫ k_f) := by simp [Category.assoc]
        have hpush_m : IsPushout m qR₁ k_f rPf := by
          refine IsPushout.mk' hqRpf.symm ?_ ?_
          · intro T t t' hB hR
            apply hP_f.hom_ext
            · exact hB
            · calc
                j_f ≫ t = (rDf ≫ rPf) ≫ t := by rw [← hrPfD]
                _ = rDf ≫ (rPf ≫ t) := by simp [Category.assoc]
                _ = rDf ≫ (rPf ≫ t') := by rw [hR]
                _ = (rDf ≫ rPf) ≫ t' := by simp [Category.assoc]
                _ = j_f ≫ t' := by rw [hrPfD]
          intro T sB sR hs
          let sCf : D.Af ⟶ T := rDf ≫ sR
          have hsAf : f.vf ≫ sB = g.vf ≫ sCf := by
            calc
              f.vf ≫ sB = (qAf ≫ m) ≫ sB := by rw [← hmAf]
              _ = qAf ≫ (m ≫ sB) := by simp [Category.assoc]
              _ = qAf ≫ (qR₁ ≫ sR) := by rw [hs]
              _ = qAf ≫ qR₁ ≫ sR := by simp [Category.assoc]
              _ = (qAf ≫ qR₁) ≫ sR := by simp [Category.assoc]
              _ = (g.vf ≫ rDf) ≫ sR := by rw [hqR₁k]
              _ = g.vf ≫ rDf ≫ sR := by simp [Category.assoc]
              _ = g.vf ≫ sCf := by simp [sCf, Category.assoc]
          let t : P_f ⟶ T := hP_f.desc sB sCf hsAf
          refine ⟨t, ?_, ?_⟩
          · simp [t, hP_f]
          · apply hR₁.hom_ext
            · calc
                rDf ≫ rPf ≫ t = (rDf ≫ rPf) ≫ t := by simp [Category.assoc]
                _ = j_f ≫ t := by rw [hrPfD]
                _ = sCf := by simp [t, hP_f]
                _ = rDf ≫ sR := rfl
            · calc
                rS ≫ rPf ≫ t = sPf ≫ t := by
                  simpa [Category.assoc] using congrArg (fun z => z ≫ t) hrPfS
                _ = rS ≫ sR := by
                  apply hS_P.hom_ext
                  · apply hP₀.hom_ext
                    · calc
                        k₀ ≫ sP₀ ≫ sPf ≫ t = k₀ ≫ aP ≫ t := by
                          simpa [Category.assoc] using congrArg (fun z => k₀ ≫ z ≫ t) hsPf₀
                        _ = B.a ≫ k_f ≫ t := by simp [aP]
                        _ = B.a ≫ sB := by simp [t, hP_f]
                        _ = (qB₀ ≫ m) ≫ sB := by rw [← hmB₀]
                        _ = qB₀ ≫ m ≫ sB := by simp [Category.assoc]
                        _ = qB₀ ≫ (m ≫ sB) := by simp [Category.assoc]
                        _ = qB₀ ≫ (qR₁ ≫ sR) := by rw [hs]
                        _ = qB₀ ≫ qR₁ ≫ sR := by simp [Category.assoc]
                        _ = (qB₀ ≫ qR₁) ≫ sR := by simp [Category.assoc]
                        _ = (k₀ ≫ sP₀ ≫ rS) ≫ sR := by rw [hqR₁j]
                        _ = k₀ ≫ sP₀ ≫ rS ≫ sR := by simp [Category.assoc]
                    · calc
                        j₀ ≫ sP₀ ≫ sPf ≫ t = j₀ ≫ aP ≫ t := by
                          simpa [Category.assoc] using congrArg (fun z => j₀ ≫ z ≫ t) hsPf₀
                        _ = D.a ≫ j_f ≫ t := by simp [aP]
                        _ = D.a ≫ sCf := by simp [t, hP_f]
                        _ = D.a ≫ (rDf ≫ sR) := rfl
                        _ = (sD₀ ≫ mD) ≫ (rDf ≫ sR) := by rw [← hmD₀]
                        _ = (sD₀ ≫ (mD ≫ rDf)) ≫ sR := by simp [Category.assoc]
                        _ = (sD₀ ≫ (sD ≫ rS)) ≫ sR := by rw [hR₁.w]
                        _ = (sD₀ ≫ sD) ≫ rS ≫ sR := by simp [Category.assoc]
                        _ = (j₀ ≫ sP₀) ≫ rS ≫ sR := by rw [hsD₀]
                        _ = j₀ ≫ sP₀ ≫ rS ≫ sR := by simp [Category.assoc]
                  · calc
                      sPX ≫ sPf ≫ t = xP ≫ t := by
                        simpa [Category.assoc] using congrArg (fun z => z ≫ t) hsPfX
                      _ = D.x ≫ j_f ≫ t := by simp [xP]
                      _ = D.x ≫ sCf := by simp [t, hP_f]
                      _ = D.x ≫ (rDf ≫ sR) := rfl
                      _ = (sDX ≫ mD) ≫ (rDf ≫ sR) := by rw [← hmDX]
                      _ = (sDX ≫ (mD ≫ rDf)) ≫ sR := by simp [Category.assoc]
                      _ = (sDX ≫ (sD ≫ rS)) ≫ sR := by rw [hR₁.w]
                      _ = (sDX ≫ sD) ≫ rS ≫ sR := by simp [Category.assoc]
                      _ = sPX ≫ rS ≫ sR := by rw [hsDX]
        have hr1cof : cofibrations C rS :=
          (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout hR₁.flip hmD
        have hrpfcof : cofibrations C rPf :=
          (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout hpush_m.flip hm
        have hmP : cofibrations C sPf := by
          have hcomp := (IsCofibrationCategory.isMultiplicative (C := C)).comp_mem rS rPf
            hr1cof hrpfcof
          rw [hrPfS] at hcomp
          exact hcomp
        refine ⟨I, hI, S_P, sP₀, sPX, hS_P, sPf, ?_, ?_, hmP⟩
        · simp [sPf, hS_P]
        · simp [sPf, hS_P]
      x_cofibration := hxcof
      x_weakEquivalence := hxwe }
  let uP : B ⟶ P :=
    { v₀ := k₀
      vf := k_f
      a_vf := by simp [P, aP, hP₀]
      x_vf := hxcompat }
  let vP : D ⟶ P :=
    { v₀ := j₀
      vf := j_f
      a_vf := by simp [P, aP, hP₀]
      x_vf := rfl }
  have hv₀ : cofibrations C j₀ :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout hP₀.flip hf₀
  have hDa : cofibrations C D.a := sliceObj_a_cofibration D
  letI : HasPushout D.a j₀ :=
    IsCofibrationCategory.hasPushout (C := C) D.a j₀ hDa
  let Qᵥ := pushout D.a j₀
  let qDf : D.Af ⟶ Qᵥ := pushout.inl D.a j₀
  let qP₀ : P₀ ⟶ Qᵥ := pushout.inr D.a j₀
  let hQᵥ : IsPushout D.a j₀ qDf qP₀ := IsPushout.of_hasPushout D.a j₀
  let mᵥ : Qᵥ ⟶ P_f := hQᵥ.desc j_f aP (by simp [aP])
  have hmᵥDf : qDf ≫ mᵥ = j_f := by simp [mᵥ, hQᵥ]
  have hmᵥP₀ : qP₀ ≫ mᵥ = aP := by simp [mᵥ, hQᵥ]
  let qᵥ : Q ⟶ Qᵥ := hQ.desc (g.vf ≫ qDf) (k₀ ≫ qP₀) (by
    calc
      A.a ≫ (g.vf ≫ qDf) = (A.a ≫ g.vf) ≫ qDf := by simp [Category.assoc]
      _ = (g.v₀ ≫ D.a) ≫ qDf := by rw [g.a_vf]
      _ = g.v₀ ≫ (D.a ≫ qDf) := by simp [Category.assoc]
      _ = g.v₀ ≫ (j₀ ≫ qP₀) := by rw [hQᵥ.w]
      _ = (g.v₀ ≫ j₀) ≫ qP₀ := by simp [Category.assoc]
      _ = (f.v₀ ≫ k₀) ≫ qP₀ := by rw [hP₀.w]
      _ = f.v₀ ≫ (k₀ ≫ qP₀) := by simp [Category.assoc])
  have hqᵥAf : qAf ≫ qᵥ = g.vf ≫ qDf := by simp [qᵥ, hQ]
  have hqᵥB₀ : qB₀ ≫ qᵥ = k₀ ≫ qP₀ := by simp [qᵥ, hQ]
  have hsqᵥ : m ≫ k_f = qᵥ ≫ mᵥ := by
    apply hQ.hom_ext
    · calc
        qAf ≫ m ≫ k_f = (qAf ≫ m) ≫ k_f := by simp [Category.assoc]
        _ = f.vf ≫ k_f := by rw [hmAf]
        _ = g.vf ≫ j_f := by rw [hP_f.w.symm]
        _ = g.vf ≫ qDf ≫ mᵥ := by rw [← hmᵥDf]
        _ = (g.vf ≫ qDf) ≫ mᵥ := by simp [Category.assoc]
        _ = (qAf ≫ qᵥ) ≫ mᵥ := by rw [← hqᵥAf]
        _ = qAf ≫ qᵥ ≫ mᵥ := by simp [Category.assoc]
    · calc
        qB₀ ≫ m ≫ k_f = (qB₀ ≫ m) ≫ k_f := by simp [Category.assoc]
        _ = B.a ≫ k_f := by rw [hmB₀]
        _ = k₀ ≫ aP := by simp [aP]
        _ = k₀ ≫ qP₀ ≫ mᵥ := by rw [← hmᵥP₀]
        _ = (k₀ ≫ qP₀) ≫ mᵥ := by simp [Category.assoc]
        _ = (qB₀ ≫ qᵥ) ≫ mᵥ := by rw [← hqᵥB₀]
        _ = qB₀ ≫ qᵥ ≫ mᵥ := by simp [Category.assoc]
  have hpushᵥ : IsPushout m qᵥ k_f mᵥ := by
    refine IsPushout.mk' hsqᵥ ?_ ?_
    · intro T t t' hB hQᵥ
      apply hP_f.hom_ext
      · exact hB
      · calc
          j_f ≫ t = (qDf ≫ mᵥ) ≫ t := by rw [← hmᵥDf]
          _ = qDf ≫ (mᵥ ≫ t) := by simp [Category.assoc]
          _ = qDf ≫ (mᵥ ≫ t') := by rw [hQᵥ]
          _ = (qDf ≫ mᵥ) ≫ t' := by simp [Category.assoc]
          _ = j_f ≫ t' := by rw [hmᵥDf]
    intro T sB sQ hsq
    let sD : D.Af ⟶ T := qDf ≫ sQ
    have hsf : f.vf ≫ sB = g.vf ≫ sD := by
      calc
        f.vf ≫ sB = (qAf ≫ m) ≫ sB := by rw [← hmAf]
        _ = qAf ≫ (m ≫ sB) := by simp [Category.assoc]
        _ = qAf ≫ (qᵥ ≫ sQ) := by rw [hsq]
        _ = (qAf ≫ qᵥ) ≫ sQ := by simp [Category.assoc]
        _ = (g.vf ≫ qDf) ≫ sQ := by rw [hqᵥAf]
        _ = g.vf ≫ sD := by simp [sD, Category.assoc]
    let t : P_f ⟶ T := hP_f.desc sB sD hsf
    refine ⟨t, ?_, ?_⟩
    · simp [t, hP_f]
    · apply hQᵥ.hom_ext
      · calc
          qDf ≫ mᵥ ≫ t = (qDf ≫ mᵥ) ≫ t := by simp [Category.assoc]
          _ = j_f ≫ t := by rw [hmᵥDf]
          _ = sD := by simp [t, hP_f]
          _ = qDf ≫ sQ := rfl
      · apply hP₀.hom_ext
        · calc
            k₀ ≫ qP₀ ≫ mᵥ ≫ t = k₀ ≫ (qP₀ ≫ mᵥ) ≫ t := by simp [Category.assoc]
            _ = k₀ ≫ aP ≫ t := by rw [hmᵥP₀]
            _ = B.a ≫ k_f ≫ t := by simp [aP]
            _ = B.a ≫ sB := by simp [t, hP_f]
            _ = (qB₀ ≫ m) ≫ sB := by rw [← hmB₀]
            _ = qB₀ ≫ (m ≫ sB) := by simp [Category.assoc]
            _ = qB₀ ≫ (qᵥ ≫ sQ) := by rw [hsq]
            _ = (qB₀ ≫ qᵥ) ≫ sQ := by simp [Category.assoc]
            _ = (k₀ ≫ qP₀) ≫ sQ := by rw [hqᵥB₀]
            _ = k₀ ≫ qP₀ ≫ sQ := by simp [Category.assoc]
        · calc
            j₀ ≫ qP₀ ≫ mᵥ ≫ t = j₀ ≫ (qP₀ ≫ mᵥ) ≫ t := by simp [Category.assoc]
            _ = j₀ ≫ aP ≫ t := by rw [hmᵥP₀]
            _ = D.a ≫ j_f ≫ t := by simp [aP]
            _ = D.a ≫ sD := by simp [t, hP_f]
            _ = D.a ≫ qDf ≫ sQ := rfl
            _ = (D.a ≫ qDf) ≫ sQ := by simp [Category.assoc]
            _ = (j₀ ≫ qP₀) ≫ sQ := by rw [hQᵥ.w]
            _ = j₀ ≫ qP₀ ≫ sQ := by simp [Category.assoc]
  have hmᵥ : cofibrations C mᵥ :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout hpushᵥ.flip hm
  have hvGlue : IsCofibrantGluing D.a j₀ j_f aP := by
    exact ⟨Qᵥ, qDf, qP₀, hQᵥ, mᵥ, hmᵥDf, hmᵥP₀, hmᵥ⟩
  have hvP : cofibrations (SliceObj X) vP := ⟨hv₀, hvGlue⟩
  refine ⟨P, uP, vP, ?_⟩
  constructor
  let coc : PushoutCocone f g := PushoutCocone.mk uP vP (by
    apply SliceObj.Hom.ext
    · exact hP₀.w
    · exact hP_f.w)
  have hcoc : IsColimit coc := by
    apply PushoutCocone.isColimitAux' coc
    intro s
    let w₀ : P₀ ⟶ s.pt.A₀ := hP₀.desc s.inl.v₀ s.inr.v₀ (by
      have h := congrArg (fun z : A ⟶ s.pt => z.v₀) s.condition
      change f.v₀ ≫ s.inl.v₀ = g.v₀ ≫ s.inr.v₀ at h
      exact h)
    let wf : P_f ⟶ s.pt.Af := hP_f.desc s.inl.vf s.inr.vf (by
      have h := congrArg (fun z : A ⟶ s.pt => z.vf) s.condition
      change f.vf ≫ s.inl.vf = g.vf ≫ s.inr.vf at h
      exact h)
    have hwa : aP ≫ wf = w₀ ≫ s.pt.a := by
      apply hP₀.hom_ext
      · calc
          k₀ ≫ aP ≫ wf = B.a ≫ k_f ≫ wf := by simp [aP]
          _ = B.a ≫ s.inl.vf := by simp [wf, hP_f]
          _ = s.inl.v₀ ≫ s.pt.a := s.inl.a_vf
          _ = k₀ ≫ w₀ ≫ s.pt.a := by simp [w₀, hP₀]
      · calc
          j₀ ≫ aP ≫ wf = D.a ≫ j_f ≫ wf := by simp [aP]
          _ = D.a ≫ s.inr.vf := by simp [wf, hP_f]
          _ = s.inr.v₀ ≫ s.pt.a := s.inr.a_vf
          _ = j₀ ≫ w₀ ≫ s.pt.a := by simp [w₀, hP₀]
    have hwx : xP ≫ wf = s.pt.x := by
      calc
        xP ≫ wf = D.x ≫ j_f ≫ wf := by simp [xP]
        _ = D.x ≫ s.inr.vf := by simp [wf, hP_f]
        _ = s.pt.x := s.inr.x_vf
    let w : P ⟶ s.pt := ⟨w₀, wf, hwa, hwx⟩
    refine ⟨w, ?_, ?_, ?_⟩
    · apply SliceObj.Hom.ext
      · change k₀ ≫ w₀ = s.inl.v₀
        simp [w₀, hP₀]
      · change k_f ≫ wf = s.inl.vf
        simp [wf, hP_f]
    · apply SliceObj.Hom.ext
      · change j₀ ≫ w₀ = s.inr.v₀
        simp [w₀, hP₀]
      · change j_f ≫ wf = s.inr.vf
        simp [wf, hP_f]
    · intro w' hw'₁ hw'₂
      apply SliceObj.Hom.ext
      · apply hP₀.hom_ext
        · have h := congrArg (fun z : B ⟶ s.pt => z.v₀) hw'₁
          change k₀ ≫ w'.v₀ = s.inl.v₀ at h
          have hw : k₀ ≫ w.v₀ = s.inl.v₀ := by
            change k₀ ≫ w₀ = s.inl.v₀
            simp [w₀, hP₀]
          exact h.trans hw.symm
        · have h := congrArg (fun z : D ⟶ s.pt => z.v₀) hw'₂
          change j₀ ≫ w'.v₀ = s.inr.v₀ at h
          have hw : j₀ ≫ w.v₀ = s.inr.v₀ := by
            change j₀ ≫ w₀ = s.inr.v₀
            simp [w₀, hP₀]
          exact h.trans hw.symm
      · apply hP_f.hom_ext
        · have h := congrArg (fun z : B ⟶ s.pt => z.vf) hw'₁
          change k_f ≫ w'.vf = s.inl.vf at h
          have hw : k_f ≫ w.vf = s.inl.vf := by
            change k_f ≫ wf = s.inl.vf
            simp [wf, hP_f]
          exact h.trans hw.symm
        · have h := congrArg (fun z : D ⟶ s.pt => z.vf) hw'₂
          change j_f ≫ w'.vf = s.inr.vf at h
          have hw : j_f ≫ w.vf = s.inr.vf := by
            change j_f ≫ wf = s.inr.vf
            simp [wf, hP_f]
          exact h.trans hw.symm
  exact IsPushout.of_isColimit hcoc
  constructor
  · exact hP₀
  · constructor
    · exact hP_f
    · constructor
      · exact hvP
      · intro hW
        exact IsCylinderCategory.trivialCofibration_cobaseChange (C := C)
          f.v₀ g.v₀ k₀ j₀ hP₀ hf₀ hW

/-- Any two pushout squares in a homotopy slice are related by their canonical isomorphism. -/
theorem slice_pushout_uniqueIso {C : Type (u + 1)} [Category.{u} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [IsCylinderCategory C]
    {X : C} {A B D P P' : SliceObj X} {f : A ⟶ B} {g : A ⟶ D}
    {u : B ⟶ P} {v : D ⟶ P} {u' : B ⟶ P'} {v' : D ⟶ P'}
    (h : IsPushout f g u v) (h' : IsPushout f g u' v') :
    ∃ e : P' ≅ P, u' ≫ e.hom = u ∧ v' ≫ e.hom = v := by
  let eHom : P' ⟶ P := h'.desc u v h.w
  let eInv : P ⟶ P' := h.desc u' v' h'.w
  have huHom : u' ≫ eHom = u := by simp [eHom, h']
  have hvHom : v' ≫ eHom = v := by simp [eHom, h']
  have huInv : u ≫ eInv = u' := by simp [eInv, h]
  have hvInv : v ≫ eInv = v' := by simp [eInv, h]
  let e : P' ≅ P :=
    { hom := eHom
      inv := eInv
      hom_inv_id := by
        apply h'.hom_ext
        · calc
            u' ≫ (eHom ≫ eInv) = (u' ≫ eHom) ≫ eInv := by simp [Category.assoc]
            _ = u ≫ eInv := by rw [huHom]
            _ = u' := huInv
            _ = u' ≫ 𝟙 P' := by simp
        · calc
            v' ≫ (eHom ≫ eInv) = (v' ≫ eHom) ≫ eInv := by simp [Category.assoc]
            _ = v ≫ eInv := by rw [hvHom]
            _ = v' := hvInv
            _ = v' ≫ 𝟙 P' := by simp
      inv_hom_id := by
        apply h.hom_ext
        · calc
            u ≫ (eInv ≫ eHom) = (u ≫ eInv) ≫ eHom := by simp [Category.assoc]
            _ = u' ≫ eHom := by rw [huInv]
            _ = u := huHom
            _ = u ≫ 𝟙 P := by simp
        · calc
            v ≫ (eInv ≫ eHom) = (v ≫ eInv) ≫ eHom := by simp [Category.assoc]
            _ = v' ≫ eHom := by rw [hvInv]
            _ = v := hvHom
            _ = v ≫ 𝟙 P := by simp }
  exact ⟨e, huHom, hvHom⟩

/-- The forgetful functor sends pushouts along slice cofibrations to pushouts in the base. -/
theorem sliceForget_map_isPushout {C : Type (u + 1)} [Category.{u} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [IsCylinderCategory C]
    {X : C} {A B D P : SliceObj X} {f : A ⟶ B} {g : A ⟶ D}
    {u : B ⟶ P} {v : D ⟶ P} (h : IsPushout f g u v)
    (hf : cofibrations (SliceObj X) f) :
    IsPushout f.v₀ g.v₀ u.v₀ v.v₀ := by
  obtain ⟨P', u', v', h', h'₀, _, hv', _⟩ := slice_pushout_exists f g hf
  obtain ⟨e, hu, hv⟩ := slice_pushout_uniqueIso h h'
  let e₀ : P'.A₀ ≅ P.A₀ :=
    { hom := e.hom.v₀
      inv := e.inv.v₀
      hom_inv_id := congrArg (fun z : P' ⟶ P' => z.v₀) e.hom_inv_id
      inv_hom_id := congrArg (fun z : P ⟶ P => z.v₀) e.inv_hom_id }
  have hu₀ : u'.v₀ ≫ e₀.hom = u.v₀ := by
    have hcomp := congrArg (fun z : B ⟶ P => z.v₀) hu
    change u'.v₀ ≫ e₀.hom = u.v₀ at hcomp
    exact hcomp
  have hv₀ : v'.v₀ ≫ e₀.hom = v.v₀ := by
    have hcomp := congrArg (fun z : D ⟶ P => z.v₀) hv
    change v'.v₀ ≫ e₀.hom = v.v₀ at hcomp
    exact hcomp
  exact h'₀.of_iso (Iso.refl A.A₀) (Iso.refl B.A₀) (Iso.refl D.A₀) e₀
    (by simp) (by simp) (by simpa using hu₀) (by simpa using hv₀)

/-- Trivial cofibrations in a homotopy slice remain weak equivalences after cobase change. -/
theorem sliceTrivialCofibration_cobaseChange {C : Type (u + 1)} [Category.{u} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [IsCylinderCategory C]
    {X : C} {A B D P : SliceObj X} (f : A ⟶ B) (g : A ⟶ D) (u : B ⟶ P) (v : D ⟶ P)
    (h : IsPushout f g u v) (hf : cofibrations (SliceObj X) f)
    (hW : weakEquivalences (SliceObj X) f) : weakEquivalences (SliceObj X) v := by
  change weakEquivalences C f.v₀ at hW
  change cofibrations C f.v₀ ∧ IsCofibrantGluing A.a f.v₀ f.vf B.a at hf
  obtain ⟨P', u', v', h', h'₀, _, _, hWv'⟩ :=
    slice_pushout_exists f g hf
  have hWv'₀ : weakEquivalences C v'.v₀ := hWv' hW
  obtain ⟨e, _, hv⟩ := slice_pushout_uniqueIso h h'
  let e₀ : P'.A₀ ≅ P.A₀ :=
    { hom := e.hom.v₀
      inv := e.inv.v₀
      hom_inv_id := congrArg (fun z : P' ⟶ P' => z.v₀) e.hom_inv_id
      inv_hom_id := congrArg (fun z : P ⟶ P => z.v₀) e.inv_hom_id }
  haveI : IsIso e.hom.v₀ := e₀.isIso_hom
  have hWiso : weakEquivalences C e.hom.v₀ :=
    IsCylinderCategory.isomorphisms_le_weakEquivalences (C := C) e.hom.v₀
      (MorphismProperty.isomorphisms.infer_property e.hom.v₀)
  have hcomp : weakEquivalences C (v'.v₀ ≫ e.hom.v₀) :=
    (IsCylinderCategory.weakEquivalences_isMultiplicative (C := C)).comp_mem
      v'.v₀ e.hom.v₀ hWv'₀ hWiso
  have hv₀ : v'.v₀ ≫ e.hom.v₀ = v.v₀ := by
    have hvcomp := congrArg (fun z : D ⟶ P => z.v₀) hv
    change v'.v₀ ≫ e.hom.v₀ = v.v₀ at hvcomp
    exact hvcomp
  rw [hv₀] at hcomp
  exact hcomp

/-- Cofibrations in a homotopy slice are stable under arbitrary cobase change squares. -/
theorem sliceCofibration_cobaseChange {C : Type (u + 1)} [Category.{u} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [IsCylinderCategory C]
    {X : C} {A B D P : SliceObj X} (f : A ⟶ B) (g : A ⟶ D) (u : B ⟶ P) (v : D ⟶ P)
    (h : IsPushout f g u v) (hf : cofibrations (SliceObj X) f) :
    cofibrations (SliceObj X) v := by
  classical
  obtain ⟨P', u', v', h', h'₀, _, hv', _⟩ := slice_pushout_exists f g hf
  let eHom : P' ⟶ P := h'.desc u v h.w
  let eInv : P ⟶ P' := h.desc u' v' h'.w
  have huHom : u' ≫ eHom = u := by simp [eHom, h']
  have hvHom : v' ≫ eHom = v := by simp [eHom, h']
  have huInv : u ≫ eInv = u' := by simp [eInv, h]
  have hvInv : v ≫ eInv = v' := by simp [eInv, h]
  let e : P' ≅ P :=
    { hom := eHom
      inv := eInv
      hom_inv_id := by
        apply h'.hom_ext
        · calc
            u' ≫ (eHom ≫ eInv) = (u' ≫ eHom) ≫ eInv := by simp [Category.assoc]
            _ = u ≫ eInv := by rw [huHom]
            _ = u' := huInv
            _ = u' ≫ 𝟙 P' := by simp
        · calc
            v' ≫ (eHom ≫ eInv) = (v' ≫ eHom) ≫ eInv := by simp [Category.assoc]
            _ = v ≫ eInv := by rw [hvHom]
            _ = v' := hvInv
            _ = v' ≫ 𝟙 P' := by simp
      inv_hom_id := by
        apply h.hom_ext
        · calc
            u ≫ (eInv ≫ eHom) = (u ≫ eInv) ≫ eHom := by simp [Category.assoc]
            _ = u' ≫ eHom := by rw [huInv]
            _ = u := huHom
            _ = u ≫ 𝟙 P := by simp
        · calc
            v ≫ (eInv ≫ eHom) = (v ≫ eInv) ≫ eHom := by simp [Category.assoc]
            _ = v' ≫ eHom := by rw [hvInv]
            _ = v := hvHom
            _ = v ≫ 𝟙 P := by simp }
  haveI : IsIso e.hom := e.isIso_hom
  have hecof : cofibrations (SliceObj X) e.hom :=
    sliceCofibration_isomorphisms X e.hom (MorphismProperty.isomorphisms.infer_property e.hom)
  have hcomp : cofibrations (SliceObj X) (v' ≫ e.hom) :=
    sliceCofibration_comp v' e.hom hv' hecof
  rw [hvHom] at hcomp
  exact hcomp

end

end HomotopyHypothesis.Cylinder.SliceCategory

#print axioms HomotopyHypothesis.Cylinder.SliceCategory.slice_pushout_exists
#print axioms HomotopyHypothesis.Cylinder.SliceCategory.slice_pushout_uniqueIso
#print axioms HomotopyHypothesis.Cylinder.SliceCategory.sliceForget_map_isPushout
#print axioms HomotopyHypothesis.Cylinder.SliceCategory.sliceCofibration_cobaseChange
