import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Cylinder.SliceCategory.Proofs
open CategoryTheory Limits HomotopicalAlgebra HomotopyHypothesis.Henry

universe u

namespace HomotopyHypothesis.Cylinder.SliceCategory

noncomputable section

/-- Enlarging the first leg of a cofibrant pair along a cofibration preserves the pair condition. -/
theorem cofibrantPair_pushoutFirst {C : Type (u + 1)} [Category.{u} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [IsCylinderCategory C]
    {A Af X P L : C} {a : A ⟶ Af} {x : X ⟶ Af} (hpair : IsCofibrantPair a x)
    (i : A ⟶ P) (hi : cofibrations C i) {kP : P ⟶ L} {kA : Af ⟶ L}
    (hL : IsPushout i a kP kA) : IsCofibrantPair kP (x ≫ kA) := by
  classical
  obtain ⟨I, hI, T, tA, tX, hT, mA, htA, htX, hmA⟩ := hpair
  have hIP : cofibrations C (hI.to P) :=
    IsCofibrationCategory.initial_cofibration hI P
  letI : HasPushout (hI.to P) (hI.to X) :=
    IsCofibrationCategory.hasPushout (C := C) (hI.to P) (hI.to X) hIP
  let S := pushout (hI.to P) (hI.to X)
  let sP : P ⟶ S := pushout.inl (hI.to P) (hI.to X)
  let sX : X ⟶ S := pushout.inr (hI.to P) (hI.to X)
  let hS : IsPushout (hI.to P) (hI.to X) sP sX :=
    IsPushout.of_hasPushout (hI.to P) (hI.to X)
  let tS : T ⟶ S := hT.desc (i ≫ sP) sX (by
    apply hI.hom_ext)
  have htS_A : tA ≫ tS = i ≫ sP := by simp [tS, hT]
  have htS_X : tX ≫ tS = sX := by simp [tS, hT]
  letI : HasPushout mA tS :=
    IsCofibrationCategory.hasPushout (C := C) mA tS hmA
  let R := pushout mA tS
  let rAf : Af ⟶ R := pushout.inl mA tS
  let rS : S ⟶ R := pushout.inr mA tS
  let hR : IsPushout mA tS rAf rS := IsPushout.of_hasPushout mA tS
  let sL : S ⟶ L := hS.desc kP (x ≫ kA) (by
    exact hI.hom_ext _ _)
  have hsL_P : sP ≫ sL = kP := by simp [sL, hS]
  have hsL_X : sX ≫ sL = x ≫ kA := by simp [sL, hS]
  have hRcompat : mA ≫ kA = tS ≫ sL := by
    apply hT.hom_ext
    · calc
        tA ≫ (mA ≫ kA) = (tA ≫ mA) ≫ kA := by rw [Category.assoc]
        _ = a ≫ kA := by rw [htA]
        _ = i ≫ kP := by rw [hL.w]
        _ = i ≫ (sP ≫ sL) := by rw [hsL_P]
        _ = (i ≫ sP) ≫ sL := by rw [Category.assoc]
        _ = (tA ≫ tS) ≫ sL := by rw [htS_A]
        _ = tA ≫ (tS ≫ sL) := by rw [Category.assoc]
    · calc
        tX ≫ (mA ≫ kA) = (tX ≫ mA) ≫ kA := by rw [Category.assoc]
        _ = x ≫ kA := by rw [htX]
        _ = sX ≫ sL := by rw [hsL_X]
        _ = (tX ≫ tS) ≫ sL := by rw [htS_X]
        _ = tX ≫ (tS ≫ sL) := by rw [Category.assoc]
  let φ : R ⟶ L := hR.desc kA sL hRcompat
  have hφ_Af : rAf ≫ φ = kA := by simp [φ, hR]
  have hφ_S : rS ≫ φ = sL := by simp [φ, hR]
  have hSboundary : i ≫ sP ≫ rS = a ≫ rAf := by
    calc
      i ≫ (sP ≫ rS) = (i ≫ sP) ≫ rS := by rw [Category.assoc]
      _ = (tA ≫ tS) ≫ rS := by rw [htS_A]
      _ = tA ≫ (tS ≫ rS) := by rw [Category.assoc]
      _ = tA ≫ (mA ≫ rAf) := by rw [hR.w]
      _ = (tA ≫ mA) ≫ rAf := by rw [Category.assoc]
      _ = a ≫ rAf := by rw [htA]
  let ψ : L ⟶ R := hL.desc (sP ≫ rS) rAf hSboundary
  have hψ_P : kP ≫ ψ = sP ≫ rS := by simp [ψ, hL]
  have hψ_Af : kA ≫ ψ = rAf := by simp [ψ, hL]
  have hsXrS : sX ≫ rS = x ≫ rAf := by
    calc
      sX ≫ rS = (tX ≫ tS) ≫ rS := by rw [htS_X]
      _ = tX ≫ (tS ≫ rS) := by rw [Category.assoc]
      _ = tX ≫ (mA ≫ rAf) := by rw [hR.w]
      _ = (tX ≫ mA) ≫ rAf := by rw [Category.assoc]
      _ = x ≫ rAf := by rw [htX]
  have hφψ : φ ≫ ψ = 𝟙 R := by
    apply hR.hom_ext
    · calc
        rAf ≫ (φ ≫ ψ) = (rAf ≫ φ) ≫ ψ := by rw [Category.assoc]
        _ = kA ≫ ψ := by rw [hφ_Af]
        _ = rAf := hψ_Af
        _ = rAf ≫ 𝟙 R := by simp
    · apply hS.hom_ext
      · have hstep : rS ≫ (φ ≫ ψ) = sL ≫ ψ := by
          calc
            rS ≫ (φ ≫ ψ) = (rS ≫ φ) ≫ ψ := by rw [Category.assoc]
            _ = sL ≫ ψ := by rw [hφ_S]
        calc
          sP ≫ (rS ≫ (φ ≫ ψ)) = sP ≫ (sL ≫ ψ) := by rw [hstep]
          _ = (sP ≫ sL) ≫ ψ := by rw [Category.assoc]
          _ = kP ≫ ψ := by rw [hsL_P]
          _ = sP ≫ rS := hψ_P
          _ = sP ≫ rS ≫ 𝟙 R := by simp
      · have hstep : rS ≫ (φ ≫ ψ) = sL ≫ ψ := by
          calc
            rS ≫ (φ ≫ ψ) = (rS ≫ φ) ≫ ψ := by rw [Category.assoc]
            _ = sL ≫ ψ := by rw [hφ_S]
        calc
          sX ≫ (rS ≫ (φ ≫ ψ)) = sX ≫ (sL ≫ ψ) := by rw [hstep]
          _ = (sX ≫ sL) ≫ ψ := by rw [Category.assoc]
          _ = (x ≫ kA) ≫ ψ := by rw [hsL_X]
          _ = x ≫ (kA ≫ ψ) := by rw [Category.assoc]
          _ = x ≫ rAf := by rw [hψ_Af]
          _ = sX ≫ rS := hsXrS.symm
          _ = sX ≫ rS ≫ 𝟙 R := by simp
  have hψφ : ψ ≫ φ = 𝟙 L := by
    apply hL.hom_ext
    · calc
        kP ≫ (ψ ≫ φ) = (kP ≫ ψ) ≫ φ := by rw [Category.assoc]
        _ = (sP ≫ rS) ≫ φ := by rw [hψ_P]
        _ = sP ≫ (rS ≫ φ) := by rw [Category.assoc]
        _ = sP ≫ sL := by rw [hφ_S]
        _ = kP := hsL_P
        _ = kP ≫ 𝟙 L := by simp
    · calc
        kA ≫ (ψ ≫ φ) = (kA ≫ ψ) ≫ φ := by rw [Category.assoc]
        _ = rAf ≫ φ := by rw [hψ_Af]
        _ = kA := hφ_Af
        _ = kA ≫ 𝟙 L := by simp
  let e : R ≅ L := ⟨φ, ψ, hφψ, hψφ⟩
  haveI : IsIso φ := ⟨ψ, hφψ, hψφ⟩
  have hrS : cofibrations C rS :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout hR.flip hmA
  have hφcof : cofibrations C φ :=
    IsCofibrationCategory.isomorphisms_le φ (MorphismProperty.isomorphisms.infer_property φ)
  have hsLcof : cofibrations C sL := by
    have hcomp :=
      (IsCofibrationCategory.isMultiplicative (C := C)).comp_mem rS φ hrS hφcof
    rw [hφ_S] at hcomp
    exact hcomp
  exact ⟨I, hI, S, sP, sX, hS, sL, hsL_P, hsL_X, hsLcof⟩

#print axioms HomotopyHypothesis.Cylinder.SliceCategory.cofibrantPair_pushoutFirst

end

end HomotopyHypothesis.Cylinder.SliceCategory
