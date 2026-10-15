import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Cylinder.SliceCategory.Proofs
open CategoryTheory Limits HomotopicalAlgebra HomotopyHypothesis.Henry

universe u

namespace HomotopyHypothesis.Cylinder.SliceCategory

/-- The forgetful functor from a homotopy slice lifts retractions of trivial cofibrations. -/
theorem sliceForget_lift_retraction {C : Type (u + 1)} [Category.{u} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [IsCylinderCategory C]
    (X : C) :
    ∀ {A B : SliceObj X} (s : A ⟶ B), cofibrations (SliceObj X) s →
      weakEquivalences (SliceObj X) s → ∀ (r₀ : B.A₀ ⟶ A.A₀),
        s.v₀ ≫ r₀ = 𝟙 A.A₀ → ∃ r : B ⟶ A,
          s ≫ r = 𝟙 A ∧ (SliceObj.forget X).map r = r₀ := by
  intro A B s hs hsw r₀ hr₀
  change cofibrations C s.v₀ ∧ IsCofibrantGluing A.a s.v₀ s.vf B.a at hs
  rcases hs with ⟨hs₀, hglue⟩
  change weakEquivalences C s.v₀ at hsw
  obtain ⟨P, k, j, hpo, m, hkm, hjm, hm⟩ := hglue
  have hkWE : weakEquivalences C k :=
    IsCylinderCategory.trivialCofibration_cobaseChange (C := C)
      s.v₀ A.a j k hpo.flip hs₀ hsw
  have hAxk : weakEquivalences C (A.x ≫ k) :=
    (IsCylinderCategory.weakEquivalences_isMultiplicative (C := C)).comp_mem
      A.x k A.x_weakEquivalence hkWE
  have hBm_eq : (A.x ≫ k) ≫ m = B.x := by
    calc
      (A.x ≫ k) ≫ m = A.x ≫ (k ≫ m) := by simp [Category.assoc]
      _ = A.x ≫ s.vf := by rw [hkm]
      _ = B.x := s.x_vf
  have hBm : weakEquivalences C ((A.x ≫ k) ≫ m) := by
    rw [hBm_eq]
    exact B.x_weakEquivalence
  have hId : weakEquivalences C ((𝟙 X) ≫ (A.x ≫ k)) := by simpa using hAxk
  have hmWE : weakEquivalences C m :=
    (IsCylinderCategory.twoOutOfSix (C := C) (𝟙 X) (A.x ≫ k) m hId hBm).2.2.1
  obtain ⟨rP, hrP⟩ := IsCylinderCategory.exists_retraction (C := C) m hm hmWE
  have hucompat : A.a ≫ 𝟙 A.Af = s.v₀ ≫ (r₀ ≫ A.a) := by
    calc
      A.a ≫ 𝟙 A.Af = A.a := by simp
      _ = (s.v₀ ≫ r₀) ≫ A.a := by rw [hr₀]; simp
      _ = s.v₀ ≫ (r₀ ≫ A.a) := by simp [Category.assoc]
  let u : P ⟶ A.Af := hpo.desc (𝟙 A.Af) (r₀ ≫ A.a) hucompat
  have huAf : k ≫ u = 𝟙 A.Af := by simp [u, hpo]
  have huB₀ : j ≫ u = r₀ ≫ A.a := by simp [u, hpo]
  have hrf : s.vf ≫ (rP ≫ u) = 𝟙 A.Af := by
    calc
      s.vf ≫ (rP ≫ u) = (k ≫ m) ≫ (rP ≫ u) := by rw [← hkm]
      _ = k ≫ ((m ≫ rP) ≫ u) := by simp [Category.assoc]
      _ = k ≫ (𝟙 P ≫ u) := by rw [hrP]
      _ = k ≫ u := by simp
      _ = 𝟙 A.Af := huAf
  have hra : B.a ≫ (rP ≫ u) = r₀ ≫ A.a := by
    calc
      B.a ≫ (rP ≫ u) = (j ≫ m) ≫ (rP ≫ u) := by rw [← hjm]
      _ = j ≫ ((m ≫ rP) ≫ u) := by simp [Category.assoc]
      _ = j ≫ (𝟙 P ≫ u) := by rw [hrP]
      _ = j ≫ u := by simp
      _ = r₀ ≫ A.a := huB₀
  have hrx : B.x ≫ (rP ≫ u) = A.x := by
    calc
      B.x ≫ (rP ≫ u) = (A.x ≫ s.vf) ≫ (rP ≫ u) := by rw [s.x_vf]
      _ = A.x ≫ (s.vf ≫ (rP ≫ u)) := by simp [Category.assoc]
      _ = A.x ≫ 𝟙 A.Af := by rw [hrf]
      _ = A.x := by simp
  let r : B ⟶ A :=
    { v₀ := r₀
      vf := rP ≫ u
      a_vf := hra
      x_vf := hrx }
  have hsr : s ≫ r = 𝟙 A := by
    apply SliceObj.Hom.ext
    · exact hr₀
    · exact hrf
  exact ⟨r, hsr, rfl⟩

#print axioms HomotopyHypothesis.Cylinder.SliceCategory.sliceForget_lift_retraction

end HomotopyHypothesis.Cylinder.SliceCategory
