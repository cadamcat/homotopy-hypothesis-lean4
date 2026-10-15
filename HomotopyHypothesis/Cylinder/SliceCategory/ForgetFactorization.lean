import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Cylinder.SliceCategory.Proofs
import HomotopyHypothesis.Category.SemiModelStructure.CylinderFacts
open CategoryTheory Limits HomotopicalAlgebra HomotopyHypothesis.Henry

universe u

namespace HomotopyHypothesis.Cylinder.SliceCategory

/-- The forgetful functor from a homotopy slice lifts cofibration/weak-equivalence factorizations. -/
theorem sliceForget_lift_factorization {C : Type (u + 1)} [Category.{u} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [IsCylinderCategory C]
    (X : C) {A B : SliceObj X} (f : A ⟶ B) {Q : C}
    (i : A.A₀ ⟶ Q) (w : Q ⟶ B.A₀) (hi : cofibrations C i)
    (hw : weakEquivalences C w) (hfactor : i ≫ w = f.v₀) :
    ∃ (P : SliceObj X) (i' : A ⟶ P) (w' : P ⟶ B) (e : P.A₀ = Q),
      cofibrations (SliceObj X) i' ∧ weakEquivalences (SliceObj X) w' ∧
        i' ≫ w' = f ∧ (SliceObj.forget X).map i' = i ≫ eqToHom e.symm ∧
          (SliceObj.forget X).map w' = eqToHom e ≫ w := by
  classical
  obtain ⟨I, hI_nonempty⟩ := IsCofibrationCategory.exists_initial (C := C)
  let hI : IsInitial I := Classical.choice hI_nonempty
  obtain ⟨I_A, hI_A, P_A, k_A, j_A, hPA, m_A, hk_A, hj_A, hm_A⟩ := A.cofibrant
  have hI_Q : cofibrations C (hI.to Q) := IsCofibrationCategory.initial_cofibration hI Q
  letI : HasPushout (hI.to Q) (hI.to X) :=
    IsCofibrationCategory.hasPushout (C := C) (hI.to Q) (hI.to X) hI_Q
  let QX := pushout (hI.to Q) (hI.to X)
  let q₀ : Q ⟶ QX := pushout.inl (hI.to Q) (hI.to X)
  let qX : X ⟶ QX := pushout.inr (hI.to Q) (hI.to X)
  let hQX : IsPushout (hI.to Q) (hI.to X) q₀ qX :=
    IsPushout.of_hasPushout (hI.to Q) (hI.to X)
  have hrcompat : (hI_A.to A.A₀) ≫ (i ≫ q₀) = (hI_A.to X) ≫ qX := by
    exact hI_A.hom_ext _ _
  let r : P_A ⟶ QX := hPA.desc (i ≫ q₀) qX hrcompat
  have hr₀ : k_A ≫ r = i ≫ q₀ := by simp [r, hPA]
  have hrX : j_A ≫ r = qX := by simp [r, hPA]
  have hDhas : HasPushout m_A r :=
    IsCofibrationCategory.hasPushout (C := C) m_A r hm_A
  letI := hDhas
  let D := pushout m_A r
  let d_A : A.Af ⟶ D := pushout.inl m_A r
  let d_QX : QX ⟶ D := pushout.inr m_A r
  let hD : IsPushout m_A r d_A d_QX := IsPushout.of_hasPushout m_A r
  have hQXbase : (hI.to Q) ≫ (w ≫ B.a) = (hI.to X) ≫ B.x := by
    exact hI.hom_ext _ _
  let g_QX : QX ⟶ B.Af := hQX.desc (w ≫ B.a) B.x hQXbase
  have hgQ : q₀ ≫ g_QX = w ≫ B.a := by simp [g_QX, hQX]
  have hgX : qX ≫ g_QX = B.x := by simp [g_QX, hQX]
  have hDcompat : m_A ≫ f.vf = r ≫ g_QX := by
    apply hPA.hom_ext
    · calc
        k_A ≫ (m_A ≫ f.vf) = A.a ≫ f.vf := by
          simpa [Category.assoc] using congrArg (fun z => z ≫ f.vf) hk_A
        _ = f.v₀ ≫ B.a := f.a_vf
        _ = i ≫ (w ≫ B.a) := by
          simpa [Category.assoc] using congrArg (fun z => z ≫ B.a) hfactor.symm
        _ = i ≫ (q₀ ≫ g_QX) := by rw [hgQ]
        _ = (i ≫ q₀) ≫ g_QX := by simp [Category.assoc]
        _ = (k_A ≫ r) ≫ g_QX := by rw [← hr₀]
        _ = k_A ≫ (r ≫ g_QX) := by exact Category.assoc _ _ _
    · calc
        j_A ≫ (m_A ≫ f.vf) = A.x ≫ f.vf := by
          simpa [Category.assoc] using congrArg (fun z => z ≫ f.vf) hj_A
        _ = B.x := f.x_vf
        _ = qX ≫ g_QX := hgX.symm
        _ = (j_A ≫ r) ≫ g_QX := by rw [← hrX]
        _ = j_A ≫ (r ≫ g_QX) := by exact Category.assoc _ _ _
  let g : D ⟶ B.Af := hD.desc f.vf g_QX hDcompat
  obtain ⟨P_f, c, w_f, hc, hw_f, hcw⟩ :=
    HomotopyHypothesis.Category.SemiModelStructure.brown_factorization g
  have hqX_cof : cofibrations C qX :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout hQX.flip hI_Q
  have hdQX_cof : cofibrations C d_QX :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout hD.flip hm_A
  have hDqXc_cof : cofibrations C (d_QX ≫ c) :=
    (IsCofibrationCategory.isMultiplicative (C := C)).comp_mem d_QX c hdQX_cof hc
  have hx_cof : cofibrations C (qX ≫ d_QX ≫ c) :=
    (IsCofibrationCategory.isMultiplicative (C := C)).comp_mem qX (d_QX ≫ c)
      hqX_cof hDqXc_cof
  have hx_we : weakEquivalences C (qX ≫ d_QX ≫ c) := by
    have hcomp_eq : ((qX ≫ d_QX ≫ c) ≫ w_f) = B.x := by
      calc
        (qX ≫ d_QX ≫ c) ≫ w_f = qX ≫ (d_QX ≫ (c ≫ w_f)) := by simp [Category.assoc]
        _ = qX ≫ (d_QX ≫ g) := by rw [hcw]
        _ = qX ≫ g_QX := by simp [g, hD]
        _ = B.x := by rw [hgX]
    have hcomp : weakEquivalences C ((qX ≫ d_QX ≫ c) ≫ w_f) := by
      rw [hcomp_eq]
      exact B.x_weakEquivalence
    have hcomp' : weakEquivalences C (w_f ≫ 𝟙 B.Af) := by simpa using hw_f
    exact (IsCylinderCategory.twoOutOfSix (C := C) (qX ≫ d_QX ≫ c) w_f
      (𝟙 B.Af) hcomp hcomp').1
  let P : SliceObj X :=
    { A₀ := Q
      Af := P_f
      a := q₀ ≫ d_QX ≫ c
      x := qX ≫ d_QX ≫ c
      cofibrant := by
        refine ⟨I, hI, QX, q₀, qX, hQX, d_QX ≫ c, ?_, ?_, hDqXc_cof⟩
        · simp [Category.assoc]
        · simp [Category.assoc]
      x_cofibration := hx_cof
      x_weakEquivalence := hx_we }
  let i' : A ⟶ P :=
    { v₀ := i
      vf := d_A ≫ c
      a_vf := by
        dsimp [P]
        calc
          A.a ≫ (d_A ≫ c) = k_A ≫ (m_A ≫ (d_A ≫ c)) := by
            simpa [Category.assoc] using congrArg (fun z => z ≫ (d_A ≫ c)) hk_A.symm
          _ = k_A ≫ ((m_A ≫ d_A) ≫ c) := by simp [Category.assoc]
          _ = k_A ≫ ((r ≫ d_QX) ≫ c) := by rw [hD.w]
          _ = (k_A ≫ r) ≫ d_QX ≫ c := by simp [Category.assoc]
          _ = (i ≫ q₀) ≫ d_QX ≫ c := by rw [hr₀]
          _ = i ≫ (q₀ ≫ d_QX ≫ c) := by simp [Category.assoc]
      x_vf := by
        dsimp [P]
        calc
          A.x ≫ (d_A ≫ c) = j_A ≫ (m_A ≫ (d_A ≫ c)) := by
            simpa [Category.assoc] using congrArg (fun z => z ≫ (d_A ≫ c)) hj_A.symm
          _ = j_A ≫ ((m_A ≫ d_A) ≫ c) := by simp [Category.assoc]
          _ = j_A ≫ ((r ≫ d_QX) ≫ c) := by rw [hD.w]
          _ = (j_A ≫ r) ≫ d_QX ≫ c := by simp [Category.assoc]
          _ = qX ≫ d_QX ≫ c := by rw [hrX] }
  let w' : P ⟶ B :=
    { v₀ := w
      vf := w_f
      a_vf := by
        dsimp [P]
        calc
          (q₀ ≫ d_QX ≫ c) ≫ w_f = q₀ ≫ d_QX ≫ (c ≫ w_f) := by simp [Category.assoc]
          _ = q₀ ≫ d_QX ≫ g := by rw [hcw]
          _ = q₀ ≫ g_QX := by simp [g, hD]
          _ = w ≫ B.a := by rw [hgQ]
      x_vf := by
        dsimp [P]
        calc
          (qX ≫ d_QX ≫ c) ≫ w_f = qX ≫ d_QX ≫ (c ≫ w_f) := by simp [Category.assoc]
          _ = qX ≫ d_QX ≫ g := by rw [hcw]
          _ = qX ≫ g_QX := by simp [g, hD]
          _ = B.x := by rw [hgX] }
  have hRhas : HasPushout i A.a :=
    IsCofibrationCategory.hasPushout (C := C) i A.a hi
  letI := hRhas
  let R := pushout i A.a
  let r_Q : Q ⟶ R := pushout.inl i A.a
  let r_Af : A.Af ⟶ R := pushout.inr i A.a
  let hR : IsPushout i A.a r_Q r_Af := IsPushout.of_hasPushout i A.a
  have htcompat : i ≫ (q₀ ≫ d_QX) = A.a ≫ d_A := by
    calc
      i ≫ (q₀ ≫ d_QX) = (k_A ≫ r) ≫ d_QX := by
        simpa [Category.assoc] using congrArg (fun z => z ≫ d_QX) hr₀.symm
      _ = k_A ≫ (r ≫ d_QX) := by simp [Category.assoc]
      _ = k_A ≫ (m_A ≫ d_A) := by rw [hD.w]
      _ = (k_A ≫ m_A) ≫ d_A := by simp [Category.assoc]
      _ = A.a ≫ d_A := by rw [hk_A]
  let t : R ⟶ D := hR.desc (q₀ ≫ d_QX) d_A htcompat
  have htQ : r_Q ≫ t = q₀ ≫ d_QX := by simp [t, hR]
  have htAf : r_Af ≫ t = d_A := by simp [t, hR]
  have hQXRbase : (hI.to Q) ≫ r_Q = (hI.to X) ≫ (A.x ≫ r_Af) := by
    exact hI.hom_ext _ _
  let q_R : QX ⟶ R := hQX.desc r_Q (A.x ≫ r_Af) hQXRbase
  have hqR₀ : q₀ ≫ q_R = r_Q := by simp [q_R, hQX]
  have hqRX : qX ≫ q_R = A.x ≫ r_Af := by simp [q_R, hQX]
  have hDinvCompat : m_A ≫ r_Af = r ≫ q_R := by
    apply hPA.hom_ext
    · calc
        k_A ≫ (m_A ≫ r_Af) = (k_A ≫ m_A) ≫ r_Af := by simp [Category.assoc]
        _ = A.a ≫ r_Af := by rw [hk_A]
        _ = i ≫ r_Q := hR.w.symm
        _ = i ≫ (q₀ ≫ q_R) := by rw [← hqR₀]
        _ = (i ≫ q₀) ≫ q_R := by simp [Category.assoc]
        _ = (k_A ≫ r) ≫ q_R := by rw [← hr₀]
        _ = k_A ≫ (r ≫ q_R) := by simp [Category.assoc]
    · calc
        j_A ≫ (m_A ≫ r_Af) = (j_A ≫ m_A) ≫ r_Af := by simp [Category.assoc]
        _ = A.x ≫ r_Af := by rw [hj_A]
        _ = qX ≫ q_R := hqRX.symm
        _ = (j_A ≫ r) ≫ q_R := by rw [hrX]
        _ = j_A ≫ (r ≫ q_R) := by simp [Category.assoc]
  let d : D ⟶ R := hD.desc r_Af q_R hDinvCompat
  have hdAf : d_A ≫ d = r_Af := by simp [d, hD]
  have hdQX : d_QX ≫ d = q_R := by simp [d, hD]
  have htd : t ≫ d = 𝟙 R := by
    apply hR.hom_ext
    · calc
        r_Q ≫ (t ≫ d) = (r_Q ≫ t) ≫ d := by simp [Category.assoc]
        _ = (q₀ ≫ d_QX) ≫ d := by rw [htQ]
        _ = q₀ ≫ (d_QX ≫ d) := by simp [Category.assoc]
        _ = q₀ ≫ q_R := by rw [hdQX]
        _ = r_Q := hqR₀
        _ = r_Q ≫ 𝟙 R := by simp
    · calc
        r_Af ≫ (t ≫ d) = (r_Af ≫ t) ≫ d := by simp [Category.assoc]
        _ = d_A ≫ d := by rw [htAf]
        _ = r_Af := hdAf
        _ = r_Af ≫ 𝟙 R := by simp
  have hqRt : q_R ≫ t = d_QX := by
    apply hQX.hom_ext
    · calc
        q₀ ≫ (q_R ≫ t) = (q₀ ≫ q_R) ≫ t := by simp [Category.assoc]
        _ = r_Q ≫ t := by rw [hqR₀]
        _ = q₀ ≫ d_QX := htQ
    · calc
        qX ≫ (q_R ≫ t) = (qX ≫ q_R) ≫ t := by simp [Category.assoc]
        _ = (A.x ≫ r_Af) ≫ t := by rw [hqRX]
        _ = A.x ≫ (r_Af ≫ t) := by simp [Category.assoc]
        _ = A.x ≫ d_A := by rw [htAf]
        _ = (j_A ≫ m_A) ≫ d_A := by rw [← hj_A]
        _ = j_A ≫ (m_A ≫ d_A) := by simp [Category.assoc]
        _ = j_A ≫ (r ≫ d_QX) := by rw [hD.w]
        _ = (j_A ≫ r) ≫ d_QX := by simp [Category.assoc]
        _ = qX ≫ d_QX := by rw [hrX]
  have hdt : d ≫ t = 𝟙 D := by
    apply hD.hom_ext
    · calc
        d_A ≫ (d ≫ t) = (d_A ≫ d) ≫ t := by simp [Category.assoc]
        _ = r_Af ≫ t := by rw [hdAf]
        _ = d_A := htAf
        _ = d_A ≫ 𝟙 D := by simp
    · calc
        d_QX ≫ (d ≫ t) = (d_QX ≫ d) ≫ t := by simp [Category.assoc]
        _ = q_R ≫ t := by rw [hdQX]
        _ = d_QX := hqRt
        _ = d_QX ≫ 𝟙 D := by simp
  letI : IsIso t := ⟨d, htd, hdt⟩
  have ht_cof : cofibrations C t :=
    IsCofibrationCategory.isomorphisms_le t (MorphismProperty.isomorphisms.infer_property t)
  have htc_cof : cofibrations C (t ≫ c) :=
    (IsCofibrationCategory.isMultiplicative (C := C)).comp_mem t c ht_cof hc
  have hi' : cofibrations (SliceObj X) i' := by
    constructor
    · exact hi
    · refine ⟨R, r_Af, r_Q, hR.flip, t ≫ c, ?_, ?_, htc_cof⟩
      · dsimp [i', P]
        change r_Af ≫ (t ≫ c) = d_A ≫ c
        calc
          r_Af ≫ (t ≫ c) = (r_Af ≫ t) ≫ c := by simp [Category.assoc]
          _ = d_A ≫ c := by rw [htAf]
      · dsimp [i', P]
        change r_Q ≫ (t ≫ c) = q₀ ≫ d_QX ≫ c
        calc
          r_Q ≫ (t ≫ c) = (r_Q ≫ t) ≫ c := by simp [Category.assoc]
          _ = (q₀ ≫ d_QX) ≫ c := by
            simpa [Category.assoc] using congrArg (fun z => z ≫ c) htQ
          _ = q₀ ≫ (d_QX ≫ c) := by exact Category.assoc _ _ _
  have hw' : weakEquivalences (SliceObj X) w' := hw
  have hcomp : i' ≫ w' = f := by
    apply SliceObj.Hom.ext
    · change i ≫ w = f.v₀
      exact hfactor
    · dsimp [i', w']
      change (d_A ≫ c) ≫ w_f = f.vf
      calc
        (d_A ≫ c) ≫ w_f = d_A ≫ (c ≫ w_f) := by simp [Category.assoc]
        _ = d_A ≫ g := by rw [hcw]
        _ = f.vf := by simp [g, hD]
  refine ⟨P, i', w', rfl, hi', hw', hcomp, ?_, ?_⟩
  · change i = i ≫ eqToHom rfl
    simp
  · change w = eqToHom rfl ≫ w
    simp

#print axioms HomotopyHypothesis.Cylinder.SliceCategory.sliceForget_lift_factorization

end HomotopyHypothesis.Cylinder.SliceCategory
