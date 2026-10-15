import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Cylinder.SliceCategory.Proofs
open CategoryTheory Limits HomotopicalAlgebra HomotopyHypothesis.Henry

universe u

namespace HomotopyHypothesis.Cylinder.SliceCategory

/-- Isomorphisms in a homotopy slice are cofibrations. -/
theorem sliceCofibration_isomorphisms {C : Type (u + 1)} [Category.{u} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [IsCylinderCategory C]
    (X : C) :
    MorphismProperty.isomorphisms (SliceObj X) ≤ cofibrations (SliceObj X) := by
  intro A B f hf
  haveI : IsIso f := hf
  let e₀ : A.A₀ ≅ B.A₀ :=
    { hom := f.v₀
      inv := (inv f).v₀
      hom_inv_id := by
        exact congrArg (fun g : A ⟶ A => g.v₀) (IsIso.hom_inv_id f)
      inv_hom_id := by
        exact congrArg (fun g : B ⟶ B => g.v₀) (IsIso.inv_hom_id f) }
  let e_f : A.Af ≅ B.Af :=
    { hom := f.vf
      inv := (inv f).vf
      hom_inv_id := by
        exact congrArg (fun g : A ⟶ A => g.vf) (IsIso.hom_inv_id f)
      inv_hom_id := by
        exact congrArg (fun g : B ⟶ B => g.vf) (IsIso.inv_hom_id f) }
  haveI : IsIso f.v₀ := e₀.isIso_hom
  haveI : IsIso f.vf := e_f.isIso_hom
  have hA₀ : cofibrations C f.v₀ :=
    IsCofibrationCategory.isomorphisms_le f.v₀
      (MorphismProperty.isomorphisms.infer_property f.v₀)
  have hId : cofibrations C (𝟙 B.Af) :=
    IsCofibrationCategory.isomorphisms_le (𝟙 B.Af)
      (MorphismProperty.isomorphisms.infer_property (𝟙 B.Af))
  have hbase : IsPushout A.a (𝟙 A.A₀) (𝟙 A.Af) A.a :=
    IsPushout.of_id_snd (f := A.a)
  have hpo : IsPushout A.a f.v₀ f.vf B.a :=
    hbase.of_iso (Iso.refl A.A₀) (Iso.refl A.Af) e₀ e_f
      (by simp) (by rfl) (by simpa [e_f]) (by simpa [e₀, e_f] using f.a_vf)
  refine ⟨hA₀, B.Af, f.vf, B.a, hpo, 𝟙 B.Af, ?_, ?_, hId⟩
  · simp
  · simp

/-- Cofibrations in a homotopy slice are closed under composition. -/
theorem sliceCofibration_comp {C : Type (u + 1)} [Category.{u} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [IsCylinderCategory C]
    {X : C} {A B D : SliceObj X} (f : A ⟶ B) (g : B ⟶ D)
    (hf : cofibrations (SliceObj X) f) (hg : cofibrations (SliceObj X) g) :
    cofibrations (SliceObj X) (f ≫ g) := by
  rcases hf with ⟨hf₀, hfglue⟩
  rcases hfglue with ⟨P_f, k_f, j_f, hP_f, m_f, hkm_f, hjm_f, hm_f⟩
  rcases hg with ⟨hg₀, hgglue⟩
  rcases hgglue with ⟨P_g, k_g, j_g, hP_g, m_g, hkm_g, hjm_g, hm_g⟩
  have hh₀ : cofibrations C (f.v₀ ≫ g.v₀) :=
    (IsCofibrationCategory.isMultiplicative (C := C)).comp_mem f.v₀ g.v₀ hf₀ hg₀
  letI : HasPushout (f.v₀ ≫ g.v₀) A.a :=
    IsCofibrationCategory.hasPushout (C := C) (f.v₀ ≫ g.v₀) A.a hh₀
  let P_h := pushout (f.v₀ ≫ g.v₀) A.a
  let k_h : D.A₀ ⟶ P_h := pushout.inl (f.v₀ ≫ g.v₀) A.a
  let j_h : A.Af ⟶ P_h := pushout.inr (f.v₀ ≫ g.v₀) A.a
  let hP_h : IsPushout (f.v₀ ≫ g.v₀) A.a k_h j_h :=
    IsPushout.of_hasPushout (f.v₀ ≫ g.v₀) A.a
  have hucompat : A.a ≫ j_h = f.v₀ ≫ (g.v₀ ≫ k_h) := by
    calc
      A.a ≫ j_h = (f.v₀ ≫ g.v₀) ≫ k_h := hP_h.w.symm
      _ = f.v₀ ≫ (g.v₀ ≫ k_h) := by simp [Category.assoc]
  let u : P_f ⟶ P_h := hP_f.desc j_h (g.v₀ ≫ k_h) hucompat
  have huAf : k_f ≫ u = j_h := by simp [u, hP_f]
  have huB₀ : j_f ≫ u = g.v₀ ≫ k_h := by simp [u, hP_f]
  have hφcompat : (f.v₀ ≫ g.v₀) ≫ j_g = A.a ≫ (f.vf ≫ k_g) := by
    calc
      (f.v₀ ≫ g.v₀) ≫ j_g = f.v₀ ≫ (g.v₀ ≫ j_g) := by simp [Category.assoc]
      _ = f.v₀ ≫ (B.a ≫ k_g) := by rw [hP_g.w.symm]
      _ = (f.v₀ ≫ B.a) ≫ k_g := by simp [Category.assoc]
      _ = (A.a ≫ f.vf) ≫ k_g := by rw [f.a_vf.symm]
      _ = A.a ≫ (f.vf ≫ k_g) := by simp [Category.assoc]
  let φ : P_h ⟶ P_g := hP_h.desc j_g (f.vf ≫ k_g) hφcompat
  have hφAf : j_h ≫ φ = f.vf ≫ k_g := by simp [φ, hP_h]
  have hφD₀ : k_h ≫ φ = j_g := by simp [φ, hP_h]
  have hcomm : m_f ≫ k_g = u ≫ φ := by
    apply hP_f.hom_ext
    · calc
        k_f ≫ (m_f ≫ k_g) = (k_f ≫ m_f) ≫ k_g := by simp [Category.assoc]
        _ = f.vf ≫ k_g := by rw [hkm_f]
        _ = j_h ≫ φ := hφAf.symm
        _ = (k_f ≫ u) ≫ φ := by rw [huAf]
        _ = k_f ≫ (u ≫ φ) := by simp [Category.assoc]
    · calc
        j_f ≫ (m_f ≫ k_g) = (j_f ≫ m_f) ≫ k_g := by simp [Category.assoc]
        _ = B.a ≫ k_g := by rw [hjm_f]
        _ = g.v₀ ≫ j_g := hP_g.w
        _ = g.v₀ ≫ (k_h ≫ φ) := by rw [hφD₀]
        _ = (g.v₀ ≫ k_h) ≫ φ := by simp [Category.assoc]
        _ = (j_f ≫ u) ≫ φ := by rw [huB₀.symm]
        _ = j_f ≫ (u ≫ φ) := by simp [Category.assoc]
  let coc : PushoutCocone m_f u := PushoutCocone.mk k_g φ hcomm
  have hcoc : IsColimit coc := by
    apply PushoutCocone.isColimitAux' coc
    intro s
    have hs : m_f ≫ s.inl = u ≫ s.inr := s.condition
    have hbase : g.v₀ ≫ (k_h ≫ s.inr) = B.a ≫ s.inl := by
      calc
        g.v₀ ≫ (k_h ≫ s.inr) = (g.v₀ ≫ k_h) ≫ s.inr := by simp [Category.assoc]
        _ = (j_f ≫ u) ≫ s.inr := by rw [huB₀.symm]
        _ = j_f ≫ (u ≫ s.inr) := by simp [Category.assoc]
        _ = j_f ≫ (m_f ≫ s.inl) := by rw [← hs]
        _ = (j_f ≫ m_f) ≫ s.inl := by simp [Category.assoc]
        _ = B.a ≫ s.inl := by rw [hjm_f]
    let z : P_g ⟶ s.pt := hP_g.desc s.inl (k_h ≫ s.inr) hbase.symm
    have hzk : k_g ≫ z = s.inl := by simp [z, hP_g]
    have hzj : j_g ≫ z = k_h ≫ s.inr := by simp [z, hP_g]
    have hφz : φ ≫ z = s.inr := by
      apply hP_h.hom_ext
      · calc
          k_h ≫ (φ ≫ z) = (k_h ≫ φ) ≫ z := by simp [Category.assoc]
          _ = j_g ≫ z := by rw [hφD₀]
          _ = k_h ≫ s.inr := hzj
      · calc
          j_h ≫ (φ ≫ z) = (j_h ≫ φ) ≫ z := by simp [Category.assoc]
          _ = (f.vf ≫ k_g) ≫ z := by rw [hφAf]
          _ = f.vf ≫ (k_g ≫ z) := by simp [Category.assoc]
          _ = f.vf ≫ s.inl := by rw [hzk]
          _ = (k_f ≫ m_f) ≫ s.inl := by rw [hkm_f]
          _ = k_f ≫ (m_f ≫ s.inl) := by simp [Category.assoc]
          _ = k_f ≫ (u ≫ s.inr) := by rw [hs]
          _ = (k_f ≫ u) ≫ s.inr := by simp [Category.assoc]
          _ = j_h ≫ s.inr := by rw [huAf]
    refine ⟨z, hzk, hφz, ?_⟩
    intro z' hz'k hz'φ
    change P_g ⟶ s.pt at z'
    change k_g ≫ z' = s.inl at hz'k
    change φ ≫ z' = s.inr at hz'φ
    apply hP_g.hom_ext
    · exact hz'k.trans hzk.symm
    · calc
        j_g ≫ z' = (k_h ≫ φ) ≫ z' := by rw [hφD₀]
        _ = k_h ≫ (φ ≫ z') := by simp [Category.assoc]
        _ = k_h ≫ s.inr := by rw [hz'φ]
        _ = j_g ≫ z := hzj.symm
  have hpush : IsPushout m_f u k_g φ := IsPushout.of_isColimit hcoc
  have hφcof : cofibrations C φ :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout hpush.flip hm_f
  have hm_h : cofibrations C (φ ≫ m_g) :=
    (IsCofibrationCategory.isMultiplicative (C := C)).comp_mem φ m_g hφcof hm_g
  have hcompglue : IsCofibrantGluing A.a (f.v₀ ≫ g.v₀) ((f ≫ g).vf) D.a := by
    refine ⟨P_h, j_h, k_h, hP_h.flip, φ ≫ m_g, ?_, ?_, hm_h⟩
    · calc
        j_h ≫ (φ ≫ m_g) = (j_h ≫ φ) ≫ m_g := by simp [Category.assoc]
        _ = (f.vf ≫ k_g) ≫ m_g := by rw [hφAf]
        _ = f.vf ≫ (k_g ≫ m_g) := by simp [Category.assoc]
        _ = f.vf ≫ g.vf := by rw [hkm_g]
    · calc
        k_h ≫ (φ ≫ m_g) = (k_h ≫ φ) ≫ m_g := by simp [Category.assoc]
        _ = j_g ≫ m_g := by rw [hφD₀]
        _ = D.a := hjm_g
  refine ⟨hh₀, hcompglue⟩

/-- Identity morphisms in a homotopy slice are cofibrations. -/
theorem sliceCofibration_id {C : Type (u + 1)} [Category.{u} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [IsCylinderCategory C]
    {X : C} (A : SliceObj X) : cofibrations (SliceObj X) (𝟙 A) := by
  have hId₀ : cofibrations C (𝟙 A.A₀) :=
    IsCofibrationCategory.isomorphisms_le (𝟙 A.A₀)
      (MorphismProperty.isomorphisms.infer_property (𝟙 A.A₀))
  have hIdf : cofibrations C (𝟙 A.Af) :=
    IsCofibrationCategory.isomorphisms_le (𝟙 A.Af)
      (MorphismProperty.isomorphisms.infer_property (𝟙 A.Af))
  refine ⟨hId₀, ?_⟩
  refine ⟨A.Af, 𝟙 A.Af, A.a, ?_, 𝟙 A.Af, ?_, ?_, hIdf⟩
  · exact IsPushout.of_id_snd (f := A.a)
  · change 𝟙 A.Af ≫ 𝟙 A.Af = 𝟙 A.Af
    simp
  · simp

/-- Cofibrations in a homotopy slice form a multiplicative class. -/
theorem sliceCofibration_multiplicative {C : Type (u + 1)} [Category.{u} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [IsCylinderCategory C]
    {X : C} : (cofibrations (SliceObj X)).IsMultiplicative := by
  haveI : (cofibrations (SliceObj X)).ContainsIdentities :=
    ⟨fun A => sliceCofibration_id A⟩
  haveI : (cofibrations (SliceObj X)).IsStableUnderComposition :=
    ⟨fun f g hf hg => sliceCofibration_comp f g hf hg⟩
  exact ⟨⟩

#print axioms HomotopyHypothesis.Cylinder.SliceCategory.sliceCofibration_isomorphisms
#print axioms HomotopyHypothesis.Cylinder.SliceCategory.sliceCofibration_comp
#print axioms HomotopyHypothesis.Cylinder.SliceCategory.sliceCofibration_id
#print axioms HomotopyHypothesis.Cylinder.SliceCategory.sliceCofibration_multiplicative

end HomotopyHypothesis.Cylinder.SliceCategory
