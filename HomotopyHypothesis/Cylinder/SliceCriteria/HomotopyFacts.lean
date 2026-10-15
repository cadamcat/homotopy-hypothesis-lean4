import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.CylinderCategoryTheory.Proofs
import HomotopyHypothesis.Category.SemiModelStructure.CylinderFacts
open CategoryTheory Limits HomotopicalAlgebra HomotopyHypothesis.Henry

universe v u v' u'

namespace HomotopyHypothesis.Cylinder.SliceCriteria

section Homotopies

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [IsCylinderCategory C]

theorem homotopic_normalize {X Y : C} {f g : X ⟶ Y}
    (h : Homotopic f g) {O : C} (hO : IsInitial O) :
    RelHomotopic (hO.to X) f g := by
  obtain ⟨O', hO', hrel⟩ := h
  have hsq : hO.to X ≫ 𝟙 X = hO.to O' ≫ hO'.to X := hO.hom_ext _ _
  simpa using Category.SemiModelStructure.relHomotopic_precomp (hO'.to X) (hO.to X)
    (hO.to O') (𝟙 X) hsq (IsCofibrationCategory.initial_cofibration hO X) hrel

theorem homotopic_symm {X Y : C} {f g : X ⟶ Y}
    (h : Homotopic f g) : Homotopic g f := by
  obtain ⟨O, hO, hrel⟩ := h
  exact ⟨O, hO, (_root_.HomotopyHypothesis.CylinderCategoryTheory.relHomotopic_equivalence_proof (hO.to X)
    (IsCofibrationCategory.initial_cofibration hO X)).1.symm hrel⟩

theorem homotopic_trans {X Y : C} {f g h : X ⟶ Y}
    (hfg : Homotopic f g) (hgh : Homotopic g h) : Homotopic f h := by
  obtain ⟨O, hO, hrel⟩ := hfg
  exact ⟨O, hO, (_root_.HomotopyHypothesis.CylinderCategoryTheory.relHomotopic_equivalence_proof (hO.to X)
    (IsCofibrationCategory.initial_cofibration hO X)).1.trans hrel
      (homotopic_normalize hgh hO)⟩

theorem homotopic_postcomp {X Y Z : C} {f g : X ⟶ Y}
    (h : Homotopic f g) (k : Y ⟶ Z) : Homotopic (f ≫ k) (g ≫ k) := by
  obtain ⟨O, hO, cyl, H, h₀, h₁⟩ := h
  refine ⟨O, hO, cyl, H ≫ k, ?_, ?_⟩
  · simpa [Category.assoc] using congrArg (fun z => z ≫ k) h₀
  · simpa [Category.assoc] using congrArg (fun z => z ≫ k) h₁

theorem homotopic_precomp {X Y Z : C} {f g : Y ⟶ Z}
    (h : Homotopic f g) (k : X ⟶ Y) : Homotopic (k ≫ f) (k ≫ g) := by
  obtain ⟨O, hO, hrel⟩ := h
  have hsq : hO.to X ≫ k = 𝟙 O ≫ hO.to Y := hO.hom_ext _ _
  exact ⟨O, hO, Category.SemiModelStructure.relHomotopic_precomp (hO.to Y) (hO.to X)
    (𝟙 O) k hsq (IsCofibrationCategory.initial_cofibration hO X) hrel⟩

variable {D : Type u'} [Category.{v'} D] [CategoryWithCofibrations D]
  [CategoryWithWeakEquivalences D]

/-- Exact functors carry cylinder homotopies to cylinder homotopies. -/
theorem homotopic_map {F : C ⥤ D} (hF : IsCylinderMorphism F)
    {X Y : C} {f g : X ⟶ Y} (h : Homotopic f g) :
    Homotopic (F.map f) (F.map g) := by
  obtain ⟨O, hO, cyl, H, h₀, h₁⟩ := h
  obtain ⟨hFO⟩ := hF.map_initial hO
  have heq : F.map (hO.to X) = hFO.to (F.obj X) := hFO.hom_ext _ _
  let mapped : RelativeCylinder (F.map (hO.to X)) :=
    { P := F.obj cyl.P
      j₀ := F.map cyl.j₀
      j₁ := F.map cyl.j₁
      isPushout := hF.map_isPushout _ _ _ _ cyl.isPushout
        (IsCofibrationCategory.initial_cofibration hO X)
      I := F.obj cyl.I
      c := F.map cyl.c
      p := F.map cyl.p
      c_mem := hF.map_cofibration cyl.c cyl.c_mem
      p_mem := hF.map_weakEquivalence cyl.p cyl.p_mem
      j₀_c_p := by
        calc
          F.map cyl.j₀ ≫ F.map cyl.c ≫ F.map cyl.p =
              F.map (cyl.j₀ ≫ cyl.c ≫ cyl.p) := by simp only [Functor.map_comp]
          _ = F.map (𝟙 X) := congrArg F.map cyl.j₀_c_p
          _ = 𝟙 _ := F.map_id X
      j₁_c_p := by
        calc
          F.map cyl.j₁ ≫ F.map cyl.c ≫ F.map cyl.p =
              F.map (cyl.j₁ ≫ cyl.c ≫ cyl.p) := by simp only [Functor.map_comp]
          _ = F.map (𝟙 X) := congrArg F.map cyl.j₁_c_p
          _ = 𝟙 _ := F.map_id X }
  have hrel : RelHomotopic (F.map (hO.to X)) (F.map f) (F.map g) := by
    refine ⟨mapped, F.map H, ?_, ?_⟩
    · simpa only [Functor.map_comp] using congrArg F.map h₀
    · simpa only [Functor.map_comp] using congrArg F.map h₁
  exact ⟨F.obj O, hFO, heq ▸ hrel⟩

end Homotopies

section Extension

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [IsCylinderCategory C]

/-- An extension up to homotopy along a cofibration can be made exact. -/
theorem cofibration_extension_of_homotopic {A B Z : C} (i : A ⟶ B)
    (hi : cofibrations C i) (a : A ⟶ Z) (b : B ⟶ Z)
    (h : Homotopic (i ≫ b) a) : ∃ b' : B ⟶ Z, i ≫ b' = a := by
  classical
  obtain ⟨O, hO, cyl, H, h₀, h₁⟩ := h
  have hend := Category.SemiModelStructure.relativeCylinder_endpoint_properties
    (IsCofibrationCategory.initial_cofibration hO A) cyl
  let e₀ : A ⟶ cyl.I := cyl.j₀ ≫ cyl.c
  let e₁ : A ⟶ cyl.I := cyl.j₁ ≫ cyl.c
  have he₀ : e₀ ≫ cyl.p = 𝟙 A := by simpa only [e₀, Category.assoc] using cyl.j₀_c_p
  have he₁ : e₁ ≫ cyl.p = 𝟙 A := by simpa only [e₁, Category.assoc] using cyl.j₁_c_p
  letI : HasPushout e₀ i := IsCofibrationCategory.hasPushout e₀ i hend.1.1
  let P := pushout e₀ i
  let k : cyl.I ⟶ P := pushout.inl e₀ i
  let j : B ⟶ P := pushout.inr e₀ i
  have hP : IsPushout e₀ i k j := IsPushout.of_hasPushout e₀ i
  have hcompat : e₀ ≫ (cyl.p ≫ i) = i ≫ 𝟙 B := by
    rw [← Category.assoc, he₀]
    simp
  let p : P ⟶ B := hP.desc (cyl.p ≫ i) (𝟙 B) hcompat
  have hjp : j ≫ p = 𝟙 B := hP.inr_desc _ _ _
  have hkp : k ≫ p = cyl.p ≫ i := hP.inl_desc _ _ _
  have hjw : weakEquivalences C j :=
    IsCylinderCategory.trivialCofibration_cobaseChange e₀ i k j hP hend.1.1 hend.1.2
  have hId : weakEquivalences C (𝟙 B) :=
    IsCylinderCategory.isomorphisms_le_weakEquivalences _
      (MorphismProperty.isomorphisms.infer_property _)
  have hpw : weakEquivalences C p :=
    (IsCylinderCategory.twoOutOfSix (𝟙 B) j p (by simpa using hjw)
      (by rw [hjp]; exact hId)).2.2.1
  have hsq : i ≫ 𝟙 B = (e₁ ≫ k) ≫ p := by
    rw [Category.assoc, hkp, ← Category.assoc, he₁]
    simp
  obtain ⟨l, hl⟩ := Category.SemiModelStructure.cofibration_lifts_against_weak_equivalence
    i hi (e₁ ≫ k) p (𝟙 B) hsq hpw
  have hcompatH : e₀ ≫ H = i ≫ b := by simpa [e₀, Category.assoc] using h₀
  let t : P ⟶ Z := hP.desc H b hcompatH
  have hkt : k ≫ t = H := hP.inl_desc _ _ _
  refine ⟨l ≫ t, ?_⟩
  calc
    i ≫ (l ≫ t) = (e₁ ≫ k) ≫ t := by rw [← Category.assoc, hl]
    _ = e₁ ≫ H := by rw [Category.assoc, hkt]
    _ = a := by simpa [e₁, Category.assoc] using h₁

end Extension

#print axioms homotopic_map
#print axioms cofibration_extension_of_homotopic

end HomotopyHypothesis.Cylinder.SliceCriteria
