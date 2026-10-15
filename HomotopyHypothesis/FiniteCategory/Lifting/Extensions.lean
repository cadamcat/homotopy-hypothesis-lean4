import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.CylinderCategoryTheory.Proofs
import HomotopyHypothesis.FiniteCategory.Lifting.Exactness
/-!+# Extension lifting for pre-fibrations

Pre-fibrations lift extensions across trivial cofibrations. They also turn extensions whose
images have the required relative homotopy into extensions with the required image exactly.
-/

universe v u v₁ u₁

open CategoryTheory Limits HomotopicalAlgebra
open HomotopyHypothesis.Henry

namespace HomotopyHypothesis.FiniteCategory.Lifting

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [IsCylinderCategory C]
  {D : Type u₁} [Category.{v₁} D] [CategoryWithCofibrations D]
  [CategoryWithWeakEquivalences D] [IsCylinderCategory D]

/-- A pre-fibration lifts an extension across a trivial cofibration. -/
theorem lift_trivialCofibration_extension {p : C ⥤ D}
    (hp : IsPreFibration p) (hm : IsCylinderMorphism p)
    {A B T : C} (i : A ⟶ B) (hi : cofibrations C i) (hw : weakEquivalences C i)
    (a : A ⟶ T) (w : p.obj B ⟶ p.obj T) (hsq : p.map i ≫ w = p.map a) :
    ∃ b : B ⟶ T, i ≫ b = a ∧ p.map b = w := by
  classical
  letI : HasPushout i a := IsCofibrationCategory.hasPushout i a hi
  let P := pushout i a
  let k : B ⟶ P := pushout.inl i a
  let j : T ⟶ P := pushout.inr i a
  have sq : IsPushout i a k j := IsPushout.of_hasPushout i a
  have hj : cofibrations C j :=
    (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout sq.flip hi
  have hwj : weakEquivalences C j :=
    IsCylinderCategory.trivialCofibration_cobaseChange i a k j sq hi hw
  have psq := hm.map_isPushout i a k j sq hi
  let r : p.obj P ⟶ p.obj T := psq.desc w (𝟙 _) (by simpa using hsq)
  have hjr : p.map j ≫ r = 𝟙 _ := psq.inr_desc _ _ _
  obtain ⟨r', hr', hpr'⟩ := hp.lift_retraction j hj hwj r hjr
  refine ⟨k ≫ r', ?_, ?_⟩
  · rw [← Category.assoc, sq.w, Category.assoc, hr', Category.comp_id]
  · rw [p.map_comp, hpr']
    exact psq.inl_desc _ _ _

/-- The first endpoint of a relative cylinder of a cofibration is a trivial cofibration. -/
theorem relativeCylinder_endpoint {A B : C} {i : A ⟶ B}
    (hi : cofibrations C i) (cyl : RelativeCylinder i) :
    cofibrations C (cyl.j₀ ≫ cyl.c) ∧ weakEquivalences C (cyl.j₀ ≫ cyl.c) := by
  have hj := (IsCofibrationCategory.isStableUnderCobaseChange (C := C)).of_isPushout
    cyl.isPushout hi
  have hc := (IsCofibrationCategory.isMultiplicative (C := C)).comp_mem _ _ hj cyl.c_mem
  have hid : weakEquivalences C (𝟙 B) :=
    IsCylinderCategory.isomorphisms_le_weakEquivalences _ inferInstance
  have hw := IsCylinderCategory.twoOutOfSix (cyl.j₀ ≫ cyl.c) cyl.p (𝟙 B)
    (by simpa [Category.assoc, cyl.j₀_c_p] using hid) (by simpa using cyl.p_mem)
  exact ⟨hc, hw.1⟩

/-- A cylinder morphism sends a relative cylinder to a relative cylinder. -/
def mapRelativeCylinder {p : C ⥤ D} (hm : IsCylinderMorphism p)
    {A B : C} {i : A ⟶ B} (hi : cofibrations C i) (cyl : RelativeCylinder i) :
    RelativeCylinder (p.map i) where
  P := p.obj cyl.P
  j₀ := p.map cyl.j₀
  j₁ := p.map cyl.j₁
  isPushout := hm.map_isPushout i i cyl.j₀ cyl.j₁ cyl.isPushout hi
  I := p.obj cyl.I
  c := p.map cyl.c
  p := p.map cyl.p
  c_mem := hm.map_cofibration _ cyl.c_mem
  p_mem := hm.map_weakEquivalence _ cyl.p_mem
  j₀_c_p := by rw [← p.map_comp, ← p.map_comp, cyl.j₀_c_p, p.map_id]
  j₁_c_p := by rw [← p.map_comp, ← p.map_comp, cyl.j₁_c_p, p.map_id]

/-- An extension homotopic to an image extension can be lifted with its exact image. -/
theorem lift_homotopic_extension {p : C ⥤ D} (hp : IsPreFibration p)
    (hm : IsCylinderMorphism p) {A B T : C} (i : A ⟶ B) (hi : cofibrations C i)
    (v : B ⟶ T) (w : p.obj B ⟶ p.obj T)
    (h : RelHomotopic (p.map i) (p.map v) w) :
    ∃ v' : B ⟶ T, i ≫ v' = i ≫ v ∧ p.map v' = w := by
  obtain ⟨cyl, _, _, _⟩ :=
    (_root_.HomotopyHypothesis.CylinderCategoryTheory.relHomotopic_equivalence_proof i hi).1.refl v
  let pcyl := mapRelativeCylinder hm hi cyl
  obtain ⟨H, h₀, h₁⟩ :=
    (_root_.HomotopyHypothesis.CylinderCategoryTheory.relHomotopic_equivalence_proof (p.map i)
      (hm.map_cofibration i hi)).2 pcyl (p.map v) w h
  dsimp only [pcyl, mapRelativeCylinder] at H h₀ h₁
  have hext : p.map (cyl.j₀ ≫ cyl.c) ≫ H = p.map v := by
    rw [p.map_comp, Category.assoc]
    exact h₀
  obtain ⟨H', hH', hpH'⟩ := lift_trivialCofibration_extension hp hm _
    (relativeCylinder_endpoint hi cyl).1 (relativeCylinder_endpoint hi cyl).2 v H hext
  refine ⟨cyl.j₁ ≫ cyl.c ≫ H', ?_, ?_⟩
  · calc
      i ≫ (cyl.j₁ ≫ cyl.c ≫ H') = i ≫ (cyl.j₀ ≫ cyl.c ≫ H') := by
        rw [← Category.assoc, ← cyl.isPushout.w, Category.assoc]
      _ = i ≫ v := by simpa only [Category.assoc] using congrArg (fun f => i ≫ f) hH'
  · simpa only [Functor.map_comp, hpH'] using h₁

/-- Acyclic pre-fibrations lift every prescribed extension across a cofibration. -/
theorem lift_acyclic_extension {p : C ⥤ D} (hp : IsPreFibration p)
    (hm : IsCylinderMorphism p) (ha : IsAcyclic p)
    {A B T : C} (i : A ⟶ B) (hi : cofibrations C i) (a : A ⟶ T)
    (w : p.obj B ⟶ p.obj T) (hsq : p.map i ≫ w = p.map a) :
    ∃ b : B ⟶ T, i ≫ b = a ∧ p.map b = w := by
  obtain ⟨v, hv, hrel⟩ := ha.2 i hi a w hsq
  obtain ⟨v', hv', hpv'⟩ := lift_homotopic_extension hp hm i hi v w hrel
  exact ⟨v', hv'.trans hv, hpv'⟩

/-- Extensions into an h-terminal object are homotopic relative to their common boundary. -/
theorem relHomotopic_of_hterminal {A B T : C} (hT : IsHTerminal T)
    (i : A ⟶ B) (hi : cofibrations C i) (f g : B ⟶ T) (hfg : i ≫ f = i ≫ g) :
    RelHomotopic i f g := by
  obtain ⟨cyl, _, _, _⟩ :=
    (_root_.HomotopyHypothesis.CylinderCategoryTheory.relHomotopic_equivalence_proof i hi).1.refl f
  let a := cyl.isPushout.desc f g hfg
  obtain ⟨H, hH⟩ := hT cyl.c cyl.c_mem a
  refine ⟨cyl, H, ?_, ?_⟩
  · rw [hH]
    exact cyl.isPushout.inl_desc _ _ _
  · rw [hH]
    exact cyl.isPushout.inr_desc _ _ _

/-- A pre-fibration lifts prescribed extensions into h-terminal objects with h-terminal image. -/
theorem lift_hterminal_extension {p : C ⥤ D} (hp : IsPreFibration p)
    (hm : IsCylinderMorphism p) {A B T : C} (hT : IsHTerminal T)
    (hpT : IsHTerminal (p.obj T)) (i : A ⟶ B) (hi : cofibrations C i) (a : A ⟶ T)
    (w : p.obj B ⟶ p.obj T) (hsq : p.map i ≫ w = p.map a) :
    ∃ b : B ⟶ T, i ≫ b = a ∧ p.map b = w := by
  obtain ⟨v, hv⟩ := hT i hi a
  have hrel : RelHomotopic (p.map i) (p.map v) w :=
    relHomotopic_of_hterminal hpT _ (hm.map_cofibration i hi) _ _ (by
      rw [← p.map_comp, hv, hsq])
  obtain ⟨v', hv', hpv'⟩ := lift_homotopic_extension hp hm i hi v w hrel
  exact ⟨v', hv'.trans hv, hpv'⟩

#print axioms lift_trivialCofibration_extension
#print axioms lift_homotopic_extension
#print axioms lift_acyclic_extension
#print axioms lift_hterminal_extension

end HomotopyHypothesis.FiniteCategory.Lifting
