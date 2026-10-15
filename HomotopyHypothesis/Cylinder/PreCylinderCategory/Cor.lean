import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Cylinder.PreCylinderCategory.Basic
import HomotopyHypothesis.Cylinder.PreCylinderCategory.Brown
namespace HomotopyHypothesis.Cylinder.PreCylinderCategory

open CategoryTheory Limits HomotopicalAlgebra HomotopyHypothesis.Henry

universe v u

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C]

/-- H Cor 2.2.2(1): a weak equivalence factors as a trivial cofibration followed by
a map with a trivial-cofibration section. -/
theorem we_factor [IsCylinderCategory C] {A B : C} (f : A ⟶ B)
    (hf : weakEquivalences C f) :
    ∃ (P : C) (i : A ⟶ P) (p : P ⟶ B) (s : B ⟶ P),
      i ≫ p = f ∧ s ≫ p = 𝟙 B ∧ cofibrations C i ∧ weakEquivalences C i ∧
      cofibrations C s ∧ weakEquivalences C s ∧ weakEquivalences C p := by
  haveI := we_twoOutOfThree (C := C)
  obtain ⟨bf⟩ := brown_factorization (C := C) f
  have hi : weakEquivalences C bf.i := by
    -- i≫p = f WE, p WE → i WE
    have hfac : weakEquivalences C (bf.i ≫ bf.p) := by
      rw [bf.fac]
      exact hf
    exact MorphismProperty.of_postcomp (weakEquivalences C) _ _ bf.we_p hfac
  exact ⟨bf.P, bf.i, bf.p, bf.s, bf.fac, bf.sec, bf.cof_i, hi,
    bf.cof_s, bf.we_s, bf.we_p⟩

/-- H Cor 2.2.2(2), Ken Brown's lemma for cylinder categories: a functor preserving
trivial cofibrations preserves weak equivalences. -/
theorem kenBrown [IsCylinderCategory C] {D : Type*} [Category D]
    [CategoryWithCofibrations D] [CategoryWithWeakEquivalences D] [IsCylinderCategory D]
    (F : C ⥤ D)
    (hF : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), cofibrations C f → weakEquivalences C f →
      cofibrations D (F.map f) ∧ weakEquivalences D (F.map f))
    {X Y : C} (f : X ⟶ Y) (hf : weakEquivalences C f) :
    weakEquivalences D (F.map f) := by
  haveI := we_twoOutOfThree (C := D)
  obtain ⟨P, i, p, s, hfac, hsec, hcof_i, hwe_i, hcof_s, hwe_s, _⟩ :=
    we_factor (C := C) f hf
  obtain ⟨_, hwe_Fi⟩ := hF i hcof_i hwe_i
  obtain ⟨_, hwe_Fs⟩ := hF s hcof_s hwe_s
  have hFp : weakEquivalences D (F.map p) := by
    have hsecF : F.map s ≫ F.map p = 𝟙 (F.obj Y) := by
      rw [← F.map_comp, hsec, F.map_id]
    have hid : weakEquivalences D (𝟙 (F.obj Y)) := we_id (F.obj Y)
    have hsecWE : weakEquivalences D (F.map s ≫ F.map p) := by
      rw [hsecF]
      exact hid
    exact MorphismProperty.of_precomp (weakEquivalences D) _ _ hwe_Fs hsecWE
  have hFfac : F.map i ≫ F.map p = F.map f := by
    rw [← F.map_comp, hfac]
  have hcomp : weakEquivalences D (F.map i ≫ F.map p) :=
    IsCylinderCategory.weakEquivalences_isMultiplicative.toIsStableUnderComposition.comp_mem
      _ _ hwe_Fi hFp
  rw [hFfac] at hcomp
  exact hcomp

end HomotopyHypothesis.Cylinder.PreCylinderCategory
