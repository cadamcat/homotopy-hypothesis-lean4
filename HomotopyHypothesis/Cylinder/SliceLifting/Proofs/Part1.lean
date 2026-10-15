import HomotopyHypothesis.Blueprint.Henry.Constructions
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiModel
import HomotopyHypothesis.Cylinder.SliceCategory.Proofs

/-!
# `HomotopyHypothesis.Cylinder.SliceLifting.Proofs`, part 1

Lines 18–61 of `HomotopyHypothesis.Cylinder.SliceLifting.Proofs`, split so that the modules of the development form an acyclic import graph.
-/

open CategoryTheory Limits HomotopicalAlgebra
open HomotopyHypothesis.Henry

universe u

namespace HomotopyHypothesis.Cylinder.SliceLifting

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {C : Type (u + 1)} [Category.{u} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [IsCylinderCategory C]

/-- Extensionality for morphisms in `SliceObj X`. -/
theorem hom_ext {X : C} {A B : SliceObj X} (f g : A ⟶ B)
    (h₀ : f.v₀ = g.v₀) (hf : f.vf = g.vf) : f = g :=
  SliceObj.Hom.ext h₀ hf

/-- The pushout of an identity map along any map `f` is given by `f` and the identity. -/
theorem isPushout_id_left {Z Y : C} (f : Z ⟶ Y) :
    IsPushout (𝟙 Z) f f (𝟙 Y) := by
  refine IsPushout.mk' (by simp)
    (fun T φ ψ hk hj => by simpa using hj)
    (fun T a b h => ⟨b, by simpa using h.symm, by simp⟩)

/-- An initial object in the homotopy slice category `SliceObj X`. -/
theorem slice_exists_initial (X : C) : ∃ I : SliceObj X, Nonempty (IsInitial I) := by
  obtain ⟨I, ⟨hI⟩⟩ := IsCofibrationCategory.exists_initial (C := C)
  have hx_cof : cofibrations C (𝟙 X) :=
    IsCofibrationCategory.isomorphisms_le _ (inferInstanceAs (IsIso (𝟙 X)))
  have hx_we : weakEquivalences C (𝟙 X) :=
    IsCylinderCategory.isomorphisms_le_weakEquivalences _ (inferInstanceAs (IsIso (𝟙 X)))
  have hpo : IsPushout (hI.to I) (hI.to X) (hI.to X) (𝟙 X) := by
    have hI_id : hI.to I = 𝟙 I := hI.hom_ext _ _
    rw [hI_id]
    exact isPushout_id_left (hI.to X)
  have hpair : IsCofibrantPair (hI.to X) (𝟙 X) := by
    refine ⟨I, hI, X, hI.to X, 𝟙 X, hpo, 𝟙 X, ?_, ?_, hx_cof⟩
    · simp
    · simp
  let initObj : SliceObj X :=
    { A₀ := I
      Af := X
      a := hI.to X
      x := 𝟙 X
      cofibrant := hpair
      x_cofibration := hx_cof
      x_weakEquivalence := hx_we }
  refine ⟨initObj, ⟨IsInitial.ofUniqueHom (fun Y => ⟨hI.to Y.A₀, Y.x, hI.hom_ext _ _, Category.id_comp Y.x⟩) ?_⟩⟩
  intro Y m
  apply SliceObj.Hom.ext
  · exact hI.hom_ext _ _
  · calc
      m.vf = 𝟙 X ≫ m.vf := by simp
      _ = initObj.x ≫ m.vf := rfl
      _ = Y.x := m.x_vf
