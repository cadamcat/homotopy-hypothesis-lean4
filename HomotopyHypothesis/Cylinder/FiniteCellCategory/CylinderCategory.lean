import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Interfaces.AfinIotaMapIsPushout
import HomotopyHypothesis.Blueprint.Interfaces.WeakEquivalenceClosure
import HomotopyHypothesis.Cylinder.FiniteCellCategory.Cofibrations
import HomotopyHypothesis.Cylinder.FiniteCellCategory.FiniteCells
import HomotopyHypothesis.Cylinder.FiniteCellCategory.FiniteFactorization
import HomotopyHypothesis.Cylinder.FiniteCellCategory.WeakEquivalences
noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Blueprint HomotopyHypothesis.Henry

namespace HomotopyHypothesis.Cylinder.FiniteCellCategory

universe u

variable {C : GlobularTheory.{u}} (hC : C.IsCoherator)

 theorem afin_exists_cylinder {A : Afin C hC} (hA : IsInitial A) (X : Afin C hC) :
    Nonempty (RelativeCylinder (hA.to X)) := by
  let i := hA.to X
  have hi : cofibrations (Afin C hC) i :=
    (afin_isCofibrationCategory hC).initial_cofibration hA X
  have := afin_hasPushout hC i i hi
  let P := pushout i i
  let j₀ : X ⟶ P := pushout.inl i i
  let j₁ : X ⟶ P := pushout.inr i i
  have sq : IsPushout i i j₀ j₁ := .of_hasPushout i i
  have sqM := Packages.afin_ι_map_isPushout hC i i j₀ j₁ sq hi
  let f : P.obj ⟶ X.obj := sqM.desc (𝟙 X.obj) (𝟙 X.obj) (by simp)
  have hp : W hC (𝟙 X.obj) := (Packages.weakEquivalence_closure hC).1 _ inferInstance
  obtain ⟨T, c, t, p, hc, ht, hwp, hcomm, hcp, htp⟩ :=
    finiteCellMaps_extendsFactorization hC (initial.to P.obj) P.property
      (initial.to X.obj) X.property X.property (𝟙 X.obj) hp f
      (initialIsInitial.hom_ext _ _)
  let Y : Afin C hC := ⟨T, isFinitelyCellular_of_finiteCellMap X.property t ht⟩
  refine ⟨{
    P := P
    j₀ := j₀
    j₁ := j₁
    isPushout := sq
    I := Y
    c := ObjectProperty.homMk c
    p := ObjectProperty.homMk p
    c_mem := hc
    p_mem := hwp
    j₀_c_p := ?_
    j₁_c_p := ?_ }⟩
  · apply ObjectProperty.hom_ext
    change j₀.hom ≫ c ≫ p = 𝟙 X.obj
    rw [hcp]
    exact sqM.inl_desc _ _ _
  · apply ObjectProperty.hom_ext
    change j₁.hom ≫ c ≫ p = 𝟙 X.obj
    rw [hcp]
    exact sqM.inr_desc _ _ _

 theorem afin_trivialCofibration_cobaseChange {A B X Q : Afin C hC}
    (i : A ⟶ B) (f : A ⟶ X) (k : B ⟶ Q) (j : X ⟶ Q)
    (sq : IsPushout i f k j) (hi : cofibrations (Afin C hC) i)
    (hwi : weakEquivalences (Afin C hC) i) : weakEquivalences (Afin C hC) j := by
  exact model_trivialCofibration_cobaseChange hC i.hom f.hom k.hom j.hom
    (Packages.afin_ι_map_isPushout hC i f k j sq hi)
    (finiteCellMaps_le_cofibrations C _ hi) hwi
    (finiteCellMaps_le_cofibrations C _ A.property)
    (finiteCellMaps_le_cofibrations C _ X.property)

end HomotopyHypothesis.Cylinder.FiniteCellCategory

namespace HomotopyHypothesis.Blueprint.Packages

universe u

 theorem afin_isCylinderCategory_proof {C : GlobularTheory.{u}} (hC : C.IsCoherator) :
    IsCylinderCategory (Afin C hC) where
  toIsCofibrationCategory := Cylinder.FiniteCellCategory.afin_isCofibrationCategory hC
  isomorphisms_le_weakEquivalences := Cylinder.FiniteCellCategory.afin_weakEquivalence_isomorphisms hC
  weakEquivalences_isMultiplicative := Cylinder.FiniteCellCategory.afin_weakEquivalence_multiplicative hC
  twoOutOfSix := Cylinder.FiniteCellCategory.afin_weakEquivalence_twoOutOfSix hC
  trivialCofibration_cobaseChange := Cylinder.FiniteCellCategory.afin_trivialCofibration_cobaseChange hC
  exists_cylinder := Cylinder.FiniteCellCategory.afin_exists_cylinder hC
  exists_retraction := Cylinder.FiniteCellCategory.afin_trivialCofibration_retraction hC

#print axioms afin_isCylinderCategory_proof

end HomotopyHypothesis.Blueprint.Packages
