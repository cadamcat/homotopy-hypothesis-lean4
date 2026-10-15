import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Interfaces.AfinIotaMapInitial
import HomotopyHypothesis.Blueprint.Interfaces.AfinIotaMapIsPushout
import HomotopyHypothesis.Blueprint.Interfaces.Fibrant
import HomotopyHypothesis.Blueprint.Interfaces.TrivialCofibrationLift
import HomotopyHypothesis.Blueprint.Interfaces.WeakEquivalenceClosure
import HomotopyHypothesis.Blueprint.Interfaces.WeakEquivalenceTwoOutOfSix
import HomotopyHypothesis.Cylinder.FiniteCellCategory.FiniteCells
noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open OAI.Grothendieck OAI.Grothendieck.GlobularTheory.Model
open HomotopyHypothesis.Blueprint HomotopyHypothesis.Henry

namespace HomotopyHypothesis.Cylinder.FiniteCellCategory

universe u

variable {C : GlobularTheory.{u}} (hC : C.IsCoherator)

 def afinInitial : Afin C hC := ⟨⊥_ C.Model, initial_finitelyCellular C⟩

 def afinInitial_isInitial : IsInitial (afinInitial hC) :=
  IsInitial.ofUniqueHom
    (fun X => ObjectProperty.homMk (initial.to X.obj))
    (fun X f => by apply ObjectProperty.hom_ext; exact initialIsInitial.hom_ext _ _)

 theorem afin_hasPushout {A B X : Afin C hC} (i : A ⟶ B) (f : A ⟶ X)
    (hi : cofibrations (Afin C hC) i) : HasPushout i f := by
  let Q : Afin C hC := ⟨pushout i.hom f.hom,
    isFinitelyCellular_of_finiteCellMap X.property (pushout.inr i.hom f.hom)
      ((finiteCellMaps C).of_isPushout (IsPushout.of_hasPushout i.hom f.hom).flip hi)⟩
  let k : B ⟶ Q := ObjectProperty.homMk (pushout.inl i.hom f.hom)
  let j : X ⟶ Q := ObjectProperty.homMk (pushout.inr i.hom f.hom)
  have sq : IsPushout i f k j :=
    IsPushout.of_map_of_faithful (Afin.ι hC) (IsPushout.of_hasPushout i.hom f.hom)
  exact sq.hasPushout

 theorem afin_isCofibrationCategory : IsCofibrationCategory (Afin C hC) where
  isomorphisms_le := by
    intro X Y i hi
    let := hi
    exact finiteCellMaps_isomorphisms C ((Afin.ι hC).map i) inferInstance
  isMultiplicative := inferInstanceAs
    (((finiteCellMaps C).inverseImage (Afin.ι hC)).IsMultiplicative)
  exists_initial := ⟨afinInitial hC, ⟨afinInitial_isInitial hC⟩⟩
  initial_cofibration {I} hI X := by
    obtain ⟨hI'⟩ := Packages.afin_ι_map_initial hC hI
    let e : I.obj ≅ ⊥_ C.Model := hI'.uniqueUpToIso initialIsInitial
    have h := (finiteCellMaps C).comp_mem e.hom (initial.to X.obj)
      (finiteCellMaps_isomorphisms C e.hom inferInstance) X.property
    have he : e.hom ≫ initial.to X.obj = (Afin.ι hC).map (hI.to X) :=
      hI'.hom_ext _ _
    rwa [he] at h
  hasPushout := afin_hasPushout hC
  isStableUnderCobaseChange := ⟨by
    intro A A' B B' f g f' g' sq hf
    exact (finiteCellMaps C).of_isPushout
      (Packages.afin_ι_map_isPushout hC f g g' f' sq.flip hf).flip hf⟩

 theorem afin_weakEquivalence_isomorphisms :
    MorphismProperty.isomorphisms (Afin C hC) ≤ weakEquivalences (Afin C hC) := by
  intro X Y f hf
  let := hf
  exact (Packages.weakEquivalence_closure hC).1 ((Afin.ι hC).map f) inferInstance

 theorem afin_weakEquivalence_multiplicative :
    (weakEquivalences (Afin C hC)).IsMultiplicative := by
  let := (Packages.weakEquivalence_closure hC).2
  exact inferInstanceAs (((W hC).inverseImage (Afin.ι hC)).IsMultiplicative)

 theorem afin_weakEquivalence_twoOutOfSix :
    TwoOutOfSix (Afin C hC) (weakEquivalences (Afin C hC)) := by
  intro X Y Z T f g h hfg hgh
  exact Packages.weakEquivalence_twoOutOfSix hC f.hom g.hom h.hom hfg hgh

 theorem afin_trivialCofibration_retraction {A B : Afin C hC} (i : A ⟶ B)
    (hi : cofibrations (Afin C hC) i) (hwi : weakEquivalences (Afin C hC) i) :
    ∃ r : B ⟶ A, i ≫ r = 𝟙 A := by
  let := Packages.trivialCofibration_lift hC i.hom
    (finiteCellMaps_le_cofibrations C _ hi) hwi
    (finiteCellMaps_le_cofibrations C _ A.property)
    (terminal.from A.obj) (Packages.fibrant hC A.obj)
  have sq : CommSq (𝟙 A.obj) i.hom (terminal.from A.obj) (terminal.from B.obj) :=
    ⟨terminal.hom_ext _ _⟩
  exact ⟨ObjectProperty.homMk sq.lift, by apply ObjectProperty.hom_ext; exact sq.fac_left⟩

end HomotopyHypothesis.Cylinder.FiniteCellCategory
