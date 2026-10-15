import HomotopyHypothesis.Cylinder.SimplicialCategory.Cofibrations
import HomotopyHypothesis.Cylinder.SimplicialCategory.CylinderCategory
import HomotopyHypothesis.Cylinder.SimplicialCategory.FreeAlgKan
import HomotopyHypothesis.Cylinder.SimplicialCategory.HornFiltration
import HomotopyHypothesis.Cylinder.SimplicialCategory.HornRealization
import HomotopyHypothesis.Cylinder.SimplicialCategory.SimplexContractions
import HomotopyHypothesis.Cylinder.SimplicialCategory.SimplexLift
import HomotopyHypothesis.Cylinder.SimplicialCategory.SimplexRealization
import HomotopyHypothesis.Cylinder.SimplicialCategory.SimplexSubfunctors
import HomotopyHypothesis.Blueprint.Henry.Acyclic
import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.Blueprint.Henry.SemiSimplicial
import HomotopyHypothesis.Cylinder.PreCylinderCategory.PreCylinder
import HomotopyHypothesis.Realization.SemisimplicialComparison.CDeltaFacts
import HomotopyHypothesis.Realization.SemisimplicialComparison.CellAttach
import HomotopyHypothesis.Coherator.Comparison.Lifted
import HomotopyHypothesis.Coherator.Comparison.Nerve
import HomotopyHypothesis.Coherator.Comparison.Target
/-!
# `C^Δ` is a cylinder coherator

H Prop 5.2.11 (H:2994–3000). Let `p : X ⥤ Y` be a pre-fibration and isofibration of cylinder
categories, `h : C^Δ ⥤ Y` a morphism of cylinder categories and `x` an object of `X` over the image of
the free point `o`. Every object `A` of `C^Δ` is corepresented along the nerve of the lifted
cosimplicial data by an object `l A` lying strictly over `h A`, with `l o = x`. The corepresenting
objects form a functor `l : C^Δ ⥤ X` with `l ⋙ p = h`; it is a morphism of cylinder categories
because corepresentations turn the cell structure of `C^Δ` into pushouts along cofibrations of `X`,
and the generating weak equivalences between free simplices into the lifted face maps, which are
weak equivalences.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace HomotopyHypothesis.Coherator.Comparison

open HomotopyHypothesis.Henry HomotopyHypothesis.Cylinder.SimplicialCategory

section Functor

variable {X Y : Type (u + 1)} [Category.{u} X] [CategoryWithCofibrations X]
  [CategoryWithWeakEquivalences X] [Category.{u} Y] [CategoryWithCofibrations Y]
  [CategoryWithWeakEquivalences Y]
  (p : X ⥤ Y) (hp : IsLiftingTarget false X Y p)
  (h : CDelta.{u} ⥤ Y) (hh : IsCylinderMorphism h)
  (x₀ : X) (hx₀ : p.obj x₀ = h.obj (stdSimplexCDelta.{u} 0))

set_option hygiene false in
local notation "𝓧" => dataX p hp h hh x₀ hx₀

set_option hygiene false in
local notation "𝓨" => targetData h hh.toIsCofibrationMorphism

set_option hygiene false in
local notation "Θ" => (morphXY p hp h hh x₀ hx₀).mapNerve

/-- `(P, u₀)` corepresents `A` along the lifted nerve, strictly over the corepresentation of `A` by
`h A`. -/
def IsStrict (A : CDelta.{u}) (P : X) (u₀ : A.obj ⟶ (𝓧).nerve.obj P) : Prop :=
  IsCorep (𝓧).nerve A.obj P u₀ ∧
    ∃ e : p.obj P = h.obj A,
      u₀ ≫ (Θ).app P ≫ (𝓨).nerve.map (eqToHom e) = unitY h hh.toIsCofibrationMorphism A

include hp hh in
lemma exists_isStrict (A : CDelta.{u}) : ∃ (P : X) (u₀ : A.obj ⟶ (𝓧).nerve.obj P),
    IsStrict p hp h hh x₀ hx₀ A P u₀ := by
  obtain ⟨P, u₀, h1, e, h2⟩ := exists_strict p hp h hh x₀ hx₀ A
  exact ⟨P, u₀, h1, e, h2⟩

include hp hh in
/-- The free simplices are strictly corepresented by the lifted simplices. -/
lemma isStrict_stdSimplex (n : ℕ) : ∃ u₀ : (stdSimplexCDelta.{u} n).obj ⟶ (𝓧).nerve.obj
    (objX p hp h hh x₀ hx₀ n), IsStrict p hp h hh x₀ hx₀ (stdSimplexCDelta.{u} n) _ u₀ := by
  obtain ⟨u₀, hX, hu⟩ := exists_isCorep_free 𝓧 (hasDimLe_stdSimplex.{u} (le_refl n))
    (stdSimplexRealization (toUpTo (𝓧).D n) n (le_refl n)) (freeAlgKan_isFreeOn _)
  refine ⟨u₀, hX, (morphXY p hp h hh x₀ hx₀).obj_eq (Henry.SemiSimplexCategory.mk n), ?_⟩
  apply free_hom_ext
  intro k x
  have hk : k ≤ n := len_le_of_hom (ULift.down x)
  have e1 := hu k hk x
  have e2 := (morphXY p hp h hh x₀ hx₀).map_eq (ULift.down x)
  change (eqToHom ((morphXY p hp h hh x₀ hx₀).obj_eq _).symm ≫
      p.map ((freeAlgKanUnit _ ≫ u₀.hom).app _ x)) ≫
      eqToHom ((morphXY p hp h hh x₀ hx₀).obj_eq (Henry.SemiSimplexCategory.mk n)) =
    h.map (simplexHat ((freeAlgKanUnit _).app _ x))
  erw [e1, simplexHat_stdUnit]
  change (eqToHom ((morphXY p hp h hh x₀ hx₀).obj_eq _).symm ≫ p.map ((𝓧).D.map (ULift.down x))) ≫
      eqToHom ((morphXY p hp h hh x₀ hx₀).obj_eq (Henry.SemiSimplexCategory.mk n)) = _
  rw [e2]
  simp
  rfl

include hp hh in
/-- Strict corepresentations transport along isomorphisms over `h`. -/
lemma IsStrict.transport {A A' : CDelta.{u}} {P P' : X} {u₀ : A.obj ⟶ (𝓧).nerve.obj P}
    (hs : IsCorep (𝓧).nerve A.obj P u₀) (eP : p.obj P = h.obj A)
    (hc : u₀ ≫ (Θ).app P ≫ (𝓨).nerve.map (eqToHom eP) = unitY h hh.toIsCofibrationMorphism A)
    (φ : A ≅ A') (e : P ≅ P') (eP' : p.obj P' = h.obj A')
    (hpe : p.map e.hom = eqToHom eP ≫ h.map φ.hom ≫ eqToHom eP'.symm) :
    IsStrict p hp h hh x₀ hx₀ A' P' (φ.inv.hom ≫ u₀ ≫ (𝓧).nerve.map e.hom) := by
  refine ⟨(hs.of_iso e).precomp_iso ((ObjectProperty.ι _).mapIso φ.symm), eP', ?_⟩
  have nat := (morphXY p hp h hh x₀ hx₀).mapNerve_naturality e.hom
  have hY := unitY_naturality h hh.toIsCofibrationMorphism φ.hom
  calc (φ.inv.hom ≫ u₀ ≫ (𝓧).nerve.map e.hom) ≫ (Θ).app P' ≫ (𝓨).nerve.map (eqToHom eP')
      = φ.inv.hom ≫ (u₀ ≫ (Θ).app P ≫ (𝓨).nerve.map (eqToHom eP)) ≫
          (𝓨).nerve.map (h.map φ.hom) := by
        simp only [Category.assoc]
        rw [← Category.assoc ((𝓧).nerve.map e.hom), nat, Category.assoc,
          ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, hpe]
        simp
    _ = unitY h hh.toIsCofibrationMorphism A' := by
        rw [hc, hY, ← Category.assoc]
        change ((ObjectProperty.ι _).map (φ.inv ≫ φ.hom)) ≫ _ = _
        rw [Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

variable (o : CDelta.{u}) (x : X) (u_o : o.obj ⟶ (𝓧).nerve.obj x)
  (hs_o : IsStrict p hp h hh x₀ hx₀ o x u_o)

include hp hh hs_o in
lemma exists_isStrict_sel (A : CDelta.{u}) : ∃ (P : X) (u₀ : A.obj ⟶ (𝓧).nerve.obj P),
    IsStrict p hp h hh x₀ hx₀ A P u₀ ∧ (A = o → P = x) := by
  by_cases hA : A = o
  · subst hA
    exact ⟨x, u_o, hs_o, fun _ => rfl⟩
  · obtain ⟨P, u₀, hP⟩ := exists_isStrict p hp h hh x₀ hx₀ A
    exact ⟨P, u₀, hP, fun h' => absurd h' hA⟩

/-- The chosen corepresenting objects. -/
noncomputable def lObj (A : CDelta.{u}) : X :=
  (exists_isStrict_sel p hp h hh x₀ hx₀ o x u_o hs_o A).choose

/-- The chosen corepresentations. -/
noncomputable def lU (A : CDelta.{u}) : A.obj ⟶ (𝓧).nerve.obj (lObj p hp h hh x₀ hx₀ o x u_o hs_o A) :=
  (exists_isStrict_sel p hp h hh x₀ hx₀ o x u_o hs_o A).choose_spec.choose

lemma lU_isStrict (A : CDelta.{u}) :
    IsStrict p hp h hh x₀ hx₀ A (lObj p hp h hh x₀ hx₀ o x u_o hs_o A)
      (lU p hp h hh x₀ hx₀ o x u_o hs_o A) :=
  (exists_isStrict_sel p hp h hh x₀ hx₀ o x u_o hs_o A).choose_spec.choose_spec.1

lemma lObj_o : lObj p hp h hh x₀ hx₀ o x u_o hs_o o = x :=
  (exists_isStrict_sel p hp h hh x₀ hx₀ o x u_o hs_o o).choose_spec.choose_spec.2 rfl

lemma lU_isCorep (A : CDelta.{u}) :
    IsCorep (𝓧).nerve A.obj (lObj p hp h hh x₀ hx₀ o x u_o hs_o A)
      (lU p hp h hh x₀ hx₀ o x u_o hs_o A) :=
  (lU_isStrict p hp h hh x₀ hx₀ o x u_o hs_o A).1

/-- The lift `l : C^Δ ⥤ X`. -/
noncomputable def lFun : CDelta.{u} ⥤ X where
  obj A := lObj p hp h hh x₀ hx₀ o x u_o hs_o A
  map {A B} f := (lU_isCorep p hp h hh x₀ hx₀ o x u_o hs_o A).desc
    (f.hom ≫ lU p hp h hh x₀ hx₀ o x u_o hs_o B)
  map_id A := by
    symm
    apply IsCorep.eq_desc
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  map_comp {A B C} f g := by
    symm
    apply IsCorep.eq_desc
    rw [CategoryTheory.Functor.map_comp, IsCorep.fac_assoc, Category.assoc, IsCorep.fac]
    rfl

lemma lFun_map_spec {A B : CDelta.{u}} (f : A ⟶ B) :
    lU p hp h hh x₀ hx₀ o x u_o hs_o A ≫ (𝓧).nerve.map ((lFun p hp h hh x₀ hx₀ o x u_o hs_o).map f) =
      f.hom ≫ lU p hp h hh x₀ hx₀ o x u_o hs_o B :=
  (lU_isCorep p hp h hh x₀ hx₀ o x u_o hs_o A).fac _

lemma lFun_obj_o : (lFun p hp h hh x₀ hx₀ o x u_o hs_o).obj o = x :=
  lObj_o p hp h hh x₀ hx₀ o x u_o hs_o

include hp hh in
/-- A map between strict corepresentations lies over the image under `h` of the classified map. -/
lemma map_eq_of_isStrict {A B : CDelta.{u}} (f : A ⟶ B) {PA PB : X}
    {uA : A.obj ⟶ (𝓧).nerve.obj PA} {uB : B.obj ⟶ (𝓧).nerve.obj PB}
    (eA : p.obj PA = h.obj A) (eB : p.obj PB = h.obj B)
    (hcA : uA ≫ (Θ).app PA ≫ (𝓨).nerve.map (eqToHom eA) = unitY h hh.toIsCofibrationMorphism A)
    (hcB : uB ≫ (Θ).app PB ≫ (𝓨).nerve.map (eqToHom eB) = unitY h hh.toIsCofibrationMorphism B)
    (g : PA ⟶ PB) (hg : uA ≫ (𝓧).nerve.map g = f.hom ≫ uB) :
    p.map g = eqToHom eA ≫ h.map f ≫ eqToHom eB.symm := by
  have nat := (morphXY p hp h hh x₀ hx₀).mapNerve_naturality g
  have key : eqToHom eA.symm ≫ p.map g ≫ eqToHom eB = h.map f := by
    apply (isCorep_unitY h hh.toIsCofibrationMorphism A).hom_ext
    rw [unitY_naturality, ← hcA, ← hcB]
    simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
    rw [CategoryTheory.Functor.map_comp, ← Category.assoc ((Θ).app PA), ← nat, ← Category.assoc uA,
      ← Category.assoc uA, hg]
    simp only [Category.assoc]
  rw [← key]
  simp

include hp hh in
lemma lFun_comp : lFun p hp h hh x₀ hx₀ o x u_o hs_o ⋙ p = h := by
  have he : ∀ A : CDelta.{u}, p.obj (lObj p hp h hh x₀ hx₀ o x u_o hs_o A) = h.obj A :=
    fun A => (lU_isStrict p hp h hh x₀ hx₀ o x u_o hs_o A).2.choose
  have hc : ∀ A : CDelta.{u}, lU p hp h hh x₀ hx₀ o x u_o hs_o A ≫
      (Θ).app (lObj p hp h hh x₀ hx₀ o x u_o hs_o A) ≫ (𝓨).nerve.map (eqToHom (he A)) =
        unitY h hh.toIsCofibrationMorphism A :=
    fun A => (lU_isStrict p hp h hh x₀ hx₀ o x u_o hs_o A).2.choose_spec
  refine CategoryTheory.Functor.ext he ?_
  intro A B f
  exact map_eq_of_isStrict p hp h hh x₀ hx₀ f (he A) (he B) (hc A) (hc B)
    ((lFun p hp h hh x₀ hx₀ o x u_o hs_o).map f) (lFun_map_spec p hp h hh x₀ hx₀ o x u_o hs_o f)

/-! ### `l` is a morphism of cylinder categories -/

include hp hh in
lemma lFun_cellAttachment {A B : CDelta.{u}} (f : A ⟶ B) (hf : AlgKan.IsCellAttachment f.hom) :
    cofibrations X ((lFun p hp h hh x₀ hx₀ o x u_o hs_o).map f) := by
  have : IsCofibrationCategory X := hp.1.toIsCofibrationCategory
  obtain ⟨P', u', g, hc, hg, hjg, -⟩ :=
    cellStep p hp h hh x₀ hx₀ f.hom hf (lU_isCorep p hp h hh x₀ hx₀ o x u_o hs_o A)
  obtain ⟨e, he⟩ := hc.exists_iso (lU_isCorep p hp h hh x₀ hx₀ o x u_o hs_o B)
  have : (lFun p hp h hh x₀ hx₀ o x u_o hs_o).map f = g ≫ e.hom := by
    apply (lU_isCorep p hp h hh x₀ hx₀ o x u_o hs_o A).hom_ext
    erw [lFun_map_spec, CategoryTheory.Functor.map_comp, ← Category.assoc, ← hjg, Category.assoc, he]
    rfl
  rw [this]
  exact cofibrations_comp _ _ hg (cofibrations_of_isIso e.hom)

include hp hh in
lemma lFun_cofibration_aux {A₁ A₂ : AlgKan.{u}} (φ : A₁ ⟶ A₂) (hφ : AlgKan.cellularMaps φ) :
    ∀ (h₁ : A₁.IsFinitelyCellular) (h₂ : A₂.IsFinitelyCellular),
      cofibrations X ((lFun p hp h hh x₀ hx₀ o x u_o hs_o).map
        (ObjectProperty.homMk φ : (⟨A₁, h₁⟩ : CDelta.{u}) ⟶ ⟨A₂, h₂⟩)) := by
  have : IsCofibrationCategory X := hp.1.toIsCofibrationCategory
  induction hφ with
  | of φ hφ =>
    intro h₁ h₂
    rcases hφ with hφ | hφ
    · exact lFun_cellAttachment p hp h hh x₀ hx₀ o x u_o hs_o _ hφ
    · have : IsIso φ := hφ
      have : IsIso (ObjectProperty.homMk φ : (⟨_, h₁⟩ : CDelta.{u}) ⟶ ⟨_, h₂⟩) :=
        ⟨ObjectProperty.homMk (inv φ), ObjectProperty.hom_ext _ (IsIso.hom_inv_id φ),
          ObjectProperty.hom_ext _ (IsIso.inv_hom_id φ)⟩
      exact cofibrations_of_isIso _
  | id A =>
    intro h₁ _
    have : (ObjectProperty.homMk (𝟙 A) : (⟨A, h₁⟩ : CDelta.{u}) ⟶ ⟨A, h₁⟩) = 𝟙 _ := rfl
    rw [this, CategoryTheory.Functor.map_id]
    exact cofibrations_id _
  | comp_of φ₁ φ₂ hφ₁ hφ₂ ih =>
    intro h₁ h₂
    have hM := isFinitelyCellular_of_cellularMaps hφ₁ h₁
    have : (ObjectProperty.homMk (φ₁ ≫ φ₂) : (⟨_, h₁⟩ : CDelta.{u}) ⟶ ⟨_, h₂⟩) =
        (ObjectProperty.homMk φ₁ : (⟨_, h₁⟩ : CDelta.{u}) ⟶ ⟨_, hM⟩) ≫ ObjectProperty.homMk φ₂ :=
      rfl
    rw [this, CategoryTheory.Functor.map_comp]
    refine cofibrations_comp _ _ (ih h₁ hM) ?_
    rcases hφ₂ with hφ₂ | hφ₂
    · exact lFun_cellAttachment p hp h hh x₀ hx₀ o x u_o hs_o _ hφ₂
    · have : IsIso φ₂ := hφ₂
      have : IsIso (ObjectProperty.homMk φ₂ : (⟨_, hM⟩ : CDelta.{u}) ⟶ ⟨_, h₂⟩) :=
        ⟨ObjectProperty.homMk (inv φ₂), ObjectProperty.hom_ext _ (IsIso.hom_inv_id φ₂),
          ObjectProperty.hom_ext _ (IsIso.inv_hom_id φ₂)⟩
      exact cofibrations_of_isIso _

include hp hh in
lemma lFun_map_cofibration {A B : CDelta.{u}} (f : A ⟶ B) (hf : cofibrations CDelta.{u} f) :
    cofibrations X ((lFun p hp h hh x₀ hx₀ o x u_o hs_o).map f) :=
  lFun_cofibration_aux p hp h hh x₀ hx₀ o x u_o hs_o f.hom hf A.property B.property

include hp hh in
lemma lFun_map_isPushout {A B Z P : CDelta.{u}} (i : A ⟶ B) (f : A ⟶ Z) (k : B ⟶ P) (j : Z ⟶ P)
    (sq : IsPushout i f k j) (hi : cofibrations CDelta.{u} i) :
    IsPushout ((lFun p hp h hh x₀ hx₀ o x u_o hs_o).map i)
      ((lFun p hp h hh x₀ hx₀ o x u_o hs_o).map f)
      ((lFun p hp h hh x₀ hx₀ o x u_o hs_o).map k)
      ((lFun p hp h hh x₀ hx₀ o x u_o hs_o).map j) := by
  have sqA := Realization.SemisimplicialComparison.isPushout_alg_of_isPushout sq hi
  have spec : ∀ {A B : CDelta.{u}} (f : A ⟶ B), lU p hp h hh x₀ hx₀ o x u_o hs_o A ≫
      (𝓧).nerve.map ((lFun p hp h hh x₀ hx₀ o x u_o hs_o).map f) = f.hom ≫ lU p hp h hh x₀ hx₀ o x u_o hs_o B :=
    fun f => lFun_map_spec p hp h hh x₀ hx₀ o x u_o hs_o f
  have cor := lU_isCorep p hp h hh x₀ hx₀ o x u_o hs_o
  refine Realization.SemisimplicialComparison.isPushout_of_universal
    (by rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, sq.w]) fun T b z hbz => ?_
  have hw : i.hom ≫ lU p hp h hh x₀ hx₀ o x u_o hs_o B ≫ (𝓧).nerve.map b =
      f.hom ≫ lU p hp h hh x₀ hx₀ o x u_o hs_o Z ≫ (𝓧).nerve.map z := by
    calc i.hom ≫ lU p hp h hh x₀ hx₀ o x u_o hs_o B ≫ (𝓧).nerve.map b
        = (i.hom ≫ lU p hp h hh x₀ hx₀ o x u_o hs_o B) ≫ (𝓧).nerve.map b :=
          (Category.assoc _ _ _).symm
      _ = lU p hp h hh x₀ hx₀ o x u_o hs_o A ≫
          (𝓧).nerve.map ((lFun p hp h hh x₀ hx₀ o x u_o hs_o).map i ≫ b) := by
          erw [← spec, Category.assoc, CategoryTheory.Functor.map_comp]
          try rfl
      _ = lU p hp h hh x₀ hx₀ o x u_o hs_o A ≫
          (𝓧).nerve.map ((lFun p hp h hh x₀ hx₀ o x u_o hs_o).map f ≫ z) := by
          erw [hbz]
          try rfl
      _ = (f.hom ≫ lU p hp h hh x₀ hx₀ o x u_o hs_o Z) ≫ (𝓧).nerve.map z := by
          erw [← spec, Category.assoc, CategoryTheory.Functor.map_comp]
          try rfl
      _ = f.hom ≫ lU p hp h hh x₀ hx₀ o x u_o hs_o Z ≫ (𝓧).nerve.map z := Category.assoc _ _ _
  let q := sqA.desc _ _ hw
  refine ⟨(cor P).desc q, ⟨(cor B).hom_ext ?_, (cor Z).hom_ext ?_⟩, fun o' ⟨h₁, h₂⟩ => ?_⟩
  · erw [CategoryTheory.Functor.map_comp, ← Category.assoc, spec, Category.assoc, IsCorep.fac]
    exact sqA.inl_desc _ _ hw
  · erw [CategoryTheory.Functor.map_comp, ← Category.assoc, spec, Category.assoc, IsCorep.fac]
    exact sqA.inr_desc _ _ hw
  · apply IsCorep.eq_desc
    apply sqA.hom_ext
    · erw [sqA.inl_desc, ← Category.assoc, ← spec, Category.assoc, ← CategoryTheory.Functor.map_comp, h₁]
    · erw [sqA.inr_desc, ← Category.assoc, ← spec, Category.assoc, ← CategoryTheory.Functor.map_comp, h₂]

include hp hh in
lemma lFun_map_simplexMaps {A B : CDelta.{u}} (f : A ⟶ B) (hf : CDelta.simplexMaps f) :
    weakEquivalences X ((lFun p hp h hh x₀ hx₀ o x u_o hs_o).map f) := by
  have : IsCylinderCategory X := hp.1
  obtain ⟨m, n, σ, ηA, ηB, hA, hB, hcomm⟩ := hf
  obtain ⟨uA, hXA, huA⟩ := exists_isCorep_free 𝓧 (hasDimLe_stdSimplex.{u} (le_refl m))
    (stdSimplexRealization (toUpTo (𝓧).D m) m (le_refl m)) hA
  obtain ⟨uB, hXB, huB⟩ := exists_isCorep_free 𝓧 (hasDimLe_stdSimplex.{u} (le_refl n))
    (stdSimplexRealization (toUpTo (𝓧).D n) n (le_refl n)) hB
  obtain ⟨eA, heA⟩ := hXA.exists_iso (lU_isCorep p hp h hh x₀ hx₀ o x u_o hs_o A)
  obtain ⟨eB, heB⟩ := hXB.exists_iso (lU_isCorep p hp h hh x₀ hx₀ o x u_o hs_o B)
  have hσ : uA ≫ (𝓧).nerve.map ((𝓧).D.map σ) = f.hom ≫ uB := by
    apply Realization.SemisimplicialComparison.isFreeOn_hom_ext hA
    ext Δ y
    have e1 := huA (unop Δ).obj.len (len_le_of_hom (ULift.down y)) y
    have e2 := huB (unop Δ).obj.len (len_le_of_hom (ULift.down y ≫ σ))
      ((SemiSSet.stdSimplex.{u}.map σ).app _ y)
    have e3 := ConcreteCategory.congr_hom (congr_app hcomm Δ) y
    change (ηA ≫ uA.hom).app Δ y ≫ (𝓧).D.map σ = uB.hom.app Δ ((ηA ≫ f.hom.hom).app Δ y)
    rw [e3]
    change (ηA ≫ uA.hom).app Δ y ≫ (𝓧).D.map σ = (ηB ≫ uB.hom).app Δ
      ((SemiSSet.stdSimplex.{u}.map σ).app Δ y)
    erw [e1, e2]
    exact ((𝓧).D.map_comp _ _).symm
  have key : (lFun p hp h hh x₀ hx₀ o x u_o hs_o).map f = eA.inv ≫ (𝓧).D.map σ ≫ eB.hom := by
    apply (lU_isCorep p hp h hh x₀ hx₀ o x u_o hs_o A).hom_ext
    erw [lFun_map_spec, ← heA, ← heB, Category.assoc, ← CategoryTheory.Functor.map_comp,
      Iso.hom_inv_id_assoc, CategoryTheory.Functor.map_comp, ← Category.assoc uA, hσ, Category.assoc]
    try rfl
  rw [key]
  refine weakEquivalences_comp _ _ (weakEquivalences_of_isIso eA.inv)
    (weakEquivalences_comp _ _ ?_ (weakEquivalences_of_isIso eB.hom))
  change weakEquivalences X (eqToHom (objEq p hp h hh x₀ hx₀ (len_le_of_hom σ)).symm ≫ _)
  exact weakEquivalences_comp _ _
    (weakEquivalences_of_isIso (eqToHom (objEq p hp h hh x₀ hx₀ (len_le_of_hom σ)).symm))
    ((liftedCosimplicialUpTo p hp h hh x₀ hx₀ n).map_weq hp _ _ σ)

include hp hh in
lemma lFun_map_weakEquivalence {A B : CDelta.{u}} (f : A ⟶ B) (hf : weakEquivalences CDelta.{u} f) :
    weakEquivalences X ((lFun p hp h hh x₀ hx₀ o x u_o hs_o).map f) := by
  have : IsCylinderCategory X := hp.1
  have hpre : IsPreCylinderCategory X := Cylinder.PreCylinderCategory.isPreCylinderCategory_proof
  let l := lFun p hp h hh x₀ hx₀ o x u_o hs_o
  let W' : MorphismProperty CDelta.{u} := fun _ _ g => weakEquivalences X (l.map g)
  have hW' : IsWeakEquivalenceClass CDelta.{u} (cofibrations CDelta.{u}) W' := by
    refine ⟨fun _ _ g hg => ?_, ?_, ?_, ?_⟩
    · have : IsIso g := hg
      exact weakEquivalences_of_isIso (l.map g)
    · exact
        { id_mem := fun A => by
            change weakEquivalences X (l.map (𝟙 A))
            rw [CategoryTheory.Functor.map_id]
            exact weakEquivalences_id _
          comp_mem := fun g₁ g₂ h₁ h₂ => by
            change weakEquivalences X (l.map (g₁ ≫ g₂))
            rw [CategoryTheory.Functor.map_comp]
            exact weakEquivalences_comp _ _ h₁ h₂ }
    · intro _ _ _ _ g₁ g₂ g₃ h₁₂ h₂₃
      change weakEquivalences X (l.map (g₁ ≫ g₂)) at h₁₂
      change weakEquivalences X (l.map (g₂ ≫ g₃)) at h₂₃
      rw [CategoryTheory.Functor.map_comp] at h₁₂ h₂₃
      obtain ⟨r₁, r₂, r₃, r₄⟩ := IsCylinderCategory.twoOutOfSix _ _ _ h₁₂ h₂₃
      refine ⟨r₁, r₂, r₃, ?_⟩
      change weakEquivalences X (l.map (g₁ ≫ g₂ ≫ g₃))
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
      exact r₄
    · intro A B Z P A' B' Z' P' i g k j i' g' k' j' vA vB vZ φ sq sq' hi hi' hA hB hZ c₁ c₂ c₃ c₄
      exact hpre.gluing (l.map i) (l.map g) (l.map k) (l.map j) (l.map i') (l.map g') (l.map k')
        (l.map j') (l.map vA) (l.map vB) (l.map vZ) (l.map φ)
        (lFun_map_isPushout p hp h hh x₀ hx₀ o x u_o hs_o i g k j sq hi)
        (lFun_map_isPushout p hp h hh x₀ hx₀ o x u_o hs_o i' g' k' j' sq' hi')
        (lFun_map_cofibration p hp h hh x₀ hx₀ o x u_o hs_o i hi)
        (lFun_map_cofibration p hp h hh x₀ hx₀ o x u_o hs_o i' hi') hA hB hZ
        (by rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, c₁])
        (by rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, c₂])
        (by rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, c₃])
        (by rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, c₄])
  have hle : weakEquivalences CDelta.{u} ≤ W' :=
    sInf_le ⟨hW', fun _ _ g hg => lFun_map_simplexMaps p hp h hh x₀ hx₀ o x u_o hs_o g hg⟩
  exact hle _ hf

include hp hh in
theorem lFun_isCylinderMorphism : IsCylinderMorphism (lFun p hp h hh x₀ hx₀ o x u_o hs_o) where
  map_cofibration _ _ f hf := lFun_map_cofibration p hp h hh x₀ hx₀ o x u_o hs_o f hf
  map_initial I hI := ⟨(lU_isCorep p hp h hh x₀ hx₀ o x u_o hs_o I).isInitial
    (Realization.SemisimplicialComparison.isInitial_obj_of_isInitial hI)⟩
  map_isPushout _ _ _ _ i f k j sq hi := lFun_map_isPushout p hp h hh x₀ hx₀ o x u_o hs_o i f k j sq hi
  map_weakEquivalence _ _ f hf := lFun_map_weakEquivalence p hp h hh x₀ hx₀ o x u_o hs_o f hf

end Functor

/-! ### The cylinder coherator -/

/-- The free point is isomorphic in `C^Δ` to any object free on `Δ₀`. -/
noncomputable def freePointIso (o : CDelta.{u})
    {η : SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk 0) ⟶ o.obj.X}
    (hη : o.obj.IsFreeOn η) : stdSimplexCDelta.{u} 0 ≅ o where
  hom := ObjectProperty.homMk (Realization.SemisimplicialComparison.isoOfIsFreeOn (freeAlgKan_isFreeOn _) hη).hom
  inv := ObjectProperty.homMk (Realization.SemisimplicialComparison.isoOfIsFreeOn (freeAlgKan_isFreeOn _) hη).inv
  hom_inv_id := ObjectProperty.hom_ext _ (Realization.SemisimplicialComparison.isoOfIsFreeOn (freeAlgKan_isFreeOn _) hη).hom_inv_id
  inv_hom_id := ObjectProperty.hom_ext _ (Realization.SemisimplicialComparison.isoOfIsFreeOn (freeAlgKan_isFreeOn _) hη).inv_hom_id

/-- **H Prop 5.2.11**: `C^Δ` is a cylinder coherator at the free point. -/
theorem _root_.HomotopyHypothesis.Henry.Packages.cDelta_isCylinderCoherator_proof (o : CDelta.{u})
    (η : SemiSSet.stdSimplex.obj (Henry.SemiSimplexCategory.mk 0) ⟶ o.obj.X)
    (hη : o.obj.IsFreeOn η) :
    IsCylinderCoherator.{u + 1, u} CDelta.{u} o := by
  refine ⟨Henry.Packages.cDelta_isCylinderCategory_proof, ?_⟩
  intro X _ _ _ Y _ _ _ p hp x _ h hh hx
  let φ := freePointIso o hη
  obtain ⟨x₀, e₀, hx₀, he₀⟩ := hp.2.2.2.2.1 x (h.obj (stdSimplexCDelta.{u} 0))
    (eqToIso hx.symm ≪≫ h.mapIso φ.symm)
  obtain ⟨u₀, hcor, e0, hc0⟩ := isStrict_stdSimplex p hp h hh x₀ hx₀ 0
  have hz : objX p hp h hh x₀ hx₀ 0 = x₀ :=
    (liftedCosimplicialUpTo p hp h hh x₀ hx₀ 0).obj_zero
  let e : objX p hp h hh x₀ hx₀ 0 ≅ x := eqToIso hz ≪≫ e₀.symm
  have hinv : p.map e₀.inv = eqToHom hx₀ ≫ h.map φ.hom ≫ eqToHom hx := by
    rw [← cancel_mono (p.map e₀.hom), ← p.map_comp, e₀.inv_hom_id, p.map_id, he₀]
    simp
  have hpe : p.map e.hom = eqToHom e0 ≫ h.map φ.hom ≫ eqToHom hx.symm.symm := by
    change p.map (eqToHom hz ≫ e₀.inv) = _
    rw [p.map_comp, hinv, eqToHom_map]
    simp
  have hs_o := IsStrict.transport p hp h hh x₀ hx₀ hcor e0 hc0 φ e hx.symm hpe
  exact ⟨lFun p hp h hh x₀ hx₀ o x _ hs_o,
    lFun_isCylinderMorphism p hp h hh x₀ hx₀ o x _ hs_o,
    lFun_comp p hp h hh x₀ hx₀ o x _ hs_o,
    lFun_obj_o p hp h hh x₀ hx₀ o x _ hs_o⟩

end HomotopyHypothesis.Coherator.Comparison
