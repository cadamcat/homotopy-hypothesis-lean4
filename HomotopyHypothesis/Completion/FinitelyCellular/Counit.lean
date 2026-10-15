import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Blueprint.Henry.Completion
import HomotopyHypothesis.Blueprint.Interfaces.DiskFinitelyCellular
import HomotopyHypothesis.Blueprint.Interfaces.Restriction
import HomotopyHypothesis.Completion.FinitelyCellular.Afin
import HomotopyHypothesis.Completion.FinitelyCellular.Basic
import HomotopyHypothesis.Completion.FinitelyCellular.Phi
import HomotopyHypothesis.Completion.FinitelyCellular.Theta
import HomotopyHypothesis.Completion.FinitelyCellular.Unit
/-
# The counit isomorphism for the completion comparison.

For any completion presheaf `P`, the comparison map
`theta P : P ⟶ R(Phi(P))` is an isomorphism.
-/

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open OAI.Grothendieck
open HomotopyHypothesis.Blueprint
open HomotopyHypothesis.Henry

noncomputable section

namespace HomotopyHypothesis.Completion.FinitelyCellular

universe u

variable {C : GlobularTheory.{u}} (hC : C.IsCoherator)

/-- A morphism of cospan pullback cones in Type inducing bijections on the base
    induces a bijection on the cone points. -/
theorem bijective_of_isPullback {D : Type*} [Category D]
    {A B X Q : D} {i : A ⟶ B} {f : A ⟶ X} {k : B ⟶ Q} {j : X ⟶ Q}
    {P R : Dᵒᵖ ⥤ Type u} (η : NatTrans P R)
    (hP : IsPullback (P.map k.op) (P.map j.op) (P.map i.op) (P.map f.op))
    (hR : IsPullback (R.map k.op) (R.map j.op) (R.map i.op) (R.map f.op))
    (hA : Function.Bijective (η.app (op A)))
    (hB : Function.Bijective (η.app (op B)))
    (hX : Function.Bijective (η.app (op X))) :
    Function.Bijective (η.app (op Q)) := by
  have hinj : Function.Injective (η.app (op Q)) := by
    intro q1 q2 h
    have h1 : P.map k.op q1 = P.map k.op q2 := by
      have hk : (R.map k.op) (η.app (op Q) q1) = (R.map k.op) (η.app (op Q) q2) := by
        rw [h]
      have hnat1 : (R.map k.op) (η.app (op Q) q1) = (η.app (op B)) (P.map k.op q1) :=
        ConcreteCategory.congr_hom (η.naturality k.op).symm q1
      have hnat2 : (R.map k.op) (η.app (op Q) q2) = (η.app (op B)) (P.map k.op q2) :=
        ConcreteCategory.congr_hom (η.naturality k.op).symm q2
      have hBeq : (η.app (op B)) (P.map k.op q1) = (η.app (op B)) (P.map k.op q2) :=
        hnat1.symm.trans (hk.trans hnat2)
      exact hB.1 hBeq
    have h2 : P.map j.op q1 = P.map j.op q2 := by
      have hj : (R.map j.op) (η.app (op Q) q1) = (R.map j.op) (η.app (op Q) q2) := by
        rw [h]
      have hnat1 : (R.map j.op) (η.app (op Q) q1) = (η.app (op X)) (P.map j.op q1) :=
        ConcreteCategory.congr_hom (η.naturality j.op).symm q1
      have hnat2 : (R.map j.op) (η.app (op Q) q2) = (η.app (op X)) (P.map j.op q2) :=
        ConcreteCategory.congr_hom (η.naturality j.op).symm q2
      have hXeq : (η.app (op X)) (P.map j.op q1) = (η.app (op X)) (P.map j.op q2) :=
        hnat1.symm.trans (hj.trans hnat2)
      exact hX.1 hXeq
    let EP := PullbackCone.IsLimit.equivPullbackObj hP.isLimit
    have hEP : EP q1 = EP q2 := by
      apply Subtype.ext
      apply Prod.ext
      · have hfst1 := PullbackCone.IsLimit.equivPullbackObj_apply_fst hP.isLimit q1
        have hfst2 := PullbackCone.IsLimit.equivPullbackObj_apply_fst hP.isLimit q2
        show (EP q1).1.1 = (EP q2).1.1
        rw [hfst1, hfst2]
        exact h1
      · have hsnd1 := PullbackCone.IsLimit.equivPullbackObj_apply_snd hP.isLimit q1
        have hsnd2 := PullbackCone.IsLimit.equivPullbackObj_apply_snd hP.isLimit q2
        show (EP q1).1.2 = (EP q2).1.2
        rw [hsnd1, hsnd2]
        exact h2
    exact EP.injective hEP
  have hsurj : Function.Surjective (η.app (op Q)) := by
    intro y
    let yb := R.map k.op y
    let yx := R.map j.op y
    obtain ⟨pb, hpb⟩ := hB.2 yb
    obtain ⟨px, hpx⟩ := hX.2 yx
    have hmid : P.map i.op pb = P.map f.op px := by
      apply hA.1
      have hnat1 : (η.app (op A)) (P.map i.op pb) = (R.map i.op) (η.app (op B) pb) :=
        ConcreteCategory.congr_hom (η.naturality i.op) pb
      have hnat2 : (η.app (op A)) (P.map f.op px) = (R.map f.op) (η.app (op X) px) :=
        ConcreteCategory.congr_hom (η.naturality f.op) px
      have hcomm : (R.map i.op) (η.app (op B) pb) = (R.map f.op) (η.app (op X) px) := by
        rw [hpb, hpx]
        have hw : (R.map k.op ≫ R.map i.op) y = (R.map j.op ≫ R.map f.op) y := by rw [hR.w]
        exact hw
      exact hnat1.trans (hcomm.trans hnat2.symm)
    let EP := PullbackCone.IsLimit.equivPullbackObj hP.isLimit
    let ER := PullbackCone.IsLimit.equivPullbackObj hR.isLimit
    let pair : Types.PullbackObj (P.map i.op) (P.map f.op) := ⟨(pb, px), hmid⟩
    let q := EP.symm pair
    have hqb : P.map k.op q = pb := PullbackCone.IsLimit.equivPullbackObj_symm_apply_fst hP.isLimit pair
    have hqx : P.map j.op q = px := PullbackCone.IsLimit.equivPullbackObj_symm_apply_snd hP.isLimit pair
    refine ⟨q, ?_⟩
    apply ER.injective
    apply Subtype.ext
    apply Prod.ext
    · have hfst1 := PullbackCone.IsLimit.equivPullbackObj_apply_fst hR.isLimit (η.app (op Q) q)
      have hfst2 := PullbackCone.IsLimit.equivPullbackObj_apply_fst hR.isLimit y
      show (ER (η.app (op Q) q)).1.1 = (ER y).1.1
      rw [hfst1, hfst2]
      change (R.map k.op) (η.app (op Q) q) = (R.map k.op) y
      have hnat : (R.map k.op) (η.app (op Q) q) = (η.app (op B)) (P.map k.op q) :=
        ConcreteCategory.congr_hom (η.naturality k.op).symm q
      rw [hnat, hqb, hpb]
    · have hsnd1 := PullbackCone.IsLimit.equivPullbackObj_apply_snd hR.isLimit (η.app (op Q) q)
      have hsnd2 := PullbackCone.IsLimit.equivPullbackObj_apply_snd hR.isLimit y
      show (ER (η.app (op Q) q)).1.2 = (ER y).1.2
      rw [hsnd1, hsnd2]
      change (R.map j.op) (η.app (op Q) q) = (R.map j.op) y
      have hnat : (R.map j.op) (η.app (op Q) q) = (η.app (op X)) (P.map j.op q) :=
        ConcreteCategory.congr_hom (η.naturality j.op).symm q
      rw [hnat, hqx, hpx]
  exact ⟨hinj, hsurj⟩

/-- The comparison map is bijective on representables (free models). -/
theorem theta_freeAfin_bijective (P : Completion.{u} (Afin C hC)) (X : C.Obj) :
    Function.Bijective (thetaMap hC P ((FreeAfin hC).obj X)) := by
  let E : ((Afin.ι hC).obj ((FreeAfin hC).obj X) ⟶ (Phi hC).obj P) ≃
      P.obj.obj (op ((FreeAfin hC).obj X)) :=
    yonedaEquiv (X := X)
  have hE (x : P.obj.obj (op ((FreeAfin hC).obj X))) :
      E (thetaMap hC P ((FreeAfin hC).obj X) x) = x := by
    show (thetaMap hC P ((FreeAfin hC).obj X) x).app (op X) (𝟙 X) = x
    show P.obj.map (elemMap hC ((FreeAfin hC).obj X) (𝟙 X)).op x = x
    have helem : elemMap hC ((FreeAfin hC).obj X) (𝟙 X) = 𝟙 _ := by
      apply ObjectProperty.hom_ext
      show (yonedaEquiv (X := X)).symm (𝟙 X) = 𝟙 (yoneda.obj X)
      have h : yonedaEquiv (X := X) (𝟙 (yoneda.obj X)) = 𝟙 X := rfl
      rw [← h, Equiv.symm_apply_apply]
    rw [helem]
    show P.obj.map (𝟙 (op ((FreeAfin hC).obj X))) x = x
    rw [P.obj.map_id]
    rfl
  refine ⟨?_, ?_⟩
  · intro x1 x2 h
    have h1 := congrArg E h
    rw [hE, hE] at h1
    exact h1
  · intro f
    refine ⟨E f, ?_⟩
    apply E.injective
    rw [hE]

/-- The comparison map is bijective on the initial model. -/
theorem theta_initial_bijective (P : Completion.{u} (Afin C hC)) :
    Function.Bijective (thetaMap hC P ⟨⊥_ C.Model, initial_mem⟩) := by
  let I₀ : Afin C hC := ⟨⊥_ C.Model, initial_mem⟩
  have hI0 : IsInitial I₀ :=
    IsInitial.ofUniqueHom
      (fun X => ObjectProperty.homMk (initial.to X.obj))
      (fun X f => by
        apply ObjectProperty.hom_ext
        exact initialIsInitial.hom_ext _ _)
  obtain ⟨uP⟩ := P.property.1 hI0
  have : Subsingleton (P.obj.obj (op I₀)) := ⟨fun a b => (uP.uniq a).trans (uP.uniq b).symm⟩
  have : Subsingleton ((Afin.ι hC).obj I₀ ⟶ (Phi hC).obj P) := by
    change Subsingleton (⊥_ C.Model ⟶ (Phi hC).obj P)
    infer_instance
  refine ⟨fun x y _ => Subsingleton.elim x y, fun f => ?_⟩
  refine ⟨uP.default, Subsingleton.elim _ _⟩

/-- Bijectivity of theta is invariant under isomorphism in Afin. -/
theorem theta_iso_bijective (P : Completion.{u} (Afin C hC)) {A B : Afin C hC}
    (e : A ≅ B) (hA : Function.Bijective (thetaMap hC P A)) :
    Function.Bijective (thetaMap hC P B) := by
  let R := (Packages.restriction hC).obj ((Phi hC).obj P)
  let η := theta hC P
  have hA' : Function.Bijective (η.app (op A)) := hA
  have hP_comp : P.obj.map e.hom.op ≫ P.obj.map e.inv.op = 𝟙 _ := by
    rw [← P.obj.map_comp, ← op_comp, e.inv_hom_id, op_id, P.obj.map_id]
  have hP_comp' : P.obj.map e.inv.op ≫ P.obj.map e.hom.op = 𝟙 _ := by
    rw [← P.obj.map_comp, ← op_comp, e.hom_inv_id, op_id, P.obj.map_id]
  have hR_comp : R.obj.map e.inv.op ≫ R.obj.map e.hom.op = 𝟙 _ := by
    rw [← R.obj.map_comp, ← op_comp, e.hom_inv_id, op_id, R.obj.map_id]
  have hR_comp' : R.obj.map e.hom.op ≫ R.obj.map e.inv.op = 𝟙 _ := by
    rw [← R.obj.map_comp, ← op_comp, e.inv_hom_id, op_id, R.obj.map_id]
  have hP_bij : Function.Bijective (P.obj.map e.hom.op) := by
    have hl : Function.LeftInverse (P.obj.map e.inv.op) (P.obj.map e.hom.op) :=
      fun x => by show (P.obj.map e.hom.op ≫ P.obj.map e.inv.op) x = x; rw [hP_comp]; rfl
    have hr : Function.RightInverse (P.obj.map e.inv.op) (P.obj.map e.hom.op) :=
      fun x => by show (P.obj.map e.inv.op ≫ P.obj.map e.hom.op) x = x; rw [hP_comp']; rfl
    exact ⟨hl.injective, hr.surjective⟩
  have hR_bij : Function.Bijective (R.obj.map e.inv.op) := by
    have hl : Function.LeftInverse (R.obj.map e.hom.op) (R.obj.map e.inv.op) :=
      fun x => by show (R.obj.map e.inv.op ≫ R.obj.map e.hom.op) x = x; rw [hR_comp]; rfl
    have hr : Function.RightInverse (R.obj.map e.hom.op) (R.obj.map e.inv.op) :=
      fun x => by show (R.obj.map e.hom.op ≫ R.obj.map e.inv.op) x = x; rw [hR_comp']; rfl
    exact ⟨hl.injective, hr.surjective⟩
  have hcomp : η.app (op B) =
      P.obj.map e.hom.op ≫ η.app (op A) ≫ R.obj.map e.inv.op := by
    apply ConcreteCategory.hom_ext
    intro x
    have hnat : (P.obj.map e.hom.op ≫ η.app (op A)) x =
        (η.app (op B) ≫ R.obj.map e.hom.op) x :=
      ConcreteCategory.congr_hom (η.naturality e.hom.op) x
    dsimp at hnat ⊢
    rw [hnat]
    have hinv_app := ConcreteCategory.congr_hom hR_comp' (η.app (op B) x)
    exact hinv_app.symm
  rw [show thetaMap hC P B = η.app (op B) from rfl, hcomp]
  exact hR_bij.comp (hA'.comp hP_bij)

/-- Bijectivity of theta is preserved by pushouts along cofibrations in Afin. -/
theorem theta_pushout_bijective (P : Completion.{u} (Afin C hC))
    {A B X Q : Afin C hC} (i : A ⟶ B) (f : A ⟶ X) (k : B ⟶ Q) (j : X ⟶ Q)
    (hsq : IsPushout i f k j) (hcof : cofibrations (Afin C hC) i)
    (hA : Function.Bijective (thetaMap hC P A))
    (hB : Function.Bijective (thetaMap hC P B))
    (hX : Function.Bijective (thetaMap hC P X)) :
    Function.Bijective (thetaMap hC P Q) := by
  let R := (Packages.restriction hC).obj ((Phi hC).obj P)
  have hP := P.property.2 i f k j hsq hcof
  have hR := R.property.2 i f k j hsq hcof
  have hA' : Function.Bijective ((theta hC P).app (op A)) := hA
  have hB' : Function.Bijective ((theta hC P).app (op B)) := hB
  have hX' : Function.Bijective ((theta hC P).app (op X)) := hX
  have hQ := bijective_of_isPullback (theta hC P) hP hR hA' hB' hX'
  exact hQ

/-- Disks as objects of Afin. -/
def AfinDisk (n : ℕ) : Afin C hC :=
  ⟨GlobularTheory.Model.disk C n, Packages.disk_finitelyCellular C n⟩

/-- AfinDisk is isomorphic to the representable free model. -/
def afinDiskIso (n : ℕ) :
    AfinDisk (C := C) (hC := hC) n ≅ (FreeAfin hC).obj ⟨Shape.globe n⟩ where
  hom := ObjectProperty.homMk (𝟙 _)
  inv := ObjectProperty.homMk (𝟙 _)
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    show 𝟙 (GlobularTheory.Model.disk C n) ≫ 𝟙 _ = 𝟙 _
    exact Category.id_comp _
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    show 𝟙 (GlobularTheory.Model.disk C n) ≫ 𝟙 _ = 𝟙 _
    exact Category.id_comp _

/-- The comparison map is bijective on disks. -/
theorem theta_disk_bijective (P : Completion.{u} (Afin C hC)) (n : ℕ) :
    Function.Bijective (thetaMap hC P (AfinDisk (C := C) (hC := hC) n)) :=
  theta_iso_bijective hC P (afinDiskIso hC n).symm (theta_freeAfin_bijective hC P ⟨Shape.globe n⟩)

/-- Boundary disks as objects of Afin. -/
def AfinBoundaryDisk (n : ℕ) : Afin C hC :=
  ⟨GlobularTheory.Model.boundaryDisk C n, boundaryDisk_mem n⟩

/-- AfinBoundaryDisk 0 is isomorphic to the initial model. -/
def afinBoundaryDisk0Iso :
    AfinBoundaryDisk (C := C) (hC := hC) 0 ≅ ⟨⊥_ C.Model, initial_mem⟩ where
  hom := ObjectProperty.homMk (𝟙 _)
  inv := ObjectProperty.homMk (𝟙 _)
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    show 𝟙 (⊥_ C.Model) ≫ 𝟙 _ = 𝟙 _
    exact Category.id_comp _
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    show 𝟙 (⊥_ C.Model) ≫ 𝟙 _ = 𝟙 _
    exact Category.id_comp _

/-- The comparison map is bijective on boundary disks. -/
theorem theta_boundaryDisk_bijective (P : Completion.{u} (Afin C hC)) (n : ℕ) :
    Function.Bijective (thetaMap hC P (AfinBoundaryDisk (C := C) (hC := hC) n)) := by
  induction n with
  | zero =>
    exact theta_iso_bijective hC P (afinBoundaryDisk0Iso hC).symm (theta_initial_bijective hC P)
  | succ n ih =>
    let i : AfinBoundaryDisk (C := C) (hC := hC) n ⟶ AfinDisk (C := C) (hC := hC) n :=
      ObjectProperty.homMk (GlobularTheory.Model.I C n)
    let k : AfinDisk (C := C) (hC := hC) n ⟶ AfinBoundaryDisk (C := C) (hC := hC) (n + 1) :=
      ObjectProperty.homMk (pushout.inl (GlobularTheory.Model.I C n) (GlobularTheory.Model.I C n))
    let j : AfinDisk (C := C) (hC := hC) n ⟶ AfinBoundaryDisk (C := C) (hC := hC) (n + 1) :=
      ObjectProperty.homMk (pushout.inr (GlobularTheory.Model.I C n) (GlobularTheory.Model.I C n))
    have hsq : IsPushout i i k j := by
      apply isPushout_of_full (F := Afin.ι hC)
      exact IsPushout.of_hasPushout (GlobularTheory.Model.I C n) (GlobularTheory.Model.I C n)
    have hcof : cofibrations (Afin C hC) i := I_mem_finiteCellMaps n
    have hDisk := theta_disk_bijective hC P n
    exact theta_pushout_bijective hC P i i k j hsq hcof ih hDisk hDisk

/-- Bijectivity of theta is preserved by generating pushouts and isomorphisms. -/
theorem theta_of_base (P : Completion.{u} (Afin C hC))
    {X Y : C.Model} (f : X ⟶ Y)
    (hf : ((MorphismProperty.ofHoms (fun n => GlobularTheory.Model.I C n)).pushouts ⊔
           MorphismProperty.isomorphisms C.Model) f)
    {hX : IsFinitelyCellular C X} {hY : IsFinitelyCellular C Y}
    (h_bij : Function.Bijective (thetaMap hC P ⟨X, hX⟩)) :
    Function.Bijective (thetaMap hC P ⟨Y, hY⟩) := by
  let X_afin : Afin C hC := ⟨X, hX⟩
  let Y_afin : Afin C hC := ⟨Y, hY⟩
  cases hf with
  | inl hpush =>
    rcases hpush with ⟨_, _, _, u, g, ⟨n⟩, sq⟩
    let i : AfinBoundaryDisk (C := C) (hC := hC) n ⟶ AfinDisk (C := C) (hC := hC) n :=
      ObjectProperty.homMk (GlobularTheory.Model.I C n)
    let u' : AfinBoundaryDisk (C := C) (hC := hC) n ⟶ X_afin :=
      ObjectProperty.homMk u
    let g' : AfinDisk (C := C) (hC := hC) n ⟶ Y_afin :=
      ObjectProperty.homMk g
    let f' : X_afin ⟶ Y_afin :=
      ObjectProperty.homMk f
    have hsq : IsPushout i u' g' f' := by
      apply isPushout_of_full (F := Afin.ι hC)
      exact sq.flip
    have hcof : cofibrations (Afin C hC) i := I_mem_finiteCellMaps n
    have hA := theta_boundaryDisk_bijective hC P n
    have hB := theta_disk_bijective hC P n
    exact theta_pushout_bijective hC P i u' g' f' hsq hcof hA hB h_bij
  | inr hiso =>
    have : IsIso f := hiso
    let e : X_afin ≅ Y_afin := {
      hom := ObjectProperty.homMk f
      inv := ObjectProperty.homMk (inv f)
      hom_inv_id := by
        apply ObjectProperty.hom_ext
        exact IsIso.hom_inv_id f
      inv_hom_id := by
        apply ObjectProperty.hom_ext
        exact IsIso.inv_hom_id f
    }
    exact theta_iso_bijective hC P e h_bij

/-- Bijectivity of theta is preserved by finite cell maps. -/
theorem theta_of_finiteCellMaps (P : Completion.{u} (Afin C hC))
    {X Y : C.Model} (f : X ⟶ Y) (hf : finiteCellMaps C f) :
    ∀ {hX : IsFinitelyCellular C X} {hY : IsFinitelyCellular C Y},
      Function.Bijective (thetaMap hC P ⟨X, hX⟩) →
      Function.Bijective (thetaMap hC P ⟨Y, hY⟩) := by
  induction hf with
  | of f hf =>
    intro hX hY h_bij
    exact theta_of_base hC P f hf h_bij
  | id X =>
    intro hX hY h_bij
    have : (⟨X, hX⟩ : Afin C hC) = ⟨X, hY⟩ := rfl
    rw [← this]
    exact h_bij
  | comp_of a b ha hb ih =>
    intro hX hY h_bij
    have ihy := ih (hY := by
      show finiteCellMaps C (initial.to _)
      rw [show initial.to _ = initial.to _ ≫ a from initial.hom_ext _ _]
      exact MorphismProperty.comp_mem _ _ _ hX ha) h_bij
    exact theta_of_base hC P b hb ihy

/-- The comparison map `thetaMap` is bijective for every object in Afin. -/
theorem theta_bijective (P : Completion.{u} (Afin C hC)) (A : Afin C hC) :
    Function.Bijective (thetaMap hC P A) := by
  have hInit := theta_initial_bijective hC P
  have hProp : finiteCellMaps C (initial.to A.obj) := A.property
  exact theta_of_finiteCellMaps hC P (initial.to A.obj) hProp hInit

/-- The comparison natural transformation is an isomorphism of presheaves. -/
def thetaPresheafIso (P : Completion.{u} (Afin C hC)) :
    P.obj ≅ ((Packages.restriction hC).obj ((Phi hC).obj P)).obj :=
  NatIso.ofComponents
    (fun A => Equiv.toIso (Equiv.ofBijective _ (theta_bijective hC P A.unop)))
    (fun {_ _} f => (theta hC P).naturality f)

/-- The counit isomorphism at an object of the completion. -/
def counitIso (P : Completion.{u} (Afin C hC)) :
    (Phi hC ⋙ Packages.restriction hC).obj P ≅ P where
  hom := ObjectProperty.homMk (thetaPresheafIso hC P).inv
  inv := ObjectProperty.homMk (thetaPresheafIso hC P).hom
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    exact (thetaPresheafIso hC P).inv_hom_id
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    exact (thetaPresheafIso hC P).hom_inv_id

/-- Naturality of the comparison map theta across objects of the completion. -/
theorem theta_naturality {P Q : Completion.{u} (Afin C hC)} (f : P ⟶ Q) :
    theta hC P ≫ ((Packages.restriction hC).map ((Phi hC).map f)).hom =
      f.hom ≫ theta hC Q := by
  apply NatTrans.ext
  funext A
  obtain ⟨A⟩ := A
  apply ConcreteCategory.hom_ext
  intro x
  show ((thetaMap hC P A x) ≫ (Phi hC).map f : NatTrans _ _) =
    (thetaMap hC Q A (f.hom.app (op A) x) : NatTrans _ _)
  apply NatTrans.ext
  funext X
  obtain ⟨X⟩ := X
  apply ConcreteCategory.hom_ext
  intro z
  show f.hom.app (op ((FreeAfin hC).obj X)) (P.obj.map (elemMap hC A z).op x) =
    Q.obj.map (elemMap hC A z).op (f.hom.app (op A) x)
  have h := ConcreteCategory.congr_hom (f.hom.naturality (elemMap hC A z).op) x
  exact h

/-- The counit natural isomorphism: `Φ ⋙ R ≅ 𝟭 (Completion)`. -/
def counitNatIso :
    Phi hC ⋙ Packages.restriction hC ≅ 𝟭 (Completion.{u} (Afin C hC)) :=
  NatIso.ofComponents (fun P => counitIso hC P) (by
    intro P Q f
    have h_theta := theta_naturality hC f
    have h_theta_comp :
        (counitIso hC P).inv ≫ (Phi hC ⋙ Packages.restriction hC).map f =
          f ≫ (counitIso hC Q).inv := by
      apply ObjectProperty.hom_ext
      exact h_theta
    show (Phi hC ⋙ Packages.restriction hC).map f ≫ (counitIso hC Q).hom =
      (counitIso hC P).hom ≫ (𝟭 _).map f
    have h1 : (Phi hC ⋙ Packages.restriction hC).map f ≫ (counitIso hC Q).hom =
        (counitIso hC P).hom ≫ f := by
      calc
        (Phi hC ⋙ Packages.restriction hC).map f ≫ (counitIso hC Q).hom
        _ = 𝟙 _ ≫ (Phi hC ⋙ Packages.restriction hC).map f ≫ (counitIso hC Q).hom := by rw [Category.id_comp]
        _ = ((counitIso hC P).hom ≫ (counitIso hC P).inv) ≫ (Phi hC ⋙ Packages.restriction hC).map f ≫ (counitIso hC Q).hom := by rw [(counitIso hC P).hom_inv_id]
        _ = (counitIso hC P).hom ≫ ((counitIso hC P).inv ≫ (Phi hC ⋙ Packages.restriction hC).map f) ≫ (counitIso hC Q).hom := by simp only [Category.assoc]
        _ = (counitIso hC P).hom ≫ (f ≫ (counitIso hC Q).inv) ≫ (counitIso hC Q).hom := by rw [h_theta_comp]
        _ = (counitIso hC P).hom ≫ f ≫ ((counitIso hC Q).inv ≫ (counitIso hC Q).hom) := by simp only [Category.assoc]
        _ = (counitIso hC P).hom ≫ f ≫ 𝟙 _ := by rw [(counitIso hC Q).inv_hom_id]
        _ = (counitIso hC P).hom ≫ f := by rw [Category.comp_id]
    exact h1)

end HomotopyHypothesis.Completion.FinitelyCellular
