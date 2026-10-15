import HomotopyHypothesis.Blueprint.Defs
import HomotopyHypothesis.Challenge
import HomotopyHypothesis.Realization.Disk.DiskExtend
import HomotopyHypothesis.Realization.Disk.PushoutContract
/-!
# Existence of topological realizations (scaffold)

Ara's Proposition `coh_weak_init`: a coherator maps to any contractible
globular extension. Here the target is spaces with the standard globes:
topological globular sums are contractible, so every admissible pair extends,
and a realization is built along the cellular presentation via
`CellularPresentation.lift`.
-/

open CategoryTheory CategoryTheory.Limits Opposite OAI.Grothendieck
open HomotopyHypothesis.Blueprint
open HomotopyHypothesis.Realization.Disk

namespace HomotopyHypothesis.Realization.Functor

universe u

/-! ## Shape realization -/

noncomputable abbrev shapeLan : (Globeᵒᵖ ⥤ Type u) ⥤ TopCat.{u} :=
  (CategoryTheory.uliftYoneda.{u} (C := Globe)).leftKanExtension oaiTopGlobes.{u}

noncomputable abbrev shapeNerve : TopCat.{u} ⥤ (Globeᵒᵖ ⥤ Type u) :=
  CategoryTheory.Presheaf.restrictedULiftYoneda.{u} oaiTopGlobes.{u}

noncomputable def shapeAdj : shapeLan.{u} ⊣ shapeNerve.{u} :=
  CategoryTheory.Presheaf.uliftYonedaAdjunction.{u, 0, u, 0, u + 1}
    (C := Globe) (ℰ := TopCat.{u}) (A := oaiTopGlobes.{u})
    (((CategoryTheory.uliftYoneda.{u} (C := Globe)).leftKanExtension oaiTopGlobes.{u}))
    ((((CategoryTheory.uliftYoneda.{u} (C := Globe)).leftKanExtensionUnit oaiTopGlobes.{u})))

noncomputable instance : Functor.IsLeftAdjoint (shapeLan.{u}) where
  exists_rightAdjoint := ⟨_, ⟨shapeAdj⟩⟩

/-- Collapse a doubled ULift. -/
def uliftCollapse (α : Type 0) : ULift.{u, 0} (ULift.{0, 0} α) ≃ ULift.{u, 0} α where
  toFun x := ULift.up (ULift.down (ULift.down x))
  invFun y := ULift.up (ULift.up (ULift.down y))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Lifted globes agree with Yoneda globes. -/
noncomputable abbrev liftedGlobeIso (n : ℕ) :
    (Shape.liftedRealization.{u}).obj (Shape.globe n) ≅
      (CategoryTheory.uliftYoneda.{u} (C := Globe)).obj (Globe.mk n) :=
  NatIso.ofComponents (fun Y => (uliftCollapse (Y.unop ⟶ Globe.mk n)).toIso) (fun f => by
    ext x
    rfl)

/-- The unit iso: Kan extension extends the globes. -/
noncomputable abbrev lanUnitIso :
    (CategoryTheory.uliftYoneda.{u} (C := Globe)) ⋙ shapeLan.{u} ≅ oaiTopGlobes.{u} :=
  CategoryTheory.Presheaf.isExtensionAlongULiftYoneda.{u, 0, u, 0, u + 1} oaiTopGlobes.{u}

noncomputable abbrev shapeReal (S : Shape) : TopCat.{u} :=
  (shapeLan.{u}).obj ((Shape.liftedRealization.{u}).obj S)

noncomputable abbrev shapeRealMap {S T : Shape} (f : S ⟶ T) :
    (shapeReal.{u} S) ⟶ (shapeReal.{u} T) :=
  (shapeLan.{u}).map ((Shape.liftedRealization.{u}).map f)

theorem shapeRealMap_id (S : Shape) : shapeRealMap.{u} (𝟙 S) = 𝟙 (shapeReal.{u} S) := by
  simp [shapeRealMap]

theorem shapeRealMap_comp {R S T : Shape} (f : R ⟶ S) (g : S ⟶ T) :
    shapeRealMap.{u} (f ≫ g) = shapeRealMap.{u} f ≫ shapeRealMap.{u} g := by
  simp [shapeRealMap]

theorem shapeReal_pushout (S : Shape) (b h : ℕ) (hl : b < S.1) (hr : b < h) :
    IsPushout (shapeRealMap.{u} (S.seam hl)) (shapeRealMap.{u} (Shape.face hr false))
      (shapeRealMap.{u} (S.inl b h hl hr)) (shapeRealMap.{u} (S.inr b h hl hr)) := by
  have h0 : IsPushout ((Shape.liftedRealization.{u}).map (S.seam hl))
      ((Shape.liftedRealization.{u}).map (Shape.face hr false))
      ((Shape.liftedRealization.{u}).map (S.inl b h hl hr))
      ((Shape.liftedRealization.{u}).map (S.inr b h hl hr)) :=
    Shape.liftedRealization_pushout S b h hl hr
  exact h0.map (shapeLan.{u})

noncomputable abbrev globeRealIso (n : ℕ) :
    (shapeReal.{u} (Shape.globe n)) ≅ TopCat.disk.{u} n :=
  (shapeLan.{u}).mapIso (liftedGlobeIso.{u} n) ≪≫ lanUnitIso.app (Globe.mk n)

/-- Naturality of the lifted globe iso (general form). -/
theorem liftedGlobeIso_nat {X Y : Globe} (f : X ⟶ Y) :
    (Shape.liftedRealization.{u}).map (GlobularTheory.shapeGlobes.map f) ≫
      (liftedGlobeIso.{u} Y.dim).hom =
      (liftedGlobeIso.{u} X.dim).hom ≫
        (CategoryTheory.uliftYoneda.{u} (C := Globe)).map f := by
  ext Z x
  rfl

/-- Unfolding of `globeRealIso.hom`. -/
theorem globeRealIso_hom_eq (n : ℕ) : (globeRealIso.{u} n).hom =
    (shapeLan.{u}).map (liftedGlobeIso.{u} n).hom ≫ (lanUnitIso.app _).hom := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The globe identification intertwines shape maps with the standard globe maps. -/
theorem globeRealIso_naturality {X Y : Globe} (f : X ⟶ Y) :
    shapeRealMap.{u} (GlobularTheory.shapeGlobes.map f) ≫ (globeRealIso.{u} Y.dim).hom =
      (globeRealIso.{u} X.dim).hom ≫ oaiTopGlobes.{u}.map f := by
  cases X with
  | mk m =>
    cases Y with
    | mk n =>
      simp only [globeRealIso_hom_eq, shapeRealMap]
      have hunit :
          (shapeLan.{u}).map ((CategoryTheory.uliftYoneda.{u} (C := Globe)).map f) ≫
              (lanUnitIso.app (Globe.mk n)).hom =
            (lanUnitIso.app (Globe.mk m)).hom ≫ oaiTopGlobes.{u}.map f := by
        simpa [Functor.comp_map] using lanUnitIso.{u}.hom.naturality f
      -- `≫` associates to the right, so the two Kan-extension maps meet `map_comp_assoc`.
      simp only [← Functor.map_comp_assoc]
      simp only [liftedGlobeIso_nat]
      simp only [Functor.map_comp_assoc]
      simp only [hunit, Category.assoc]

/-- The carrier of a realized globe, as a closed disk. -/
noncomputable def globeToBall (n : ℕ) :
    (shapeReal.{u} (Shape.globe n) : Type u) ≃ₜ Ball n :=
  (TopCat.homeoOfIso (globeRealIso.{u} n)).trans Homeomorph.ulift

theorem globeToBall_apply (n : ℕ) (x : shapeReal.{u} (Shape.globe n)) :
    globeToBall.{u} n x = ULift.down ((globeRealIso.{u} n).hom x) :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Faces commute with the identification of realized globes and disks. -/
theorem globeToBall_face {b h : ℕ} (hr : b < h) (side : Bool) :
    (toC (globeToBall.{u} h)).comp (shapeRealMap.{u} (Shape.face hr side)).hom =
      (ballFace hr side).comp (toC (globeToBall.{u} b)) := by
  apply ContinuousMap.ext
  intro x
  have hnat := globeRealIso_naturality.{u} (Globe.face hr side)
  have hface :
      shapeRealMap.{u} (Shape.face hr side) =
        shapeRealMap.{u} (GlobularTheory.shapeGlobes.map (Globe.face hr side)) :=
    rfl
  rw [← hface] at hnat
  have happ :
      ULift.down ((globeRealIso.{u} h).hom ((shapeRealMap.{u} (Shape.face hr side)) x)) =
        ULift.down ((oaiTopGlobes.{u}.map (Globe.face hr side))
          ((globeRealIso.{u} b).hom x)) :=
    congrArg ULift.down (ConcreteCategory.congr_hom hnat x)
  have hball :
      ULift.down ((oaiTopGlobes.{u}.map (Globe.face hr side)) ((globeRealIso.{u} b).hom x)) =
        ballFace hr side (ULift.down ((globeRealIso.{u} b).hom x)) :=
    rfl
  change globeToBall.{u} h ((shapeRealMap.{u} (Shape.face hr side)).hom x) =
    ballFace hr side (globeToBall.{u} b x)
  rw [globeToBall_apply, globeToBall_apply, happ, hball]

/-! ## The globular theory of spaces -/

noncomputable abbrev topTheoryData : TheoryData.{u} where
  Hom S T := ((shapeReal.{u} S) ⟶ (shapeReal.{u} T))
  id _ := 𝟙 _
  comp f g := f ≫ g
  id_comp _ := Category.id_comp _
  comp_id _ := Category.comp_id _
  assoc _ _ _ := Category.assoc _ _ _
  base f := shapeRealMap.{u} f
  base_id _ := shapeRealMap_id.{u} _
  base_comp f g := shapeRealMap_comp.{u} f g

/-- View an E_Top hom as a TopCat map (identity, by definition). -/
noncomputable def viewHom {A B : topTheoryData.Obj} (f : A ⟶ B) :
    shapeReal.{u} A.shape ⟶ shapeReal.{u} B.shape := f

/-- Restriction, generally: a Top pushout of viewed maps is an E_Top pushout. -/
theorem topTheory_pushout_of_top' {Z X Y P : topTheoryData.Obj}
    {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
    (hTop : IsPushout (viewHom.{u} f) (viewHom.{u} g) (viewHom.{u} inl) (viewHom.{u} inr)) :
    IsPushout f g inl inr := by
  have hcol := hTop.isColimit
  refine IsPushout.of_isColimit (c := PushoutCocone.mk inl inr ?_)
    (PushoutCocone.IsColimit.mk _ (fun s => ?_) ?_ ?_ ?_)
  · exact hTop.w
  · exact hcol.desc (PushoutCocone.mk (viewHom.{u} s.inl) (viewHom.{u} s.inr)
      (by exact s.condition))
  · intro s
    show _ ≫ _ = _
    exact hcol.fac _ WalkingSpan.left
  · intro s
    show _ ≫ _ = _
    exact hcol.fac _ WalkingSpan.right
  · intro s m h1 h2
    let sTop : Cocone (span (viewHom.{u} f) (viewHom.{u} g)) :=
      PushoutCocone.mk (viewHom.{u} s.inl) (viewHom.{u} s.inr) (by exact s.condition)
    have hTop : viewHom.{u} m = hcol.desc sTop := by
      refine hcol.uniq sTop _ ?_
      have h1' : viewHom.{u} inl ≫ viewHom.{u} m = viewHom.{u} s.inl := h1
      have h2' : viewHom.{u} inr ≫ viewHom.{u} m = viewHom.{u} s.inr := h2
      intro j
      cases j with
      | none =>
        show (viewHom.{u} f ≫ viewHom.{u} inl) ≫ viewHom.{u} m = _
        rw [Category.assoc, h1']
        show viewHom.{u} f ≫ viewHom.{u} s.inl = viewHom.{u} f ≫ viewHom.{u} s.inl
        rfl
      | some w =>
        cases w with
        | left =>
          show viewHom.{u} inl ≫ viewHom.{u} m = _
          exact h1'
        | right =>
          show viewHom.{u} inr ≫ viewHom.{u} m = _
          exact h2'
    exact hTop

theorem topTheory_pushout_of_top (S : Shape) (b h : ℕ) (hl : b < S.1) (hr : b < h)
    (hTop : IsPushout (shapeRealMap.{u} (S.seam hl))
      (shapeRealMap.{u} (Shape.face hr false))
      (shapeRealMap.{u} (S.inl b h hl hr)) (shapeRealMap.{u} (S.inr b h hl hr))) :
    IsPushout (topTheoryData.{u}.arity.map (S.seam hl))
      (topTheoryData.{u}.arity.map (Shape.face hr false))
      (topTheoryData.{u}.arity.map (S.inl b h hl hr))
      (topTheoryData.{u}.arity.map (S.inr b h hl hr)) :=
  topTheory_pushout_of_top' hTop

noncomputable def topTheory : GlobularTheory.{u} where
  toTheoryData := topTheoryData
  sums S b h hl hr :=
    topTheory_pushout_of_top.{u} S b h hl hr (shapeReal_pushout.{u} S b h hl hr)

/-! ## The terminal theory -/

/-- The terminal globular theory (unique homs). -/
noncomputable abbrev termTheoryData : TheoryData.{u} where
  Hom _ _ := ULift.{u, 0} Unit
  id _ := ULift.up ()
  comp _ _ := ULift.up ()
  id_comp _ := Subsingleton.elim _ _
  comp_id _ := Subsingleton.elim _ _
  assoc _ _ _ := Subsingleton.elim _ _
  base _ := ULift.up ()
  base_id _ := Subsingleton.elim _ _
  base_comp _ _ := Subsingleton.elim _ _

/-- The terminal theory: every square is a pushout. -/
instance termSubsingleton (X Y : termTheoryData.Obj) : Subsingleton (X ⟶ Y) := by
  show Subsingleton (termTheoryData.Hom X.shape Y.shape)
  infer_instance

noncomputable abbrev termTheory : GlobularTheory.{u} where
  toTheoryData := termTheoryData
  sums S b h hl hr := by
    refine IsPushout.of_isColimit (c := PushoutCocone.mk
      (termTheoryData.arity.map (S.inl b h hl hr))
      (termTheoryData.arity.map (S.inr b h hl hr)) (Subsingleton.elim _ _))
      (PushoutCocone.IsColimit.mk _ (fun _ => ULift.up ()) ?_ ?_ ?_)
    · intro s
      exact Subsingleton.elim _ _
    · intro s
      exact Subsingleton.elim _ _
    · intro s m _ _
      exact Subsingleton.elim _ _

variable {C : GlobularTheory.{u}} (hC : C.IsCoherator)

/-! ## Morphisms and the lift -/

/-- The unique morphism to the terminal theory. -/
noncomputable def toTerm (C : GlobularTheory.{u}) :
    GlobularTheory.Morphism C termTheory where
  map _ := ULift.up ()
  map_id _ := rfl
  map_comp _ _ := rfl
  map_base _ := rfl

/-- The projection from spaces to the terminal theory. -/
noncomputable def topToTerm :
    GlobularTheory.Morphism topTheory termTheory where
  map _ := ULift.up ()
  map_id _ := rfl
  map_comp _ _ := rfl
  map_base _ := rfl

/-! ## Topology core (obligations) -/

/-- Every standard disk is contractible. -/
theorem diskContractible (n : ℕ) : ContractibleSpace (TopCat.disk.{u} n) := by
  have hconv : Convex ℝ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    convex_closedBall _ _
  have hmem : (0 : EuclideanSpace ℝ (Fin n)) ∈ Metric.closedBall 0 1 := by
    rw [Metric.mem_closedBall, dist_self]
    norm_num
  have hc : ContractibleSpace (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    hconv.contractibleSpace ⟨_, hmem⟩
  have hu : ContractibleSpace
      (ULift.{u, 0} (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) :=
    @Homeomorph.contractibleSpace _ _ _ _ hc Homeomorph.ulift
  exact hu

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pushout step: attaching a disk preserves contractibility. -/
theorem pushout_contractible_step (S : Shape) (b h : ℕ) (hl : b < S.1) (hr : b < h)
    (hS : ContractibleSpace (shapeReal.{u} S)) :
    ContractibleSpace (shapeReal.{u} (S.attach b h hl hr)) := by
  let A : Type u := shapeReal.{u} (Shape.globe b)
  let X : Type u := shapeReal.{u} S
  let D : Type u := shapeReal.{u} (Shape.globe h)
  let i' : C(A, D) := (shapeRealMap.{u} (Shape.face hr false)).hom
  let f : C(A, X) := (shapeRealMap.{u} (S.seam hl)).hom
  let eA : Ball b ≃ₜ A := (globeToBall.{u} b).symm
  let eD : Ball h ≃ₜ D := (globeToBall.{u} h).symm
  have hsq : (toC eD).comp (ballFace hr false) = i'.comp (toC eA) := by
    apply ContinuousMap.ext
    intro y
    show eD (ballFace hr false y) = i' (eA y)
    apply (globeToBall.{u} h).injective
    rw [(globeToBall.{u} h).apply_symm_apply (ballFace hr false y)]
    have hpt := DFunLike.congr_fun (globeToBall_face.{u} hr false) (eA y)
    rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply] at hpt
    have htoH : (toC (globeToBall.{u} h))
          ((shapeRealMap.{u} (Shape.face hr false)).hom (eA y)) =
        globeToBall.{u} h (i' (eA y)) := rfl
    have htoB : (toC (globeToBall.{u} b)) (eA y) = globeToBall.{u} b (eA y) := rfl
    rw [htoH, htoB] at hpt
    rw [(globeToBall.{u} b).apply_symm_apply y] at hpt
    exact hpt.symm
  let s : StrongDeformation i' := (ballFaceSDR hr).transport eA eD i' hsq
  have hcontract : ContractibleSpace X := hS
  have hP : IsPushout (TopCat.ofHom f) (TopCat.ofHom i')
      (shapeRealMap.{u} (S.inl b h hl hr)) (shapeRealMap.{u} (S.inr b h hl hr)) :=
    shapeReal_pushout.{u} S b h hl hr
  exact contractible_pushout f s hP

/-- Every topological globular sum is contractible. -/
theorem contractible_shapeReal (S : Shape) :
    ContractibleSpace (shapeReal.{u} S) := by
  suffices key : ∀ (n : ℕ) (T : Table n), ContractibleSpace (shapeReal.{u} ⟨n, T⟩) by
    obtain ⟨n, T⟩ := S
    exact key n T
  intro n T
  induction T with
  | globe k =>
    exact @Homeomorph.contractibleSpace _ _ _ _ (diskContractible.{u} k)
      (TopCat.homeoOfIso (globeRealIso.{u} k))
  | attach T b h hl hr ih =>
    exact pushout_contractible_step.{u} ⟨_, T⟩ b h hl hr ih

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A hemisphere point, read in the realized globe, is the face of its projection. -/
lemma globeToBall_symm_ballFace {b h : ℕ} (hr : b < h) (side : Bool) (y : Ball b) :
    (globeToBall.{u} h).symm (ballFace hr side y) =
      (shapeRealMap.{u} (Shape.face hr side)) ((globeToBall.{u} b).symm y) := by
  apply (globeToBall.{u} h).injective
  rw [(globeToBall.{u} h).apply_symm_apply (ballFace hr side y)]
  have hpt := DFunLike.congr_fun (globeToBall_face.{u} hr side)
    ((globeToBall.{u} b).symm y)
  rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply] at hpt
  have htoH : (toC (globeToBall.{u} h))
        ((shapeRealMap.{u} (Shape.face hr side)).hom ((globeToBall.{u} b).symm y)) =
      globeToBall.{u} h
        ((shapeRealMap.{u} (Shape.face hr side)) ((globeToBall.{u} b).symm y)) := rfl
  have htoB : (toC (globeToBall.{u} b)) ((globeToBall.{u} b).symm y) =
      globeToBall.{u} b ((globeToBall.{u} b).symm y) := rfl
  rw [htoH, htoB, (globeToBall.{u} b).apply_symm_apply y] at hpt
  exact hpt.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Transport of a realized map across a face, evaluated on the lower disk. -/
lemma diskOf_ballFace {S : Shape} {b h : ℕ} (hr : b < h) (side : Bool)
    (φ : shapeReal.{u} (Shape.globe h) ⟶ shapeReal.{u} S) (y : Ball b) :
    (φ.hom.comp (toC (globeToBall.{u} h).symm)) (ballFace hr side y) =
      ((shapeRealMap.{u} (Shape.face hr side) ≫ φ).hom.comp
        (toC (globeToBall.{u} b).symm)) y := by
  rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply]
  have hto1 : (toC (globeToBall.{u} h).symm) (ballFace hr side y) =
      (globeToBall.{u} h).symm (ballFace hr side y) := rfl
  have hto2 : (toC (globeToBall.{u} b).symm) y = (globeToBall.{u} b).symm y := rfl
  rw [hto1, hto2, globeToBall_symm_ballFace hr side y]
  have hhom : φ.hom ((shapeRealMap.{u} (Shape.face hr side)) ((globeToBall.{u} b).symm y)) =
      φ ((shapeRealMap.{u} (Shape.face hr side)) ((globeToBall.{u} b).symm y)) := rfl
  rw [hhom]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Parallel realized maps, read on disks, agree on the boundary sphere. -/
lemma diskMaps_agree {S : Shape} {n : ℕ}
    (src tgt : shapeReal.{u} (Shape.globe n) ⟶ shapeReal.{u} S)
    (hp : topTheory.Parallel n src tgt)
    (y : Ball n) (hy : ‖(y : E n)‖ = 1) :
    (src.hom.comp (toC (globeToBall.{u} n).symm)) y =
      (tgt.hom.comp (toC (globeToBall.{u} n).symm)) y := by
  cases n with
  | zero =>
    have hz : (y : E 0) = 0 := by
      apply PiLp.ext
      intro i
      exact Fin.elim0 i
    rw [hz, norm_zero] at hy
    exact absurd hy zero_ne_one
  | succ m =>
    have hp' : topTheory.comp (topTheory.base (Shape.source m)) src =
          topTheory.comp (topTheory.base (Shape.source m)) tgt ∧
        topTheory.comp (topTheory.base (Shape.target m)) src =
          topTheory.comp (topTheory.base (Shape.target m)) tgt := by
      simpa [GlobularTheory.Parallel] using hp
    rcases hp' with ⟨hs, ht⟩
    have hsTop : shapeRealMap.{u} (Shape.source m) ≫ src =
        shapeRealMap.{u} (Shape.source m) ≫ tgt := hs
    have htTop : shapeRealMap.{u} (Shape.target m) ≫ src =
        shapeRealMap.{u} (Shape.target m) ≫ tgt := ht
    have hEq (side : Bool) :
        (src.hom.comp (toC (globeToBall.{u} (m + 1)).symm)).comp
            (ballFace (Nat.lt_succ_self m) side) =
          (tgt.hom.comp (toC (globeToBall.{u} (m + 1)).symm)).comp
            (ballFace (Nat.lt_succ_self m) side) := by
      apply ContinuousMap.ext
      intro z
      conv_lhs =>
        rw [ContinuousMap.comp_apply,
          diskOf_ballFace (Nat.lt_succ_self m) side src z]
      conv_rhs =>
        rw [ContinuousMap.comp_apply,
          diskOf_ballFace (Nat.lt_succ_self m) side tgt z]
      cases side with
      | false =>
        have hname : Shape.source m = Shape.face (Nat.lt_succ_self m) false := rfl
        rw [← hname]
        exact congrArg (fun ψ : shapeReal.{u} (Shape.globe m) ⟶ shapeReal.{u} S =>
          (ψ.hom.comp (toC (globeToBall.{u} m).symm)) z) hsTop
      | true =>
        have hname : Shape.target m = Shape.face (Nat.lt_succ_self m) true := rfl
        rw [← hname]
        exact congrArg (fun ψ : shapeReal.{u} (Shape.globe m) ⟶ shapeReal.{u} S =>
          (ψ.hom.comp (toC (globeToBall.{u} m).symm)) z) htTop
    exact agree_on_sphere_of_faces (hEq false) (hEq true) y hy

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Coning and then returning along the globe homeomorphism is the original map. -/
lemma ofDisk_roundtrip {S : Shape} {n : ℕ}
    (φ : shapeReal.{u} (Shape.globe n) ⟶ shapeReal.{u} S) :
    TopCat.ofHom ((φ.hom.comp (toC (globeToBall.{u} n).symm)).comp
      (toC (globeToBall.{u} n))) = φ := by
  apply TopCat.hom_ext
  rw [TopCat.hom_ofHom, ContinuousMap.comp_assoc]
  have hid : (toC (globeToBall.{u} n).symm).comp (toC (globeToBall.{u} n)) =
      ContinuousMap.id _ := by
    apply ContinuousMap.ext
    intro x
    rw [ContinuousMap.comp_apply]
    have h1 : toC (globeToBall.{u} n) x = globeToBall.{u} n x := rfl
    have h2 : toC (globeToBall.{u} n).symm (globeToBall.{u} n x) =
        (globeToBall.{u} n).symm (globeToBall.{u} n x) := rfl
    rw [h1, h2, Homeomorph.symm_apply_apply]
    exact (ContinuousMap.id_apply x).symm
  rw [hid, ContinuousMap.comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A coned disk, precomposed with a face, is the cone precomposed with that hemisphere. -/
lemma ofDisk_face {S : Shape} {b h : ℕ} (hr : b < h) (side : Bool)
    (w : C(Ball h, shapeReal.{u} S)) :
    shapeRealMap.{u} (Shape.face hr side) ≫
        TopCat.ofHom (w.comp (toC (globeToBall.{u} h))) =
      TopCat.ofHom ((w.comp (ballFace hr side)).comp (toC (globeToBall.{u} b))) := by
  apply TopCat.hom_ext
  simp only [TopCat.hom_comp, TopCat.hom_ofHom]
  rw [ContinuousMap.comp_assoc, globeToBall_face hr side, ← ContinuousMap.comp_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Parallel maps of a realized globe extend along the next globe. -/
lemma exists_globeFiller {S : Shape} {n : ℕ}
    (src tgt : shapeReal.{u} (Shape.globe n) ⟶ shapeReal.{u} S)
    (hp : topTheory.Parallel n src tgt) :
    ∃ w : shapeReal.{u} (Shape.globe (n + 1)) ⟶ shapeReal.{u} S,
      shapeRealMap.{u} (Shape.source n) ≫ w = src ∧
      shapeRealMap.{u} (Shape.target n) ≫ w = tgt := by
  have : ContractibleSpace (↑(shapeReal.{u} S)) := contractible_shapeReal.{u} S
  let srcDisk : C(Ball n, ↑(shapeReal.{u} S)) :=
    src.hom.comp (toC (globeToBall.{u} n).symm)
  let tgtDisk : C(Ball n, ↑(shapeReal.{u} S)) :=
    tgt.hom.comp (toC (globeToBall.{u} n).symm)
  have hagree : ∀ y : Ball n, ‖(y : E n)‖ = 1 → srcDisk y = tgtDisk y :=
    fun y hy => diskMaps_agree src tgt hp y hy
  obtain ⟨wDisk, hsrc, htgt⟩ := exists_ballFiller srcDisk tgtDisk hagree
  refine ⟨TopCat.ofHom (wDisk.comp (toC (globeToBall.{u} (n + 1)))), ?_, ?_⟩
  · have hname : Shape.source n = Shape.face (Nat.lt_succ_self n) false := rfl
    rw [hname, ofDisk_face (Nat.lt_succ_self n) false wDisk, hsrc]
    exact ofDisk_roundtrip src
  · have hname : Shape.target n = Shape.face (Nat.lt_succ_self n) true := rfl
    rw [hname, ofDisk_face (Nat.lt_succ_self n) true wDisk, htgt]
    exact ofDisk_roundtrip tgt

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Read a hom of the theory of spaces as a map of realized shapes. -/
noncomputable def homOfTop {S T : Shape} (f : topTheory.Hom S T) :
    shapeReal S ⟶ shapeReal T := f

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Read a map of realized shapes as a hom of the theory of spaces. -/
noncomputable def topOfHom {S T : Shape} (f : shapeReal S ⟶ shapeReal T) :
    topTheory.Hom S T := f

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Parallelism is unchanged by reading homs as realized maps. -/
lemma parallel_of_homOfTop {S : Shape} {n : ℕ}
    (src tgt : topTheory.Hom (Shape.globe n) S)
    (hp : topTheory.Parallel n src tgt) :
    topTheory.Parallel n (homOfTop src) (homOfTop tgt) := hp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A realized face square is a filler square in the theory of spaces. -/
lemma fills_of_globe {S : Shape} {n : ℕ}
    (src : topTheory.Hom (Shape.globe n) S)
    (w : shapeReal (Shape.globe (n + 1)) ⟶ shapeReal S)
    (face : Shape.globe n ⟶ Shape.globe (n + 1))
    (hs : shapeRealMap face ≫ w = homOfTop src) :
    topTheory.comp (topTheory.base face) (topOfHom w) =
      (GlobularTheory.Morphism.id topTheory).map src := hs

/-- Every admissible pair in the theory of spaces has a filler. -/
theorem topTheory_hasFillers (a : topTheory.AdmissiblePair) :
    ∃ w : topTheory.Hom (Shape.globe (a.n + 1)) a.arity,
      topTheory.Fills (GlobularTheory.Morphism.id topTheory) a w := by
  obtain ⟨w, hs, ht⟩ :=
    exists_globeFiller (homOfTop a.source) (homOfTop a.target)
      (parallel_of_homOfTop a.source a.target a.parallel)
  exact ⟨topOfHom w,
    fills_of_globe a.source w (Shape.source a.n) hs,
    fills_of_globe a.target w (Shape.target a.n) ht⟩

theorem topToTerm_liftsFillers :
    GlobularTheory.LiftsFillers topToTerm := by
  intro a z hz
  obtain ⟨w, hw⟩ := topTheory_hasFillers a
  exact ⟨w, hw, Subsingleton.elim _ _⟩

/-! ## The realization -/

/-- The lifted morphism of theories. -/
noncomputable def realizeMorphism : GlobularTheory.Morphism C topTheory := by
  classical
  let P := Classical.choice hC.1
  exact (Classical.indefiniteDescription _
    (P.lift topToTerm topToTerm_liftsFillers (toTerm C))).1

/-- The realization functor. -/
noncomputable def realizeFunctor : C.Obj ⥤ TopCat.{u} where
  obj S := shapeReal.{u} S.shape
  map g := (realizeMorphism hC).map g
  map_id S := (realizeMorphism hC).map_id S.shape
  map_comp f g := (realizeMorphism hC).map_comp f g

/-- The realization sends globular sums to pushouts. -/
theorem realizeFunctor_sums (S : Shape) (b h : ℕ) (hl : b < S.1) (hr : b < h) :
    IsPushout ((realizeFunctor hC).map (C.toTheoryData.arity.map (S.seam hl)))
      ((realizeFunctor hC).map (C.toTheoryData.arity.map (Shape.face hr false)))
      ((realizeFunctor hC).map (C.toTheoryData.arity.map (S.inl b h hl hr)))
      ((realizeFunctor hC).map (C.toTheoryData.arity.map (S.inr b h hl hr))) := by
  have e1 : (realizeFunctor hC).map (C.toTheoryData.arity.map (S.seam hl)) =
      topTheory.base (S.seam hl) := (realizeMorphism hC).map_base _
  have e2 : (realizeFunctor hC).map (C.toTheoryData.arity.map (Shape.face hr false)) =
      topTheory.base (Shape.face hr false) := (realizeMorphism hC).map_base _
  have e3 : (realizeFunctor hC).map (C.toTheoryData.arity.map (S.inl b h hl hr)) =
      topTheory.base (S.inl b h hl hr) := (realizeMorphism hC).map_base _
  have e4 : (realizeFunctor hC).map (C.toTheoryData.arity.map (S.inr b h hl hr)) =
      topTheory.base (S.inr b h hl hr) := (realizeMorphism hC).map_base _
  rw [e1, e2, e3, e4]
  exact shapeReal_pushout.{u} S b h hl hr

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The realization agrees with the standard globes on globes. -/
noncomputable def realizeOnGlobes :
    C.globes ⋙ realizeFunctor hC ≅ oaiTopGlobes.{u} :=
  NatIso.ofComponents (fun n => globeRealIso.{u} n.dim) (fun f => by
    have hmap : (C.globes ⋙ realizeFunctor hC).map f =
        topTheory.base (GlobularTheory.shapeGlobes.map f) :=
      (realizeMorphism hC).map_base (GlobularTheory.shapeGlobes.map f)
    rw [hmap]
    have hbase : topTheory.base (GlobularTheory.shapeGlobes.map f) =
        shapeRealMap.{u} (GlobularTheory.shapeGlobes.map f) := rfl
    rw [hbase]
    exact globeRealIso_naturality.{u} f)

/-- The assembled realization. -/
noncomputable def oaiRealizationOf : OAIRealization C where
  functor := realizeFunctor hC
  onGlobes := realizeOnGlobes hC
  sums := realizeFunctor_sums hC

/-- Every coherator has a topological realization. -/
theorem exists_realization_proof (C : GlobularTheory.{u}) (hC : C.IsCoherator) :
    Nonempty (OAIRealization C) :=
  ⟨oaiRealizationOf hC⟩

example (C : GlobularTheory.{u}) (hC : C.IsCoherator) :
    Nonempty (OAIRealization C) :=
  exists_realization_proof C hC

#print axioms exists_realization_proof

end HomotopyHypothesis.Realization.Functor
