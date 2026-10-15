import HomotopyHypothesis.Blueprint.Henry.Coherator
import HomotopyHypothesis.Blueprint.Henry.CylinderCategory
import HomotopyHypothesis.FiniteCategory.Lifting.Extensions
import HomotopyHypothesis.FiniteCategory.Lifting.Nerve
/-!+# Lifting the globular boundary frame

Each new disk is obtained by lifting the factorization of a codiagonal through the next disk.
The weak-equivalence leg may be any unit operation, including a composite operation.
-/

noncomputable section

universe u v u₁

open CategoryTheory Limits HomotopicalAlgebra
open OAI.Grothendieck
open HomotopyHypothesis.Henry

namespace HomotopyHypothesis.FiniteCategory.Lifting

variable {X : Type u} [Category.{v} X] [CategoryWithCofibrations X]
  [CategoryWithWeakEquivalences X] [IsCylinderCategory X]
  {Y : Type u₁} [Category.{v} Y] [CategoryWithCofibrations Y]
  [CategoryWithWeakEquivalences Y] [IsCylinderCategory Y]

/-- A disk and its boundary, lifting one stage of a globular frame. -/
structure FrameNode (p : X ⥤ Y) (B : GlobularFrame Y) (n : ℕ) where
  bd : X
  disk : X
  inc : bd ⟶ disk
  cof : cofibrations X inc
  bdIso : p.obj bd ≅ B.bd n
  diskIso : p.obj disk ≅ B.obj n
  inc_over : p.map inc ≫ diskIso.hom = bdIso.hom ≫ B.inc n

/-- One lifted codiagonal factorization, together with its boundary pushout. -/
structure FrameStep {p : X ⥤ Y} {B : GlobularFrame Y} {n : ℕ} (a : FrameNode p B n) where
  next : FrameNode p B (n+1)
  left : a.disk ⟶ next.bd
  right : a.disk ⟶ next.bd
  square : IsPushout a.inc a.inc left right
  unit : next.disk ⟶ a.disk
  unit_mem : weakEquivalences X unit
  left_unit : left ≫ next.inc ≫ unit = 𝟙 _
  right_unit : right ≫ next.inc ≫ unit = 𝟙 _
  over_left : p.map left ≫ next.bdIso.hom = a.diskIso.hom ≫ B.left n
  over_right : p.map right ≫ next.bdIso.hom = a.diskIso.hom ≫ B.right n

/-- Lift the next disk by factoring the boundary codiagonal through its prescribed image. -/
theorem frameStep_exists {p : X ⥤ Y} (hp : IsPreFibration p) (hm : IsCylinderMorphism p)
    (B : GlobularFrame Y) (hc : ∀ n, cofibrations Y (B.inc n))
    (unit : ∀ n, B.obj (n+1) ⟶ B.obj n) (hw : ∀ n, weakEquivalences Y (unit n))
    (h₀ : ∀ n, B.left n ≫ B.inc (n+1) ≫ unit n = 𝟙 _)
    (h₁ : ∀ n, B.right n ≫ B.inc (n+1) ≫ unit n = 𝟙 _)
    {n : ℕ} (a : FrameNode p B n) : Nonempty (FrameStep a) := by
  classical
  letI : HasPushout a.inc a.inc := IsCofibrationCategory.hasPushout _ _ a.cof
  let P := pushout a.inc a.inc
  let k : a.disk ⟶ P := pushout.inl a.inc a.inc
  let j : a.disk ⟶ P := pushout.inr a.inc a.inc
  have sq : IsPushout a.inc a.inc k j := IsPushout.of_hasPushout _ _
  have psq := hm.map_isPushout a.inc a.inc k j sq a.cof
  have hover : B.inc n ≫ a.diskIso.inv = a.bdIso.inv ≫ p.map a.inc := by
    calc
      B.inc n ≫ a.diskIso.inv =
          a.bdIso.inv ≫ (a.bdIso.hom ≫ B.inc n) ≫ a.diskIso.inv := by simp
      _ = a.bdIso.inv ≫ (p.map a.inc ≫ a.diskIso.hom) ≫ a.diskIso.inv := by rw [a.inc_over]
      _ = a.bdIso.inv ≫ p.map a.inc := by simp [Category.assoc]
  have bsq : IsPushout (p.map a.inc) (p.map a.inc)
      (a.diskIso.hom ≫ B.left n) (a.diskIso.hom ≫ B.right n) :=
    (B.square n).of_iso a.bdIso.symm a.diskIso.symm a.diskIso.symm (Iso.refl _)
      hover hover (by simp) (by simp)
  let κ : p.obj P ≅ B.bd (n+1) := psq.isoIsPushout _ _ bsq
  let d : P ⟶ a.disk := sq.desc (𝟙 _) (𝟙 _) (by simp)
  let i : p.obj P ⟶ B.obj (n+1) := κ.hom ≫ B.inc (n+1)
  let w : B.obj (n+1) ⟶ p.obj a.disk := unit n ≫ a.diskIso.inv
  have hi : cofibrations Y i :=
    (IsCofibrationCategory.isMultiplicative (C := Y)).comp_mem _ _
      (IsCofibrationCategory.isomorphisms_le _ inferInstance) (hc _)
  have hw' : weakEquivalences Y w :=
    (IsCylinderCategory.weakEquivalences_isMultiplicative (C := Y)).comp_mem _ _
      (hw _) (IsCylinderCategory.isomorphisms_le_weakEquivalences _ inferInstance)
  have hfactor : i ≫ w = p.map d := by
    apply psq.hom_ext
    · calc
        p.map k ≫ (i ≫ w) = a.diskIso.hom ≫
            (B.left n ≫ B.inc (n+1) ≫ unit n) ≫ a.diskIso.inv := by
          simp [i, w, κ, Category.assoc]
        _ = 𝟙 _ := by rw [h₀]; simp
        _ = p.map k ≫ p.map d := by rw [← p.map_comp]; simp [d]
    · calc
        p.map j ≫ (i ≫ w) = a.diskIso.hom ≫
            (B.right n ≫ B.inc (n+1) ≫ unit n) ≫ a.diskIso.inv := by
          simp [i, w, κ, Category.assoc]
        _ = 𝟙 _ := by rw [h₁]; simp
        _ = p.map j ≫ p.map d := by rw [← p.map_comp]; simp [d]
  obtain ⟨Z, i', w', e, hi', hw'', hiw, hpi, _⟩ :=
    hp.lift_factorization d i w hi hw' hfactor
  let b : FrameNode p B (n+1) :=
    { bd := P
      disk := Z
      inc := i'
      cof := hi'
      bdIso := κ
      diskIso := eqToIso e
      inc_over := by simp [hpi, i, Category.assoc] }
  refine ⟨⟨b, k, j, sq, w', hw'', ?_, ?_, ?_, ?_⟩⟩
  · change k ≫ i' ≫ w' = 𝟙 _
    rw [hiw]
    simp [d]
  · change j ≫ i' ≫ w' = 𝟙 _
    rw [hiw]
    simp [d]
  · exact psq.inl_isoIsPushout_hom _ _ bsq
  · exact psq.inr_isoIsPushout_hom _ _ bsq

/-- A lifted stage makes its two structural endpoints trivial cofibrations. -/
theorem frameStep_endpoints {p : X ⥤ Y} {B : GlobularFrame Y} {n : ℕ}
    {a : FrameNode p B n} (s : FrameStep a) :
    (cofibrations X (s.left ≫ s.next.inc) ∧ weakEquivalences X (s.left ≫ s.next.inc)) ∧
      (cofibrations X (s.right ≫ s.next.inc) ∧ weakEquivalences X (s.right ≫ s.next.inc)) := by
  let cyl : RelativeCylinder a.inc :=
    { P := s.next.bd
      j₀ := s.left
      j₁ := s.right
      isPushout := s.square
      I := s.next.disk
      c := s.next.inc
      p := s.unit
      c_mem := s.next.cof
      p_mem := s.unit_mem
      j₀_c_p := s.left_unit
      j₁_c_p := s.right_unit }
  let cyl' : RelativeCylinder a.inc :=
    { cyl with
      j₀ := s.right
      j₁ := s.left
      isPushout := s.square.flip
      j₀_c_p := s.right_unit
      j₁_c_p := s.left_unit }
  exact ⟨relativeCylinder_endpoint a.cof cyl, relativeCylinder_endpoint a.cof cyl'⟩

/-- The marked object gives the initial lifted disk node. -/
theorem frameNode_zero_exists {p : X ⥤ Y} (hm : IsCylinderMorphism p)
    (B : GlobularFrame Y) (x : X) (e : p.obj x ≅ B.obj 0) :
    ∃ a : FrameNode p B 0, a.disk = x ∧ Nonempty (IsInitial a.bd) := by
  classical
  obtain ⟨O, ⟨hO⟩⟩ := IsCofibrationCategory.exists_initial (C := X)
  obtain ⟨hpO⟩ := hm.map_initial hO
  let a : FrameNode p B 0 :=
    { bd := O
      disk := x
      inc := hO.to x
      cof := IsCofibrationCategory.initial_cofibration hO x
      bdIso := hpO.uniqueUpToIso B.initial
      diskIso := e
      inc_over := hpO.hom_ext _ _ }
  exact ⟨a, rfl, ⟨hO⟩⟩

/-- The initial disk node retains the prescribed comparison isomorphism. -/
theorem frameNode_zero_pointed_exists {p : X ⥤ Y} (hm : IsCylinderMorphism p)
    (B : GlobularFrame Y) (x : X) (e : p.obj x ≅ B.obj 0) :
    ∃ a : FrameNode p B 0, ∃ h₀ : a.disk = x,
      a.diskIso = eqToIso (congrArg p.obj h₀) ≪≫ e ∧ Nonempty (IsInitial a.bd) := by
  classical
  obtain ⟨O, ⟨hO⟩⟩ := IsCofibrationCategory.exists_initial (C := X)
  obtain ⟨hpO⟩ := hm.map_initial hO
  let a : FrameNode p B 0 :=
    { bd := O
      disk := x
      inc := hO.to x
      cof := IsCofibrationCategory.initial_cofibration hO x
      bdIso := hpO.uniqueUpToIso B.initial
      diskIso := e
      inc_over := hpO.hom_ext _ _ }
  exact ⟨a, rfl, by simp [a], ⟨hO⟩⟩

/-- A globular frame lifting up to isomorphism, with cofibrant boundaries and trivial endpoints. -/
structure LiftedFrame (p : X ⥤ Y) (B : GlobularFrame Y) where
  frame : GlobularFrame X
  objIso : ∀ n, p.obj (frame.obj n) ≅ B.obj n
  bdIso : ∀ n, p.obj (frame.bd n) ≅ B.bd n
  inc_cof : ∀ n, cofibrations X (frame.inc n)
  endpoints : ∀ n,
    (cofibrations X (frame.diagram.source n) ∧ weakEquivalences X (frame.diagram.source n)) ∧
      (cofibrations X (frame.diagram.target n) ∧ weakEquivalences X (frame.diagram.target n))
  inc_over : ∀ n, p.map (frame.inc n) ≫ (objIso n).hom = (bdIso n).hom ≫ B.inc n
  left_over : ∀ n, p.map (frame.left n) ≫ (bdIso (n+1)).hom = (objIso n).hom ≫ B.left n
  right_over : ∀ n, p.map (frame.right n) ≫ (bdIso (n+1)).hom = (objIso n).hom ≫ B.right n

/-- Assemble all lifted disk stages, retaining the marked zero disk. -/
theorem liftedFrame_exists {p : X ⥤ Y} (hp : IsPreFibration p) (hm : IsCylinderMorphism p)
    (B : GlobularFrame Y) (hc : ∀ n, cofibrations Y (B.inc n))
    (unit : ∀ n, B.obj (n+1) ⟶ B.obj n) (hw : ∀ n, weakEquivalences Y (unit n))
    (h₀ : ∀ n, B.left n ≫ B.inc (n+1) ≫ unit n = 𝟙 _)
    (h₁ : ∀ n, B.right n ≫ B.inc (n+1) ≫ unit n = 𝟙 _)
    (x : X) (e : p.obj x ≅ B.obj 0) :
    ∃ L : LiftedFrame p B, L.frame.obj 0 = x := by
  classical
  obtain ⟨a₀, ha₀, ⟨hInitial⟩⟩ := frameNode_zero_exists hm B x e
  let step (n : ℕ) (a : FrameNode p B n) : FrameStep a :=
    Classical.choice (frameStep_exists hp hm B hc unit hw h₀ h₁ a)
  let nodes : ∀ n, FrameNode p B n :=
    fun n => Nat.rec a₀ (fun n a => (step n a).next) n
  let A : GlobularFrame X :=
    { obj n := (nodes n).disk
      bd n := (nodes n).bd
      inc n := (nodes n).inc
      left n := (step n (nodes n)).left
      right n := (step n (nodes n)).right
      square n := (step n (nodes n)).square
      initial := hInitial }
  let L : LiftedFrame p B :=
    { frame := A
      objIso n := (nodes n).diskIso
      bdIso n := (nodes n).bdIso
      inc_cof n := (nodes n).cof
      endpoints n := frameStep_endpoints (step n (nodes n))
      inc_over n := (nodes n).inc_over
      left_over n := (step n (nodes n)).over_left
      right_over n := (step n (nodes n)).over_right }
  exact ⟨L, ha₀⟩

/-- Assemble a lifted frame with its prescribed comparison at the marked disk. -/
theorem liftedFrame_pointed_exists {p : X ⥤ Y} (hp : IsPreFibration p)
    (hm : IsCylinderMorphism p) (B : GlobularFrame Y) (hc : ∀ n, cofibrations Y (B.inc n))
    (unit : ∀ n, B.obj (n+1) ⟶ B.obj n) (hw : ∀ n, weakEquivalences Y (unit n))
    (h₀ : ∀ n, B.left n ≫ B.inc (n+1) ≫ unit n = 𝟙 _)
    (h₁ : ∀ n, B.right n ≫ B.inc (n+1) ≫ unit n = 𝟙 _)
    (x : X) (e : p.obj x ≅ B.obj 0) :
    ∃ L : LiftedFrame p B, ∃ h : L.frame.obj 0 = x,
      L.objIso 0 = eqToIso (congrArg p.obj h) ≪≫ e := by
  classical
  obtain ⟨a₀, ha₀, he, ⟨hInitial⟩⟩ := frameNode_zero_pointed_exists hm B x e
  let step (n : ℕ) (a : FrameNode p B n) : FrameStep a :=
    Classical.choice (frameStep_exists hp hm B hc unit hw h₀ h₁ a)
  let nodes : ∀ n, FrameNode p B n :=
    fun n => Nat.rec a₀ (fun n a => (step n a).next) n
  let A : GlobularFrame X :=
    { obj n := (nodes n).disk
      bd n := (nodes n).bd
      inc n := (nodes n).inc
      left n := (step n (nodes n)).left
      right n := (step n (nodes n)).right
      square n := (step n (nodes n)).square
      initial := hInitial }
  let L : LiftedFrame p B :=
    { frame := A
      objIso n := (nodes n).diskIso
      bdIso n := (nodes n).bdIso
      inc_cof n := (nodes n).cof
      endpoints n := frameStep_endpoints (step n (nodes n))
      inc_over n := (nodes n).inc_over
      left_over n := (step n (nodes n)).over_left
      right_over n := (step n (nodes n)).over_right }
  exact ⟨L, ha₀, he⟩

namespace LiftedFrame

/-- Naturality of the lifted source maps. -/
theorem source_over {p : X ⥤ Y} {B : GlobularFrame Y} (L : LiftedFrame p B) (n : ℕ) :
    p.map (L.frame.diagram.source n) ≫ (L.objIso (n+1)).hom =
      (L.objIso n).hom ≫ B.diagram.source n := by
  change p.map (L.frame.left n ≫ L.frame.inc (n+1)) ≫ (L.objIso (n+1)).hom = _
  rw [p.map_comp, Category.assoc, L.inc_over, ← Category.assoc, L.left_over, Category.assoc]
  rfl

/-- Naturality of the lifted target maps. -/
theorem target_over {p : X ⥤ Y} {B : GlobularFrame Y} (L : LiftedFrame p B) (n : ℕ) :
    p.map (L.frame.diagram.target n) ≫ (L.objIso (n+1)).hom =
      (L.objIso n).hom ≫ B.diagram.target n := by
  change p.map (L.frame.right n ≫ L.frame.inc (n+1)) ≫ (L.objIso (n+1)).hom = _
  rw [p.map_comp, Category.assoc, L.inc_over, ← Category.assoc, L.right_over, Category.assoc]
  rfl

end LiftedFrame

#print axioms frameStep_exists
#print axioms frameStep_endpoints
#print axioms liftedFrame_exists
#print axioms liftedFrame_pointed_exists

end HomotopyHypothesis.FiniteCategory.Lifting
