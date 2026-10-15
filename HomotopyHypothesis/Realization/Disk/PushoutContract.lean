import HomotopyHypothesis.Challenge
import HomotopyHypothesis.Realization.Disk.FaceRetract
/-!
# Contractibility of a pushout along a hemisphere retract

A closed disk strongly deformation retracts onto a source hemisphere. Gluing a contractible
space to the disk along that hemisphere therefore keeps the pushout contractible: slide the
disk onto the hemisphere, then run the contraction of the other leg.
-/

noncomputable section

namespace HomotopyHypothesis.Realization.Disk

open CategoryTheory CategoryTheory.Limits
open ContinuousMap

universe u v

/-- Continuous map underlying a homeomorphism. -/
def toC {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    C(X, Y) :=
  ⟨e, e.continuous_toFun⟩

/-- A strong deformation retraction of an inclusion `i`. -/
structure StrongDeformation {A D : Type u} [TopologicalSpace A] [TopologicalSpace D]
    (i : C(A, D)) where
  /-- Retraction of `i`. -/
  r : C(D, A)
  /-- `r` splits `i`. -/
  retract_comp : r.comp i = ContinuousMap.id A
  /-- Straight homotopy from the identity of `D` to `i ∘ r`. -/
  hom : Homotopy (ContinuousMap.id D) (i.comp r)
  /-- The homotopy does not move the image of `i`. -/
  fixes : ∀ (t : unitInterval) (a : A), hom (t, i a) = i a

/-- The source-hemisphere inclusion is a strong deformation retraction of the disk. -/
def ballFaceSDR {m n : ℕ} (hm : m < n) : StrongDeformation (ballFace hm false) where
  r := faceFront hm
  retract_comp := faceFront_section hm
  hom := faceDeformation hm
  fixes := faceDeformation_fixes hm

/-- Transport a strong deformation retraction across a pair of homeomorphisms. -/
def StrongDeformation.transport {A D : Type u} {A' D' : Type v}
    [TopologicalSpace A] [TopologicalSpace D] [TopologicalSpace A'] [TopologicalSpace D']
    {i : C(A, D)} (s : StrongDeformation i) (eA : A ≃ₜ A') (eD : D ≃ₜ D')
    (i' : C(A', D')) (hsq : (toC eD).comp i = i'.comp (toC eA)) :
    StrongDeformation i' where
  r := (toC eA).comp (s.r.comp (toC eD.symm))
  retract_comp := by
    apply ContinuousMap.ext
    intro a'
    have hsq_apply : ∀ a, eD (i a) = i' (eA a) := fun a => DFunLike.congr_fun hsq a
    have hback : eD.symm (i' a') = i (eA.symm a') := by
      apply eD.injective
      rw [eD.apply_symm_apply, hsq_apply (eA.symm a'), eA.apply_symm_apply]
    have hret : s.r (i (eA.symm a')) = eA.symm a' :=
      DFunLike.congr_fun s.retract_comp (eA.symm a')
    change eA (s.r (eD.symm (i' a'))) = a'
    rw [hback, hret, eA.apply_symm_apply]
  hom :=
    { toFun := fun p => eD (s.hom (p.1, eD.symm p.2))
      continuous_toFun :=
        eD.continuous_toFun.comp
          (s.hom.continuous_toFun.comp
            (continuous_fst.prodMk (eD.symm.continuous_toFun.comp continuous_snd)))
      map_zero_left := fun d' => by
        change eD (s.hom (0, eD.symm d')) = d'
        have h0 : s.hom (0, eD.symm d') = eD.symm d' := s.hom.map_zero_left (eD.symm d')
        rw [h0, eD.apply_symm_apply]
      map_one_left := fun d' => by
        have hsq_apply : ∀ a, eD (i a) = i' (eA a) := fun a => DFunLike.congr_fun hsq a
        change eD (s.hom (1, eD.symm d')) = i' (eA (s.r (eD.symm d')))
        have h1 : s.hom (1, eD.symm d') = i (s.r (eD.symm d')) :=
          s.hom.map_one_left (eD.symm d')
        rw [h1, hsq_apply] }
  fixes := fun t a' => by
    have hsq_apply : ∀ a, eD (i a) = i' (eA a) := fun a => DFunLike.congr_fun hsq a
    have hback : eD.symm (i' a') = i (eA.symm a') := by
      apply eD.injective
      rw [eD.apply_symm_apply, hsq_apply (eA.symm a'), eA.apply_symm_apply]
    change eD (s.hom (t, eD.symm (i' a'))) = i' a'
    have hfix : s.hom (t, i (eA.symm a')) = i (eA.symm a') := s.fixes t (eA.symm a')
    rw [hback, hfix, hsq_apply, eA.apply_symm_apply]

/-- Generating relation of the pushout of `f` and `i`: identify `f a` with `i a`. -/
inductive GlueRel {A X D : Type u} (f : A → X) (i : A → D) : X ⊕ D → X ⊕ D → Prop
  | rel (a : A) : GlueRel f i (Sum.inl (f a)) (Sum.inr (i a))

/-- Underlying set of the pushout `X ∪_A D`. -/
abbrev Glue {A X D : Type u} [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace D]
    (f : C(A, X)) (i : C(A, D)) : Type u :=
  Quot (GlueRel (f : A → X) (i : A → D))

variable {A X D : Type u} [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace D]

/-- Inclusion of the contractible leg. -/
def glueInl (f : C(A, X)) (i : C(A, D)) : C(X, Glue f i) :=
  ⟨fun x => Quot.mk _ (Sum.inl x), continuous_quot_mk.comp continuous_inl⟩

/-- Inclusion of the retracted leg. -/
def glueInr (f : C(A, X)) (i : C(A, D)) : C(D, Glue f i) :=
  ⟨fun d => Quot.mk _ (Sum.inr d), continuous_quot_mk.comp continuous_inr⟩

lemma glue_ident (f : C(A, X)) (i : C(A, D)) (a : A) :
    glueInl f i (f a) = glueInr f i (i a) :=
  Quot.sound (GlueRel.rel a)

/-- Descend a pair of maps that agree on `A`. -/
def glueDesc {W : Type u} [TopologicalSpace W] (f : C(A, X)) (i : C(A, D))
    (k : C(X, W)) (m : C(D, W)) (hkm : k.comp f = m.comp i) : C(Glue f i, W) :=
  ⟨Quot.lift (Sum.elim k m) (fun _ _ hab => by
      cases hab with
      | rel a => exact DFunLike.congr_fun hkm a),
    continuous_quot_lift _ (k.continuous.sumElim m.continuous)⟩

lemma glueDesc_inl {W : Type u} [TopologicalSpace W] (f : C(A, X)) (i : C(A, D))
    (k : C(X, W)) (m : C(D, W)) (hkm : k.comp f = m.comp i) (x : X) :
    glueDesc f i k m hkm (glueInl f i x) = k x :=
  rfl

lemma glueDesc_inr {W : Type u} [TopologicalSpace W] (f : C(A, X)) (i : C(A, D))
    (k : C(X, W)) (m : C(D, W)) (hkm : k.comp f = m.comp i) (d : D) :
    glueDesc f i k m hkm (glueInr f i d) = m d :=
  rfl

/-- The two legs of a pushout cocone agree on the underlying continuous maps. -/
lemma spanHom_eq (f : C(A, X)) (i : C(A, D)) {W : TopCat.{u}}
    {inl : TopCat.of X ⟶ W} {inr : TopCat.of D ⟶ W}
    (eq : TopCat.ofHom f ≫ inl = TopCat.ofHom i ≫ inr) :
    inl.hom.comp f = inr.hom.comp i := by
  simpa [TopCat.hom_comp, TopCat.hom_ofHom] using congrArg TopCat.Hom.hom eq

/-- The concrete quotient is the pushout in `Top`. -/
theorem glue_isPushout (f : C(A, X)) (i : C(A, D)) :
    IsPushout (TopCat.ofHom f) (TopCat.ofHom i)
      (TopCat.ofHom (glueInl f i)) (TopCat.ofHom (glueInr f i)) := by
  have heq : TopCat.ofHom f ≫ TopCat.ofHom (glueInl f i) =
      TopCat.ofHom i ≫ TopCat.ofHom (glueInr f i) := by
    rw [← TopCat.ofHom_comp, ← TopCat.ofHom_comp]
    congr 1
    apply ContinuousMap.ext
    intro a
    exact glue_ident f i a
  refine IsPushout.of_isColimit
      (c := PushoutCocone.mk (TopCat.ofHom (glueInl f i)) (TopCat.ofHom (glueInr f i)) heq)
      (PushoutCocone.IsColimit.mk heq
        (fun s => TopCat.ofHom
          (glueDesc f i s.inl.hom s.inr.hom (spanHom_eq f i s.condition)))
        (fun s => by
          apply TopCat.ext
          intro x
          simp [glueDesc_inl])
        (fun s => by
          apply TopCat.ext
          intro d
          simp [glueDesc_inr])
        (fun s m hleft hright => by
          apply TopCat.ext
          intro q
          refine Quot.induction_on q ?_
          intro z
          cases z with
          | inl x =>
            have hmk : glueInl f i x =
                Quot.mk (GlueRel (f : A → X) (i : A → D)) (Sum.inl x) := rfl
            rw [← hmk]
            have happ : m (glueInl f i x) = s.inl.hom x := by
              simpa [TopCat.comp_app, TopCat.ofHom_apply] using
                congrFun (congrArg (fun g : TopCat.of X ⟶ s.pt => (g : X → s.pt)) hleft) x
            rw [happ]
            exact (glueDesc_inl f i s.inl.hom s.inr.hom (spanHom_eq f i s.condition) x).symm
          | inr d =>
            have hmk : glueInr f i d =
                Quot.mk (GlueRel (f : A → X) (i : A → D)) (Sum.inr d) := rfl
            rw [← hmk]
            have happ : m (glueInr f i d) = s.inr.hom d := by
              simpa [TopCat.comp_app, TopCat.ofHom_apply] using
                congrFun (congrArg (fun g : TopCat.of D ⟶ s.pt => (g : D → s.pt)) hright) d
            rw [happ]
            exact (glueDesc_inr f i s.inl.hom s.inr.hom (spanHom_eq f i s.condition) d).symm))

/-! ## The two-stage contraction -/

variable {i : C(A, D)} (s : StrongDeformation i) (f : C(A, X))

/-- Slide the disk along the deformation, and leave the other leg fixed. -/
def stage1Val (t : unitInterval) : X ⊕ D → Glue f i
  | Sum.inl x => Quot.mk _ (Sum.inl x)
  | Sum.inr d => Quot.mk _ (Sum.inr (s.hom (t, d)))

lemma stage1_resp (t : unitInterval) (a b : X ⊕ D) (hab : GlueRel f i a b) :
    stage1Val s f t a = stage1Val s f t b := by
  cases hab with
  | rel a =>
    change Quot.mk _ (Sum.inl (f a)) = Quot.mk _ (Sum.inr (s.hom (t, i a)))
    rw [s.fixes t a]
    exact Quot.sound (GlueRel.rel a)

/-- At time `1` the disk has moved onto the image of `A` inside `X`. -/
def squashFun : X ⊕ D → Glue f i :=
  Sum.elim (fun x => Quot.mk _ (Sum.inl x)) (fun d => Quot.mk _ (Sum.inl (f (s.r d))))

lemma squash_resp (a b : X ⊕ D) (hab : GlueRel f i a b) :
    squashFun s f a = squashFun s f b := by
  cases hab with
  | rel a =>
    change Quot.mk _ (Sum.inl (f a)) = Quot.mk _ (Sum.inl (f (s.r (i a))))
    have hr : s.r (i a) = a := DFunLike.congr_fun s.retract_comp a
    rw [hr]

/-- End of the first stage: every class is represented in the `X` copy. -/
def squash : C(Glue f i, Glue f i) :=
  ⟨Quot.lift (squashFun s f) (squash_resp s f),
    continuous_quot_lift _ <|
      (continuous_quot_mk.comp continuous_inl).sumElim
        (continuous_quot_mk.comp (continuous_inl.comp
          (f.continuous.comp s.r.continuous)))⟩

lemma stage1_zero (z : X ⊕ D) : stage1Val s f 0 z = Quot.mk _ z := by
  cases z with
  | inl x => rfl
  | inr d =>
    exact congrArg (fun d => Quot.mk _ (Sum.inr d)) (s.hom.map_zero_left d)

lemma stage1_one (z : X ⊕ D) : stage1Val s f 1 z = squashFun s f z := by
  cases z with
  | inl x => rfl
  | inr d =>
    change Quot.mk _ (Sum.inr (s.hom (1, d))) = Quot.mk _ (Sum.inl (f (s.r d)))
    have h1 : s.hom (1, d) = i (s.r d) := s.hom.map_one_left d
    rw [h1]
    exact (Quot.sound (GlueRel.rel (s.r d))).symm

/-- Joint map of the first stage, before descending to the quotient. -/
def stage1Raw : unitInterval × (X ⊕ D) → Glue f i :=
  fun p => stage1Val s f p.1 p.2

lemma continuous_stage1Raw : Continuous (stage1Raw s f) := by
  let e : unitInterval × (X ⊕ D) ≃ₜ (unitInterval × X) ⊕ (unitInterval × D) :=
    Homeomorph.prodSumDistrib
  let left : C(unitInterval × X, Glue f i) :=
    ⟨fun p => Quot.mk _ (Sum.inl p.2),
      continuous_quot_mk.comp (continuous_inl.comp continuous_snd)⟩
  let right : C(unitInterval × D, Glue f i) :=
    ⟨fun p => Quot.mk _ (Sum.inr (s.hom p)),
      continuous_quot_mk.comp (continuous_inr.comp s.hom.continuous_toFun)⟩
  have hsplit : Continuous (Sum.elim (⇑left) (⇑right) ∘ ⇑e) :=
    (left.continuous.sumElim right.continuous).comp e.continuous
  have heq : Sum.elim (⇑left) (⇑right) ∘ ⇑e = stage1Raw s f := by
    funext p
    rcases p with ⟨t, z⟩
    cases z with
    | inl x =>
      have hdis : e (t, Sum.inl x) = Sum.inl (t, x) := rfl
      rw [Function.comp_apply, hdis]
      rfl
    | inr d =>
      have hdis : e (t, Sum.inr d) = Sum.inr (t, d) := rfl
      rw [Function.comp_apply, hdis]
      rfl
  exact heq ▸ hsplit

lemma continuous_stage1 :
    Continuous fun p : unitInterval × Glue f i =>
      Quot.lift (stage1Val s f p.1) (stage1_resp s f p.1) p.2 := by
  refine (isQuotientMap_quot_mk (r := GlueRel (f : A → X) (i : A → D))).continuous_lift_prod_right ?_
  have heq : (fun p : unitInterval × (X ⊕ D) =>
      Quot.lift (stage1Val s f p.1) (stage1_resp s f p.1) (Quot.mk _ p.2)) =
      stage1Raw s f := by
    funext p
    exact Quot.lift_mk (stage1Val s f p.1) (stage1_resp s f p.1) p.2
  exact heq ▸ continuous_stage1Raw s f

/-- First stage: the identity slides onto `squash`. -/
def stage1Hom : Homotopy (ContinuousMap.id (Glue f i)) (squash s f) where
  toFun p := Quot.lift (stage1Val s f p.1) (stage1_resp s f p.1) p.2
  continuous_toFun := continuous_stage1 s f
  map_zero_left q := by
    refine Quot.induction_on q ?_
    intro z
    rw [Quot.lift_mk (stage1Val s f 0) (stage1_resp s f 0), stage1_zero s f z]
    rfl
  map_one_left q := by
    refine Quot.induction_on q ?_
    intro z
    rw [Quot.lift_mk (stage1Val s f 1) (stage1_resp s f 1)]
    exact stage1_one s f z

/-- Run a contraction of `X` on the image of the first stage. -/
def stage2Val {x0 : X} (K : Homotopy (ContinuousMap.id X) (ContinuousMap.const X x0))
    (t : unitInterval) : X ⊕ D → Glue f i
  | Sum.inl x => Quot.mk _ (Sum.inl (K (t, x)))
  | Sum.inr d => Quot.mk _ (Sum.inl (K (t, f (s.r d))))

lemma stage2_resp {x0 : X} (K : Homotopy (ContinuousMap.id X) (ContinuousMap.const X x0))
    (t : unitInterval) (a b : X ⊕ D) (hab : GlueRel f i a b) :
    stage2Val s f K t a = stage2Val s f K t b := by
  cases hab with
  | rel a =>
    change Quot.mk _ (Sum.inl (K (t, f a))) =
      Quot.mk _ (Sum.inl (K (t, f (s.r (i a)))))
    have hr : s.r (i a) = a := DFunLike.congr_fun s.retract_comp a
    rw [hr]

lemma stage2_zero {x0 : X} (K : Homotopy (ContinuousMap.id X) (ContinuousMap.const X x0))
    (z : X ⊕ D) : stage2Val s f K 0 z = squashFun s f z := by
  cases z with
  | inl x =>
    exact congrArg (fun x => Quot.mk _ (Sum.inl x)) (K.map_zero_left x)
  | inr d =>
    exact congrArg (fun x => Quot.mk _ (Sum.inl x)) (K.map_zero_left (f (s.r d)))

lemma stage2_one {x0 : X} (K : Homotopy (ContinuousMap.id X) (ContinuousMap.const X x0))
    (z : X ⊕ D) : stage2Val s f K 1 z = Quot.mk _ (Sum.inl x0) := by
  cases z with
  | inl x =>
    exact congrArg (fun x => Quot.mk _ (Sum.inl x)) (K.map_one_left x)
  | inr d =>
    exact congrArg (fun x => Quot.mk _ (Sum.inl x)) (K.map_one_left (f (s.r d)))

/-- Joint map of the second stage, before descending to the quotient. -/
def stage2Raw {x0 : X} (K : Homotopy (ContinuousMap.id X) (ContinuousMap.const X x0)) :
    unitInterval × (X ⊕ D) → Glue f i :=
  fun p => stage2Val s f K p.1 p.2

lemma continuous_stage2Raw {x0 : X}
    (K : Homotopy (ContinuousMap.id X) (ContinuousMap.const X x0)) :
    Continuous (stage2Raw s f K) := by
  let e : unitInterval × (X ⊕ D) ≃ₜ (unitInterval × X) ⊕ (unitInterval × D) :=
    Homeomorph.prodSumDistrib
  let left : C(unitInterval × X, Glue f i) :=
    ⟨fun p => Quot.mk _ (Sum.inl (K p)),
      continuous_quot_mk.comp (continuous_inl.comp K.continuous_toFun)⟩
  let right : C(unitInterval × D, Glue f i) :=
    ⟨fun p => Quot.mk _ (Sum.inl (K (p.1, f (s.r p.2)))),
      continuous_quot_mk.comp (continuous_inl.comp
        (K.continuous_toFun.comp (continuous_fst.prodMk
          ((f.continuous.comp s.r.continuous).comp continuous_snd))))⟩
  have hsplit : Continuous (Sum.elim (⇑left) (⇑right) ∘ ⇑e) :=
    (left.continuous.sumElim right.continuous).comp e.continuous
  have heq : Sum.elim (⇑left) (⇑right) ∘ ⇑e = stage2Raw s f K := by
    funext p
    rcases p with ⟨t, z⟩
    cases z with
    | inl x =>
      have hdis : e (t, Sum.inl x) = Sum.inl (t, x) := rfl
      rw [Function.comp_apply, hdis]
      rfl
    | inr d =>
      have hdis : e (t, Sum.inr d) = Sum.inr (t, d) := rfl
      rw [Function.comp_apply, hdis]
      rfl
  exact heq ▸ hsplit

lemma continuous_stage2 {x0 : X}
    (K : Homotopy (ContinuousMap.id X) (ContinuousMap.const X x0)) :
    Continuous fun p : unitInterval × Glue f i =>
      Quot.lift (stage2Val s f K p.1) (stage2_resp s f K p.1) p.2 := by
  refine (isQuotientMap_quot_mk (r := GlueRel (f : A → X) (i : A → D))).continuous_lift_prod_right ?_
  have heq : (fun p : unitInterval × (X ⊕ D) =>
      Quot.lift (stage2Val s f K p.1) (stage2_resp s f K p.1) (Quot.mk _ p.2)) =
      stage2Raw s f K := by
    funext p
    exact Quot.lift_mk (stage2Val s f K p.1) (stage2_resp s f K p.1) p.2
  exact heq ▸ continuous_stage2Raw s f K

/-- Second stage: contract the `X` copy. -/
def stage2Hom {x0 : X} (K : Homotopy (ContinuousMap.id X) (ContinuousMap.const X x0)) :
    Homotopy (squash s f) (ContinuousMap.const (Glue f i) (Quot.mk _ (Sum.inl x0))) where
  toFun p := Quot.lift (stage2Val s f K p.1) (stage2_resp s f K p.1) p.2
  continuous_toFun := continuous_stage2 s f K
  map_zero_left q := by
    refine Quot.induction_on q ?_
    intro z
    rw [Quot.lift_mk (stage2Val s f K 0) (stage2_resp s f K 0)]
    exact stage2_zero s f K z
  map_one_left q := by
    refine Quot.induction_on q ?_
    intro z
    rw [Quot.lift_mk (stage2Val s f K 1) (stage2_resp s f K 1), stage2_one s f K z]
    rfl

/-- The pushout of a contractible space with a disk along a strong deformation retract
is contractible. -/
theorem glue_contractible (s : StrongDeformation i) [ContractibleSpace X] :
    ContractibleSpace (Glue f i) := by
  obtain ⟨x0, hx⟩ := id_nullhomotopic X
  obtain ⟨K⟩ := hx
  refine (contractible_iff_id_nullhomotopic (Glue f i)).2 ?_
  exact ⟨Quot.mk _ (Sum.inl x0),
    ⟨ContinuousMap.Homotopy.trans (stage1Hom s f) (stage2Hom s f K)⟩⟩

/-- Any pushout of the same span is contractible. -/
theorem contractible_pushout (s : StrongDeformation i) [ContractibleSpace X]
    {P : TopCat.{u}} {inl : TopCat.of X ⟶ P} {inr : TopCat.of D ⟶ P}
    (hP : IsPushout (TopCat.ofHom f) (TopCat.ofHom i) inl inr) :
    ContractibleSpace P := by
  have hG := glue_isPushout f i
  have hc : ContractibleSpace (Glue f i) := glue_contractible f s
  exact (TopCat.homeoOfIso (hP.isoIsPushout (X := TopCat.of X) (Y := TopCat.of D) hG)).contractibleSpace

end HomotopyHypothesis.Realization.Disk
