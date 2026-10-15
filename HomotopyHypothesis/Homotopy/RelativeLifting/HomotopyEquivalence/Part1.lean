import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.RelativeFiniteCellComplexHomotopyExtension
import HomotopyHypothesis.Blueprint.Henry.Topology

/-!
# `HomotopyHypothesis.Homotopy.RelativeLifting.HomotopyEquivalence`, part 1

Lines 11–834 of `HomotopyHypothesis.Homotopy.RelativeLifting.HomotopyEquivalence`, split so that the modules of the development form an acyclic import graph.
-/

universe u

open CategoryTheory Limits HomotopicalAlgebra TopCat

namespace HomotopyHypothesis.Homotopy.RelativeLifting

noncomputable section

private def homotopyFamily {A Y : TopCat.{u}} {f g : A ⟶ Y}
    (H : f.hom.Homotopy g.hom) : A ⟶ TopCat.of C(unitInterval, Y) :=
  TopCat.ofHom <| ContinuousMap.curry (H.toContinuousMap.comp ContinuousMap.prodSwap)

private def constantPathFamily {A Y : TopCat.{u}} (f : A ⟶ Y) :
    A ⟶ TopCat.of C(unitInterval, Y) :=
  TopCat.ofHom <| ContinuousMap.curry (f.hom.comp ContinuousMap.fst)

private def homotopyExtend {A Y : TopCat.{u}} {f g : C(A, Y)}
    (H : f.Homotopy g) : C(ℝ × A, Y) := by
  let proj : C(ℝ, unitInterval) := ContinuousMap.projIccCM
  exact H.toContinuousMap.comp ((proj.comp ContinuousMap.fst).prodMk ContinuousMap.snd)

private theorem homotopyExtend_apply {A Y : TopCat.{u}} {f g : C(A, Y)}
    (H : f.Homotopy g) (t : unitInterval) (a : A) :
    homotopyExtend H ((t : ℝ), a) = H (t, a) := by
  simp [homotopyExtend, ContinuousMap.projIccCM]

private theorem homotopyExtend_apply_of_mem {A Y : TopCat.{u}} {f g : C(A, Y)}
    (H : f.Homotopy g) (t : ℝ) (ht : t ∈ unitInterval) (a : A) :
    homotopyExtend H (t, a) = H (⟨t, ht⟩, a) := by
  change H (Set.projIcc 0 1 (by norm_num : (0 : ℝ) ≤ 1) t, a) = H (⟨t, ht⟩, a)
  rw [Set.projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) ht]

private theorem homotopyExtend_zero {A Y : TopCat.{u}} {f g : C(A, Y)}
    (H : f.Homotopy g) (a : A) : homotopyExtend H (0, a) = f a := by
  simpa using homotopyExtend_apply H (0 : unitInterval) a

private theorem homotopyExtend_one {A Y : TopCat.{u}} {f g : C(A, Y)}
    (H : f.Homotopy g) (a : A) : homotopyExtend H (1, a) = g a := by
  simpa using homotopyExtend_apply H (1 : unitInterval) a

private def cancelWaitMap {A Y : TopCat.{u}} {f g : C(A, Y)}
    (H : f.Homotopy g) : C((unitInterval × A) × unitInterval, Y) := {
  toFun := fun x =>
    if (x.2 : ℝ) ≤ 1 / 2 then
      homotopyExtend H (1 - (1 - (x.1.1 : ℝ)) * 2 * (x.2 : ℝ), x.1.2)
    else if (x.2 : ℝ) ≤ 3 / 4 then
      homotopyExtend H ((x.1.1 : ℝ), x.1.2)
    else
      homotopyExtend H ((x.1.1 : ℝ) + (1 - (x.1.1 : ℝ)) * (4 * (x.2 : ℝ) - 3), x.1.2)
  continuous_toFun := by
    have h₁ : Continuous (fun x : (unitInterval × A) × unitInterval =>
        homotopyExtend H (1 - (1 - (x.1.1 : ℝ)) * 2 * (x.2 : ℝ), x.1.2)) := by fun_prop
    have h₂ : Continuous (fun x : (unitInterval × A) × unitInterval =>
        homotopyExtend H ((x.1.1 : ℝ), x.1.2)) := by fun_prop
    have h₃ : Continuous (fun x : (unitInterval × A) × unitInterval =>
        homotopyExtend H ((x.1.1 : ℝ) + (1 - (x.1.1 : ℝ)) * (4 * (x.2 : ℝ) - 3), x.1.2)) := by
      fun_prop
    have h₄ : Continuous (fun x : (unitInterval × A) × unitInterval =>
        if (x.2 : ℝ) ≤ 3 / 4 then
          homotopyExtend H ((x.1.1 : ℝ), x.1.2)
        else
          homotopyExtend H ((x.1.1 : ℝ) + (1 - (x.1.1 : ℝ)) * (4 * (x.2 : ℝ) - 3), x.1.2)) := by
      apply continuous_if_le (by fun_prop) (by fun_prop) h₂.continuousOn h₃.continuousOn
      intro x hx
      have ht : (x.2 : ℝ) = 3 / 4 := hx
      have harg : (x.1.1 : ℝ) =
          (x.1.1 : ℝ) + (1 - (x.1.1 : ℝ)) * (4 * (x.2 : ℝ) - 3) := by
        rw [ht]
        ring
      exact congrArg (fun r : ℝ => homotopyExtend H (r, x.1.2)) harg
    apply continuous_if_le (by fun_prop) (by fun_prop) h₁.continuousOn h₄.continuousOn
    intro x hx
    have ht : (x.2 : ℝ) = 1 / 2 := hx
    simp only [ht]
    norm_num
    have harg : 1 - (1 - (x.1.1 : ℝ)) * 2 * (1 / 2) = (x.1.1 : ℝ) := by ring
    exact congrArg (fun r : ℝ => homotopyExtend H (r, x.1.2)) harg
}

private def cancelWaitTrack {A Y : TopCat.{u}} {f g : C(A, Y)}
    (H : f.Homotopy g) :
    (homotopyFamily (H.symm.trans ((ContinuousMap.Homotopy.refl f).trans H))).hom.Homotopy
      (constantPathFamily (TopCat.ofHom g)).hom := by
  let K := cancelWaitMap H
  let Kc : C(unitInterval × A, C(unitInterval, Y)) := K.curry
  refine {
    toFun := Kc
    continuous_toFun := Kc.continuous
    map_zero_left := ?_
    map_one_left := ?_ }
  · intro a
    apply ContinuousMap.ext
    intro t
    let B := H.symm.trans ((ContinuousMap.Homotopy.refl f).trans H)
    change K.curry (0, a) t = ContinuousMap.curry
      (B.toContinuousMap.comp ContinuousMap.prodSwap) a t
    rw [ContinuousMap.curry_apply, ContinuousMap.curry_apply]
    change K.toFun ((0, a), t) = B (t, a)
    simp only [K, cancelWaitMap]
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · have h₂t : 2 * (t : ℝ) ∈ unitInterval :=
        (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨unitInterval.nonneg t, ht⟩
      have h₁ : 1 - 2 * (t : ℝ) ∈ unitInterval := by
        have hsymm : (unitInterval.symm ⟨2 * (t : ℝ), h₂t⟩ : ℝ) = 1 - 2 * (t : ℝ) := by
          simp [unitInterval.symm]
        rw [← hsymm]
        exact (unitInterval.symm ⟨2 * (t : ℝ), h₂t⟩).property
      have htme : (⟨1 - 2 * (t : ℝ), h₁⟩ : unitInterval) =
          unitInterval.symm ⟨2 * (t : ℝ), h₂t⟩ := by
        apply Subtype.ext
        simp [unitInterval.symm]
      rw [if_pos ht]
      norm_num
      rw [homotopyExtend_apply_of_mem H _ h₁]
      have htR : (t : ℝ) ≤ 2⁻¹ := by simpa using ht
      simp [B, ContinuousMap.Homotopy.trans_apply, htR, htme,
        ContinuousMap.Homotopy.symm]
      rfl
    · by_cases ht' : (t : ℝ) ≤ 3 / 4
      · have hmid : 2 * (t : ℝ) - 1 ≤ 1 / 2 := by linarith
        rw [if_neg ht, if_pos ht']
        norm_num
        rw [homotopyExtend_zero H a]
        have htR : ¬ (t : ℝ) ≤ 2⁻¹ := by simpa using ht
        have hmidR : 2 * (t : ℝ) - 1 ≤ 2⁻¹ := by simpa using hmid
        simp [B, ContinuousMap.Homotopy.trans_apply, htR, hmidR]
      · have hq : 2 * (t : ℝ) - 1 ∈ Set.Icc (1 / 2 : ℝ) 1 := by
          constructor <;> linarith [unitInterval.le_one t, ht']
        have h₂ : 4 * (t : ℝ) - 3 ∈ unitInterval := by
          have hh := (unitInterval.two_mul_sub_one_mem_iff
            (t := 2 * (t : ℝ) - 1)).2 hq
          simpa only [show 2 * (2 * (t : ℝ) - 1) - 1 = 4 * (t : ℝ) - 3 by ring] using hh
        rw [if_neg ht, if_neg ht']
        norm_num
        rw [homotopyExtend_apply_of_mem H _ h₂]
        have htR : ¬ (t : ℝ) ≤ 2⁻¹ := by simpa using ht
        have hmidR : ¬ (2 * (t : ℝ) - 1 ≤ 2⁻¹) := by linarith
        simp [B, ContinuousMap.Homotopy.trans_apply, htR, hmidR]
        apply congrArg (fun s : unitInterval => H (s, a))
        apply Subtype.ext
        ring
  · intro a
    apply ContinuousMap.ext
    intro t
    change K.toFun ((1, a), t) = g a
    simp [K, cancelWaitMap, homotopyExtend_one]

private theorem cancelWaitTrack_eval_zero {A Y : TopCat.{u}} {f g : C(A, Y)}
    (H : f.Homotopy g) (s : unitInterval) (a : A) :
    (cancelWaitTrack H) (s, a) 0 = g a := by
  change cancelWaitMap H ((s, a), 0) = g a
  simp [cancelWaitMap, homotopyExtend_one]

private theorem cancelWaitTrack_eval_one {A Y : TopCat.{u}} {f g : C(A, Y)}
    (H : f.Homotopy g) (s : unitInterval) (a : A) :
    (cancelWaitTrack H) (s, a) 1 = g a := by
  change cancelWaitMap H ((s, a), 1) = g a
  simp only [cancelWaitMap]
  norm_num
  exact homotopyExtend_one H a

private theorem cancelWaitTrack_at_one {A Y : TopCat.{u}} {f g : C(A, Y)}
    (H : f.Homotopy g) (a : A) (t : unitInterval) :
    (cancelWaitTrack H) (1, a) t = g a := by
  change cancelWaitMap H ((1, a), t) = g a
  simp [cancelWaitMap, homotopyExtend_one]

private def evalPathFamily {B Y : TopCat.{u}}
    (F : B ⟶ TopCat.of C(unitInterval, Y)) (t : unitInterval) : B ⟶ Y :=
  TopCat.ofHom {
    toFun := fun b => F.hom b t
    continuous_toFun := by fun_prop
  }

private def evalOuterHomotopy {B Y : TopCat.{u}}
    {F G : B ⟶ TopCat.of C(unitInterval, Y)}
    (E : F.hom.Homotopy G.hom) (t : unitInterval) :
    (evalPathFamily F t).hom.Homotopy (evalPathFamily G t).hom := by
  let ev : C(C(unitInterval, Y), Y) := {
    toFun := fun p => p t
    continuous_toFun := by fun_prop
  }
  refine {
    toFun := fun x => E (x.1, x.2) t
    continuous_toFun := (ev.comp E.toContinuousMap).continuous
    map_zero_left := ?_
    map_one_left := ?_
  }
  · intro b
    change E (0, b) t = F.hom b t
    simp
  · intro b
    change E (1, b) t = G.hom b t
    simp

private def pathFamilyHomotopy {B Y : TopCat.{u}}
    (F : B ⟶ TopCat.of C(unitInterval, Y)) :
    (evalPathFamily F 0).hom.Homotopy (evalPathFamily F 1).hom := {
  toFun := fun x => F.hom.uncurry (x.2, x.1)
  continuous_toFun := (F.hom.uncurry).continuous.comp ContinuousMap.prodSwap.continuous
  map_zero_left := by intro b; rfl
  map_one_left := by intro b; rfl
}

private theorem homotopicRelOfRange {A B Y : TopCat.{u}} (i : A ⟶ B)
    {f g : C(B, Y)} (H : f.Homotopy g)
    (h : ∀ (t : unitInterval) (a : A), H (t, i.hom a) = f (i.hom a)) :
    f.HomotopicRel g (Set.range i.hom) := by
  refine ⟨{ toHomotopy := H, prop' := ?_ }⟩
  intro t x hx
  rcases hx with ⟨a, rfl⟩
  exact h t a

private theorem homotopicRel_of_backtrack {A B Y : TopCat.{u}} (i : A ⟶ B)
    (hi : HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes i)
    {f g : C(B, Y)} {u v : C(A, Y)}
    (hfi : f.comp i.hom = v) (hgi : g.comp i.hom = v)
    (α : u.Homotopy v) (H : f.Homotopy g)
    (htrack : ∀ (s : unitInterval) (a : A),
      H (s, i.hom a) = (α.symm.trans ((ContinuousMap.Homotopy.refl u).trans α)) (s, a)) :
    f.HomotopicRel g (Set.range i.hom) := by
  let fArrow : B ⟶ Y := TopCat.ofHom f
  let gArrow : B ⟶ Y := TopCat.ofHom g
  let uArrow : A ⟶ Y := TopCat.ofHom u
  let vArrow : A ⟶ Y := TopCat.ofHom v
  let Back := α.symm.trans ((ContinuousMap.Homotopy.refl u).trans α)
  let F : B ⟶ TopCat.of C(unitInterval, Y) := homotopyFamily H
  let Fb : A ⟶ TopCat.of C(unitInterval, Y) := homotopyFamily Back
  let G : A ⟶ TopCat.of C(unitInterval, Y) := constantPathFamily vArrow
  have hF : (F.hom.comp i.hom) = Fb.hom := by
    apply ContinuousMap.ext
    intro a
    apply ContinuousMap.ext
    intro s
    change H (s, i.hom a) = Back (s, a)
    exact htrack s a
  let hstart : (F.hom.comp i.hom).Homotopy G.hom :=
    (cancelWaitTrack α).cast hF.symm rfl
  obtain ⟨q, E, Efix⟩ :=
    HomotopyHypothesis.Henry.Packages.relativeFiniteCellComplex_homotopyExtension
      i hi F.hom G.hom hstart
  let Q : B ⟶ TopCat.of C(unitInterval, Y) := TopCat.ofHom q
  let F₀ := evalPathFamily F 0
  let F₁ := evalPathFamily F 1
  let Q₀ := evalPathFamily Q 0
  let Q₁ := evalPathFamily Q 1
  have hF₀ : F₀.hom = f := by
    ext b
    simp [F₀, F, evalPathFamily, homotopyFamily, ContinuousMap.curry_apply]
  have hF₁ : F₁.hom = g := by
    ext b
    simp [F₁, F, evalPathFamily, homotopyFamily, ContinuousMap.curry_apply]
  let E₀ := (evalOuterHomotopy E 0).cast hF₀ rfl
  let E₁ := (evalOuterHomotopy E 1).cast hF₁ rfl
  have hE₀ : f.HomotopicRel Q₀.hom (Set.range i.hom) := by
    apply homotopicRelOfRange i E₀
    intro s a
    have he := congrArg (fun p : C(unitInterval, Y) => p 0) (Efix s a)
    have hstart0 : hstart (s, a) 0 = v a := by
      have hcast : hstart (s, a) = cancelWaitTrack α (s, a) := rfl
      rw [hcast]
      exact cancelWaitTrack_eval_zero α s a
    calc
      E₀ (s, i.hom a) = E (s, i.hom a) 0 := rfl
      _ = hstart (s, a) 0 := he
      _ = v a := hstart0
      _ = f (i.hom a) := (congrArg (fun m : C(A, Y) => m a) hfi).symm
  have hE₁ : g.HomotopicRel Q₁.hom (Set.range i.hom) := by
    apply homotopicRelOfRange i E₁
    intro s a
    have he := congrArg (fun p : C(unitInterval, Y) => p 1) (Efix s a)
    have hstart1 : hstart (s, a) 1 = v a := by
      have hcast : hstart (s, a) = cancelWaitTrack α (s, a) := rfl
      rw [hcast]
      exact cancelWaitTrack_eval_one α s a
    calc
      E₁ (s, i.hom a) = E (s, i.hom a) 1 := rfl
      _ = hstart (s, a) 1 := he
      _ = v a := hstart1
      _ = g (i.hom a) := (congrArg (fun m : C(A, Y) => m a) hgi).symm
  have hQboundary : ∀ (a : A) (t : unitInterval), q (i.hom a) t = v a := by
    intro a t
    have he := congrArg (fun p : C(unitInterval, Y) => p t) (Efix 1 a)
    have hstart1 : hstart (1, a) t = v a := by
      have hcast : hstart (1, a) = cancelWaitTrack α (1, a) := rfl
      rw [hcast]
      exact cancelWaitTrack_at_one α a t
    calc
      q (i.hom a) t = E (1, i.hom a) t := by simp
      _ = hstart (1, a) t := he
      _ = v a := hstart1
  have hmiddle : Q₀.hom.HomotopicRel Q₁.hom (Set.range i.hom) := by
    apply homotopicRelOfRange i (pathFamilyHomotopy Q)
    intro s a
    calc
      (pathFamilyHomotopy Q) (s, i.hom a) = q (i.hom a) s := rfl
      _ = v a := hQboundary a s
      _ = q (i.hom a) 0 := (hQboundary a 0).symm
      _ = Q₀.hom (i.hom a) := rfl
  exact hE₀.trans (hmiddle.trans hE₁.symm)

private def Extension {A B Y : TopCat.{u}} (i : A ⟶ B) (a : C(A, Y)) :=
  { l : C(B, Y) // l.comp i.hom = a }

private def extensionRel {A B Y : TopCat.{u}} (i : A ⟶ B) (a : C(A, Y)) :
    Extension i a → Extension i a → Prop :=
  fun l l' => l.val.HomotopicRel l'.val (Set.range i.hom)

private def extensionSetoid {A B Y : TopCat.{u}} (i : A ⟶ B) (a : C(A, Y)) :
    Setoid (Extension i a) where
  r := extensionRel i a
  iseqv := by
    constructor
    · intro l
      exact ContinuousMap.HomotopicRel.refl l.val
    · intro l l' h
      exact h.symm
    · intro l l' l'' h₁ h₂
      exact h₁.trans h₂

private abbrev ExtensionClass {A B Y : TopCat.{u}} (i : A ⟶ B) (a : C(A, Y)) :=
  Quotient (extensionSetoid i a)

private def castExtension {A B Y : TopCat.{u}} {i : A ⟶ B}
    {a b : C(A, Y)} (h : a = b) (x : Extension i a) : Extension i b :=
  ⟨x.val, x.property.trans h⟩

private def extensionCast {A B Y : TopCat.{u}} {i : A ⟶ B}
    {a b : C(A, Y)} (h : a = b) : ExtensionClass i a → ExtensionClass i b :=
  Quotient.map (castExtension h) (by
    intro x y hxy
    exact hxy)

private theorem extensionCast_cancel {A B Y : TopCat.{u}} {i : A ⟶ B}
    {a b : C(A, Y)} (h : a = b) (x : ExtensionClass i a) :
    extensionCast h.symm (extensionCast h x) = x := by
  refine Quotient.inductionOn x ?_
  intro e
  apply Quotient.sound
  exact ContinuousMap.HomotopicRel.refl e.val

private theorem extensionCast_rfl {A B Y : TopCat.{u}} {i : A ⟶ B}
    {a : C(A, Y)} (x : ExtensionClass i a) : extensionCast rfl x = x := by
  refine Quotient.inductionOn x ?_
  intro e
  apply Quotient.sound
  exact ContinuousMap.HomotopicRel.refl e.val

private theorem extensionCast_bijective {A B Y : TopCat.{u}} {i : A ⟶ B}
    {a b : C(A, Y)} (h : a = b) :
    Function.Bijective (@extensionCast A B Y i a b h) := by
  constructor
  · intro x y hxy
    have h' := congrArg (extensionCast h.symm) hxy
    simpa [extensionCast_cancel] using h'
  · intro y
    refine ⟨extensionCast h.symm y, ?_⟩
    simpa using extensionCast_cancel h.symm y

private def hasTrack {A B Y : TopCat.{u}} (i : A ⟶ B) {a b : C(A, Y)}
    (α : a.Homotopy b) (x : Extension i a) (y : Extension i b) : Prop :=
  ∃ H : x.val.Homotopy y.val,
    ∀ (s : unitInterval) (z : A), H (s, i.hom z) = α (s, z)

private theorem exists_track {A B Y : TopCat.{u}} (i : A ⟶ B)
    (hi : HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes i)
    {a b : C(A, Y)} (α : a.Homotopy b) (x : Extension i a) :
    ∃ y : Extension i b, hasTrack i α x y := by
  have hxi : x.val.comp i.hom = a := x.property
  let α' : (x.val.comp i.hom).Homotopy b := α.cast hxi.symm rfl
  obtain ⟨l, H, hboundary⟩ :=
    HomotopyHypothesis.Henry.Packages.relativeFiniteCellComplex_homotopyExtension
      i hi x.val b α'
  have hl : l.comp i.hom = b := by
    ext z
    calc
      l (i.hom z) = H (1, i.hom z) := (H.apply_one _).symm
      _ = α' (1, z) := hboundary 1 z
      _ = b z := by simp [α']
  refine ⟨⟨l, hl⟩, H, ?_⟩
  intro s z
  have hα' : α' (s, z) = α (s, z) := rfl
  exact (hboundary s z).trans hα'

private theorem track_outputs_rel {A B Y : TopCat.{u}} (i : A ⟶ B)
    (hi : HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes i)
    {a b : C(A, Y)} (α : a.Homotopy b)
    {x x' : Extension i a} {y y' : Extension i b}
    (hxx : extensionRel i a x x')
    (H : x.val.Homotopy y.val)
    (hH : ∀ (s : unitInterval) (z : A), H (s, i.hom z) = α (s, z))
    (H' : x'.val.Homotopy y'.val)
    (hH' : ∀ (s : unitInterval) (z : A), H' (s, i.hom z) = α (s, z)) :
    extensionRel i b y y' := by
  rcases hxx with ⟨K⟩
  let Hback : y.val.Homotopy y'.val := H.symm.trans (K.toHomotopy.trans H')
  have hconst : ∀ (s : unitInterval) (z : A), K.toHomotopy (s, i.hom z) = a z := by
    intro s z
    calc
      K.toHomotopy (s, i.hom z) = x.val (i.hom z) := K.prop' s _ ⟨z, rfl⟩
      _ = a z := by
        have hx := congrArg (fun m : C(A, Y) => m z) x.property
        exact hx
  have hsymm : ∀ (s : unitInterval) (z : A),
      H.symm (s, i.hom z) = α.symm (s, z) := by
    intro s z
    change H (unitInterval.symm s, i.hom z) = α (unitInterval.symm s, z)
    exact hH (unitInterval.symm s) z
  exact homotopicRel_of_backtrack i hi y.property y'.property α Hback (by
    intro s z
    by_cases hs : (s : ℝ) ≤ 1 / 2
    · have hsR : (s : ℝ) ≤ 2⁻¹ := by simpa using hs
      simp [Hback, ContinuousMap.Homotopy.trans_apply, hsR, hsymm]
    · by_cases hs' : 2 * (s : ℝ) - 1 ≤ 1 / 2
      · have hsR : ¬ (s : ℝ) ≤ 2⁻¹ := by simpa using hs
        have hs'R : 2 * (s : ℝ) - 1 ≤ 2⁻¹ := by simpa using hs'
        simp [Hback, ContinuousMap.Homotopy.trans_apply, hsR, hs'R, hconst, hH']
      · have hsR : ¬ (s : ℝ) ≤ 2⁻¹ := by simpa using hs
        have hs'R : ¬ (2 * (s : ℝ) - 1 ≤ 2⁻¹) := by simpa using hs'
        simp [Hback, ContinuousMap.Homotopy.trans_apply, hsR, hs'R, hconst, hH'])

private noncomputable def chooseTrack {A B Y : TopCat.{u}} (i : A ⟶ B)
    (hi : HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes i)
    {a b : C(A, Y)} (α : a.Homotopy b) (x : Extension i a) : Extension i b :=
  Classical.choose (exists_track i hi α x)

private theorem chooseTrack_hasTrack {A B Y : TopCat.{u}} (i : A ⟶ B)
    (hi : HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes i)
    {a b : C(A, Y)} (α : a.Homotopy b) (x : Extension i a) :
    hasTrack i α x (chooseTrack i hi α x) :=
  Classical.choose_spec (exists_track i hi α x)

private noncomputable def extensionTransport {A B Y : TopCat.{u}} (i : A ⟶ B)
    (hi : HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes i)
    {a b : C(A, Y)} (α : a.Homotopy b) :
    ExtensionClass i a → ExtensionClass i b :=
  Quotient.lift
    (fun x => Quotient.mk (extensionSetoid i b) (chooseTrack i hi α x))
    (by
      intro x x' hxx
      obtain ⟨H, hH⟩ := chooseTrack_hasTrack i hi α x
      obtain ⟨H', hH'⟩ := chooseTrack_hasTrack i hi α x'
      exact Quotient.sound (track_outputs_rel i hi α hxx H hH H' hH'))

private theorem extensionTransport_cast {A B Y : TopCat.{u}} (i : A ⟶ B)
    (hi : HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes i)
    {a a' b b' : C(A, Y)} (α : a.Homotopy b) (h₀ : a = a') (h₁ : b = b')
    (x : ExtensionClass i a) :
    extensionTransport i hi (α.cast h₀ h₁) (extensionCast h₀ x) =
      extensionCast h₁ (extensionTransport i hi α x) := by
  refine Quotient.inductionOn x ?_
  intro e
  let e' := castExtension h₀ e
  let y := chooseTrack i hi α e
  let y' := chooseTrack i hi (α.cast h₀ h₁) e'
  obtain ⟨H, hH⟩ := chooseTrack_hasTrack i hi α e
  obtain ⟨H', hH'⟩ := chooseTrack_hasTrack i hi (α.cast h₀ h₁) e'
  change Quotient.mk (extensionSetoid i b') y' =
    Quotient.mk (extensionSetoid i b') (castExtension h₁ y)
  apply Quotient.sound
  exact track_outputs_rel i hi (α.cast h₀ h₁)
    (ContinuousMap.HomotopicRel.refl e'.val) H' hH' H (by
      intro s z
      change H (s, i.hom z) = α (s, z)
      exact hH s z)

private theorem extensionTransport_symm_left {A B Y : TopCat.{u}} (i : A ⟶ B)
    (hi : HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes i)
    {a b : C(A, Y)} (α : a.Homotopy b) (x : Extension i a) :
    extensionTransport i hi α.symm (extensionTransport i hi α
      (Quotient.mk (extensionSetoid i a) x)) = Quotient.mk (extensionSetoid i a) x := by
  change Quotient.mk (extensionSetoid i a)
      (chooseTrack i hi α.symm (chooseTrack i hi α x)) =
    Quotient.mk (extensionSetoid i a) x
  apply Quotient.sound
  let y := chooseTrack i hi α x
  obtain ⟨H, hH⟩ := chooseTrack_hasTrack i hi α x
  obtain ⟨H', hH'⟩ := chooseTrack_hasTrack i hi α.symm y
  have hHsymm : ∀ (s : unitInterval) (z : A),
      H.symm (s, i.hom z) = α.symm (s, z) := by
    intro s z
    change H (unitInterval.symm s, i.hom z) = α (unitInterval.symm s, z)
    exact hH (unitInterval.symm s) z
  exact track_outputs_rel i hi α.symm
    (ContinuousMap.HomotopicRel.refl y.val) H' hH' H.symm hHsymm

private theorem extensionTransport_symm_left_class {A B Y : TopCat.{u}} (i : A ⟶ B)
    (hi : HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes i)
    {a b : C(A, Y)} (α : a.Homotopy b) (x : ExtensionClass i a) :
    extensionTransport i hi α.symm (extensionTransport i hi α x) = x := by
  refine Quotient.inductionOn x ?_
  intro x
  exact extensionTransport_symm_left i hi α x

private theorem extensionTransport_bijective {A B Y : TopCat.{u}} (i : A ⟶ B)
    (hi : HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes i)
    {a b : C(A, Y)} (α : a.Homotopy b) :
    Function.Bijective (extensionTransport i hi α) := by
  constructor
  · intro x y h
    have h' := congrArg (extensionTransport i hi α.symm) h
    rw [extensionTransport_symm_left_class i hi α x,
      extensionTransport_symm_left_class i hi α y] at h'
    exact h'
  · intro y
    refine ⟨extensionTransport i hi α.symm y, ?_⟩
    simpa using extensionTransport_symm_left_class i hi α.symm y

private def postcomposeExtension {A B Y Z : TopCat.{u}} (i : A ⟶ B)
    (a : C(A, Y)) (φ : C(Y, Z)) :
    Extension i a → Extension i (φ.comp a) := fun x =>
  ⟨φ.comp x.val, by
    ext z
    change φ (x.val (i.hom z)) = φ (a z)
    exact congrArg φ (congrArg (fun m : C(A, Y) => m z) x.property)⟩

private def postcomposeExtensionClass {A B Y Z : TopCat.{u}} (i : A ⟶ B)
    (a : C(A, Y)) (φ : C(Y, Z)) :
    ExtensionClass i a → ExtensionClass i (φ.comp a) :=
  Quotient.map (postcomposeExtension i a φ) (by
    intro x y h
    exact h.comp_continuousMap φ)

private theorem extensionCast_postcompose {A B Y Z : TopCat.{u}} {i : A ⟶ B}
    {a b : C(A, Y)} (h : a = b) (φ : C(Y, Z)) (x : ExtensionClass i a) :
    postcomposeExtensionClass i b φ (extensionCast h x) =
      extensionCast (congrArg (fun c : C(A, Y) => φ.comp c) h)
        (postcomposeExtensionClass i a φ x) := by
  refine Quotient.inductionOn x ?_
  intro e
  apply congrArg (Quotient.mk (extensionSetoid i (φ.comp b)))
  apply Subtype.ext
  rfl

private theorem extensionCast_postcompose_id {A B Y : TopCat.{u}} {i : A ⟶ B}
    (a : C(A, Y)) (x : ExtensionClass i a) :
    extensionCast (ContinuousMap.id_comp a)
      (postcomposeExtensionClass i a (ContinuousMap.id Y) x) = x := by
  refine Quotient.inductionOn x ?_
  intro e
  apply Quotient.sound
  exact ContinuousMap.HomotopicRel.refl e.val

private theorem extensionTransport_postcompose {A B Y : TopCat.{u}} (i : A ⟶ B)
    (hi : HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes i)
    (a : C(A, Y)) {f g : C(Y, Y)} (H : f.Homotopy g) (x : Extension i a) :
    extensionTransport i hi (H.comp (ContinuousMap.Homotopy.refl a))
      (Quotient.mk (extensionSetoid i (f.comp a)) (postcomposeExtension i a f x)) =
    Quotient.mk (extensionSetoid i (g.comp a)) (postcomposeExtension i a g x) := by
  let α := H.comp (ContinuousMap.Homotopy.refl a)
  let xF := postcomposeExtension i a f x
  let xG := postcomposeExtension i a g x
  change Quotient.mk (extensionSetoid i (g.comp a))
      (chooseTrack i hi α xF) = Quotient.mk (extensionSetoid i (g.comp a)) xG
  apply Quotient.sound
  obtain ⟨Hchosen, hchosen⟩ := chooseTrack_hasTrack i hi α xF
  let Hx := H.comp (ContinuousMap.Homotopy.refl x.val)
  have hHx : ∀ (s : unitInterval) (z : A),
      Hx (s, i.hom z) = α (s, z) := by
    intro s z
    change H (s, x.val (i.hom z)) = H (s, a z)
    exact congrArg (fun w : Y => H (s, w))
      (congrArg (fun m : C(A, Y) => m z) x.property)
  exact track_outputs_rel i hi α
    (ContinuousMap.HomotopicRel.refl xF.val) Hchosen hchosen Hx hHx

private theorem extensionTransport_natural_postcompose {A B Y Z : TopCat.{u}}
    (i : A ⟶ B) (hi : HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes i)
    {a b : C(A, Y)} (α : a.Homotopy b) (φ : C(Y, Z))
    (x : ExtensionClass i a) :
    postcomposeExtensionClass i b φ (extensionTransport i hi α x) =
      extensionTransport i hi ((ContinuousMap.Homotopy.refl φ).comp α)
        (postcomposeExtensionClass i a φ x) := by
  refine Quotient.inductionOn x ?_
  intro e
  let αf := (ContinuousMap.Homotopy.refl φ).comp α
  let eφ := postcomposeExtension i a φ e
  obtain ⟨H, hH⟩ := chooseTrack_hasTrack i hi α e
  let Hφ := (ContinuousMap.Homotopy.refl φ).comp H
  have hHφ : ∀ (s : unitInterval) (z : A),
      Hφ (s, i.hom z) = αf (s, z) := by
    intro s z
    change φ (H (s, i.hom z)) = φ (α (s, z))
    exact congrArg φ (hH s z)
  obtain ⟨Hc, hHc⟩ := chooseTrack_hasTrack i hi αf eφ
  change Quotient.mk (extensionSetoid i (φ.comp b))
      (postcomposeExtension i b φ (chooseTrack i hi α e)) =
    Quotient.mk (extensionSetoid i (φ.comp b))
      (chooseTrack i hi αf eφ)
  apply Quotient.sound
  exact track_outputs_rel i hi αf
    (ContinuousMap.HomotopicRel.refl eφ.val) Hφ hHφ Hc hHc

private theorem postcomposeExtensionClass_comp {A B Y Z W : TopCat.{u}}
    (i : A ⟶ B) (a : C(A, Y)) (φ : C(Y, Z)) (ψ : C(Z, W))
    (x : ExtensionClass i a) :
    postcomposeExtensionClass i (φ.comp a) ψ
      (postcomposeExtensionClass i a φ x) =
    postcomposeExtensionClass i a (ψ.comp φ) x := by
  refine Quotient.inductionOn x ?_
  intro e
  apply congrArg (Quotient.mk (extensionSetoid i (ψ.comp (φ.comp a))))
  apply Subtype.ext
  ext b
  simp [postcomposeExtension, ContinuousMap.comp_assoc]

private theorem postcomposeExtensionClass_id {A B Y : TopCat.{u}}
    (i : A ⟶ B) (a : C(A, Y)) (x : ExtensionClass i a) :
    postcomposeExtensionClass i a (ContinuousMap.id Y) x = x := by
  refine Quotient.inductionOn x ?_
  intro e
  apply congrArg (Quotient.mk (extensionSetoid i a))
  apply Subtype.ext
  ext b
  simp [postcomposeExtension, ContinuousMap.id_comp]

private theorem bijective_of_leftInverse_after_bijective {X Y : Sort*}
    (T : Y → X) (P : X → Y) (hT : Function.Bijective T)
    (hTP : ∀ x, T (P x) = x) : Function.Bijective P := by
  constructor
  · intro x x' h
    calc
      x = T (P x) := (hTP x).symm
      _ = T (P x') := congrArg T h
      _ = x' := hTP x'
  · intro y
    refine ⟨T y, ?_⟩
    apply hT.1
    calc
      T (P (T y)) = T y := hTP (T y)
      _ = T y := rfl

private theorem bijective_of_leftInverse_and_comp_surjective {X Y : Sort*}
    (P : X → Y) (G : Y → X) (hGP : ∀ x, G (P x) = x)
    (hPG : Function.Surjective (P ∘ G)) : Function.Bijective P := by
  constructor
  · intro x x' h
    have h' := congrArg G h
    rw [hGP x, hGP x'] at h'
    exact h'
  · intro y
    obtain ⟨y', hy'⟩ := hPG y
    exact ⟨G y', hy'⟩

private theorem postcompose_homotopic_to_id_bijective {A B Y : TopCat.{u}}
    (i : A ⟶ B) (hi : HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes i)
    (a : C(A, Y)) {f : C(Y, Y)} (H : f.Homotopy (ContinuousMap.id Y)) :
    Function.Bijective (postcomposeExtensionClass i a f) := by
  let α := H.comp (ContinuousMap.Homotopy.refl a)
  apply bijective_of_leftInverse_after_bijective
    (extensionTransport i hi α) (postcomposeExtensionClass i a f)
    (extensionTransport_bijective i hi α)
  intro x
  refine Quotient.inductionOn x ?_
  intro e
  change extensionTransport i hi α
    (Quotient.mk (extensionSetoid i (f.comp a)) (postcomposeExtension i a f e)) =
      Quotient.mk (extensionSetoid i a) e
  rw [show α = H.comp (ContinuousMap.Homotopy.refl a) from rfl]
  rw [extensionTransport_postcompose i hi a H e]
  have hid : postcomposeExtension i a (ContinuousMap.id Y) e = e := by
    apply Subtype.ext
    ext b
    simp [postcomposeExtension]
  exact congrArg (Quotient.mk (extensionSetoid i a)) hid

private theorem bijective_of_two_composites {X Y : Sort*} (f : X → Y) (g : Y → X)
    (hgf : Function.Bijective (g ∘ f)) (hfg : Function.Bijective (f ∘ g)) :
    Function.Bijective f := by
  constructor
  · intro x x' h
    apply hgf.1
    exact congrArg g h
  · intro y
    obtain ⟨y', hy'⟩ := hfg.2 y
    exact ⟨g y', hy'⟩

private theorem postcompose_homotopyEquiv_bijective {A B Y Z : TopCat.{u}}
    (i : A ⟶ B) (hi : HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes i)
    (φ : C(Y, Z)) (ψ : C(Z, Y))
    (Hη : (ψ.comp φ).Homotopy (ContinuousMap.id Y))
    (Hε : (φ.comp ψ).Homotopy (ContinuousMap.id Z)) (a : C(A, Y)) :
    Function.Bijective (postcomposeExtensionClass i a φ) := by
  let Pφ := postcomposeExtensionClass i a φ
  let Pψ := postcomposeExtensionClass i (φ.comp a) ψ
  let αηraw := Hη.comp (ContinuousMap.Homotopy.refl a)
  have hAssocY : (ψ.comp φ).comp a = ψ.comp (φ.comp a) :=
    ContinuousMap.comp_assoc ψ φ a
  let αη := αηraw.cast hAssocY rfl
  let hIdY := ContinuousMap.id_comp a
  let G := fun x => extensionCast hIdY (extensionTransport i hi αη (Pψ x))
  let Punit := postcomposeExtensionClass i a (ψ.comp φ)
  have hQP : Pψ ∘ Pφ = fun x => extensionCast hAssocY (Punit x) := by
    funext x
    refine Quotient.inductionOn x ?_
    intro e
    change Quotient.mk (extensionSetoid i (ψ.comp (φ.comp a)))
        (postcomposeExtension i (φ.comp a) ψ (postcomposeExtension i a φ e)) =
      Quotient.mk (extensionSetoid i (ψ.comp (φ.comp a)))
        (castExtension hAssocY (postcomposeExtension i a (ψ.comp φ) e))
    apply congrArg (Quotient.mk (extensionSetoid i (ψ.comp (φ.comp a))))
    apply Subtype.ext
    ext z
    simp [postcomposeExtension, castExtension, ContinuousMap.comp_assoc]
  have hUnitRaw : ∀ x, extensionTransport i hi αηraw (Punit x) =
      postcomposeExtensionClass i a (ContinuousMap.id Y) x := by
    intro x
    refine Quotient.inductionOn x ?_
    intro e
    change extensionTransport i hi αηraw
        (Quotient.mk (extensionSetoid i ((ψ.comp φ).comp a))
          (postcomposeExtension i a (ψ.comp φ) e)) =
      Quotient.mk (extensionSetoid i ((ContinuousMap.id Y).comp a))
        (postcomposeExtension i a (ContinuousMap.id Y) e)
    exact extensionTransport_postcompose i hi a Hη e
  have hGP : ∀ x, G (Pφ x) = x := by
    intro x
    change extensionCast hIdY (extensionTransport i hi αη (Pψ (Pφ x))) = x
    rw [show Pψ (Pφ x) = extensionCast hAssocY (Punit x) from
      (by
        have hx := congrFun hQP x
        simpa [extensionCast] using hx)]
    rw [extensionTransport_cast i hi αηraw hAssocY rfl (Punit x)]
    rw [extensionCast_rfl]
    rw [hUnitRaw x]
    exact extensionCast_postcompose_id a x
  let αηφ := (ContinuousMap.Homotopy.refl φ).comp αη
  let hIdZ := congrArg (fun c : C(A, Y) => φ.comp c) hIdY
  let Tηφraw := extensionTransport i hi αηφ
  let Tηφ := fun x => extensionCast hIdZ (Tηφraw x)
  let Pφψ := postcomposeExtensionClass i (φ.comp a) (φ.comp ψ)
  have hTηφraw : Function.Bijective Tηφraw := extensionTransport_bijective i hi αηφ
  have hCast : Function.Bijective (extensionCast hIdZ) := extensionCast_bijective (i := i) hIdZ
  have hTηφ : Function.Bijective Tηφ := by
    constructor
    · intro x y h
      apply hTηφraw.1
      apply hCast.1 h
    · intro y
      obtain ⟨z, hz⟩ := hCast.2 y
      obtain ⟨x, hx⟩ := hTηφraw.2 z
      refine ⟨x, ?_⟩
      change extensionCast hIdZ (Tηφraw x) = y
      rw [hx, hz]
  have hPφψ : Function.Bijective Pφψ :=
    postcompose_homotopic_to_id_bijective i hi (φ.comp a) Hε
  have hPG : Pφ ∘ G = Tηφ ∘ Pφψ := by
    funext x
    change postcomposeExtensionClass i a φ
        (extensionCast hIdY (extensionTransport i hi αη (Pψ x))) =
      extensionCast hIdZ (Tηφraw (Pφψ x))
    have hNat : postcomposeExtensionClass i ((ContinuousMap.id Y).comp a) φ
        (extensionTransport i hi αη (Pψ x)) =
        Tηφraw (postcomposeExtensionClass i (ψ.comp (φ.comp a)) φ (Pψ x)) := by
      simpa [Pψ, ContinuousMap.comp_assoc] using
        extensionTransport_natural_postcompose i hi αη φ
          (postcomposeExtensionClass i (φ.comp a) ψ x)
    rw [extensionCast_postcompose (i := i) hIdY φ (extensionTransport i hi αη (Pψ x))]
    rw [hNat]
    rw [postcomposeExtensionClass_comp i (φ.comp a) ψ φ x]
  have hPGsurj : Function.Surjective (Pφ ∘ G) := by
    rw [hPG]
    intro y
    obtain ⟨z, hz⟩ := hTηφ.2 y
    obtain ⟨x, hx⟩ := hPφψ.2 z
    refine ⟨x, ?_⟩
    change Tηφ (Pφψ x) = y
    rw [hx, hz]
  exact bijective_of_leftInverse_and_comp_surjective Pφ G hGP hPGsurj

/-- A homotopy equivalence induces a bijection on extensions modulo homotopy relative to a
relative finite cell inclusion. -/
theorem relativeLift_of_homotopyEquivalence_proof
    {A B Y Z : TopCat.{u}} (i : A ⟶ B)
    (hi : HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes i)
    (φ : Y ⟶ Z) (hφ : HomotopyHypothesis.Henry.Top.homotopyEquivalences φ) :
    (∀ (a : A ⟶ Y) (g : B ⟶ Z), a ≫ φ = i ≫ g →
      ∃ l : B ⟶ Y, i ≫ l = a ∧
        (l ≫ φ).hom.HomotopicRel g.hom (Set.range i.hom)) ∧
    ∀ l l' : B ⟶ Y, i ≫ l = i ≫ l' →
      (l ≫ φ).hom.HomotopicRel (l' ≫ φ).hom (Set.range i.hom) →
        l.hom.HomotopicRel l'.hom (Set.range i.hom) := by
  rcases hφ with ⟨ψ, hη, hε⟩
  rcases hη with ⟨Hη⟩
  rcases hε with ⟨Hε⟩
  constructor
  · intro a g hsq
    have hsq' : g.hom.comp i.hom = φ.hom.comp a.hom := by
      have hh := congrArg Hom.hom hsq
      simpa [TopCat.hom_comp] using hh.symm
    let gExt : Extension i (φ.hom.comp a.hom) := ⟨g.hom, hsq'⟩
    have hbij := postcompose_homotopyEquiv_bijective i hi φ.hom ψ.hom Hη Hε a.hom
    obtain ⟨c, hc⟩ := hbij.2 (Quotient.mk (extensionSetoid i (φ.hom.comp a.hom)) gExt)
    obtain ⟨l, hl⟩ := Quotient.mk_surjective c
    have hclass : postcomposeExtensionClass i a.hom φ.hom
        (Quotient.mk (extensionSetoid i a.hom) l) =
        Quotient.mk (extensionSetoid i (φ.hom.comp a.hom)) gExt := by
      calc
        postcomposeExtensionClass i a.hom φ.hom (Quotient.mk (extensionSetoid i a.hom) l) =
            postcomposeExtensionClass i a.hom φ.hom c := congrArg _ hl
        _ = Quotient.mk (extensionSetoid i (φ.hom.comp a.hom)) gExt := hc
    have hrel : extensionRel i (φ.hom.comp a.hom)
        (postcomposeExtension i a.hom φ.hom l) gExt := by
      exact Quotient.exact hclass
    refine ⟨TopCat.ofHom l.val, ?_, ?_⟩
    · apply TopCat.hom_ext
      ext z
      exact congrArg (fun m : C(A, Y) => m z) l.property
    · change (postcomposeExtension i a.hom φ.hom l).val.HomotopicRel gExt.val
        (Set.range i.hom)
      change (postcomposeExtension i a.hom φ.hom l).val.HomotopicRel gExt.val
        (Set.range i.hom) at hrel
      simpa [postcomposeExtension, TopCat.hom_comp, gExt] using hrel
  · intro l l' hll hrel
    let a : C(A, Y) := l.hom.comp i.hom
    have hli : l'.hom.comp i.hom = a := by
      have hh := congrArg Hom.hom hll
      simpa [TopCat.hom_comp, a] using hh.symm
    let x : Extension i a := ⟨l.hom, rfl⟩
    let x' : Extension i a := ⟨l'.hom, hli⟩
    have hbij := postcompose_homotopyEquiv_bijective i hi φ.hom ψ.hom Hη Hε a
    have hclass : postcomposeExtensionClass i a φ.hom
        (Quotient.mk (extensionSetoid i a) x) =
        postcomposeExtensionClass i a φ.hom (Quotient.mk (extensionSetoid i a) x') := by
      have hrel' : extensionRel i (φ.hom.comp a)
          (postcomposeExtension i a φ.hom x) (postcomposeExtension i a φ.hom x') := by
        change (φ.hom.comp l.hom).HomotopicRel (φ.hom.comp l'.hom) (Set.range i.hom)
        simpa [a, TopCat.hom_comp] using hrel
      exact Quotient.sound hrel'
    have hclass' := hbij.1 hclass
    exact Quotient.exact hclass'
