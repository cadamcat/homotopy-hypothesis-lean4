import HomotopyHypothesis.Blueprint.Henry.CompletionRestriction
import HomotopyHypothesis.Blueprint.Henry.Packages.Topology.RelativeFiniteCellComplexHomotopyExtension
import HomotopyHypothesis.Blueprint.Henry.Topology
/-
# Transport of relative extension classes along boundary homotopies

For a relative finite cell complex `i : A ⟶ B` and a map `a : A → Y`, the extensions of `a` along
`i`, modulo homotopy relative to `A`, are transported bijectively along any homotopy `a ≃ a'`, by
the homotopy extension property; the transport is natural in postcomposition. (Brown, *Topology and
Groupoids*, 7.2.) The construction follows the corresponding argument for relative lifts along
homotopy equivalences.
-/
universe u

open CategoryTheory Limits HomotopicalAlgebra TopCat

namespace HomotopyHypothesis.Completion.Compression

noncomputable section

def homotopyFamily {A Y : TopCat.{u}} {f g : A ⟶ Y}
    (H : f.hom.Homotopy g.hom) : A ⟶ TopCat.of C(unitInterval, Y) :=
  TopCat.ofHom <| ContinuousMap.curry (H.toContinuousMap.comp ContinuousMap.prodSwap)

def constantPathFamily {A Y : TopCat.{u}} (f : A ⟶ Y) :
    A ⟶ TopCat.of C(unitInterval, Y) :=
  TopCat.ofHom <| ContinuousMap.curry (f.hom.comp ContinuousMap.fst)

def homotopyExtend {A Y : TopCat.{u}} {f g : C(A, Y)}
    (H : f.Homotopy g) : C(ℝ × A, Y) := by
  let proj : C(ℝ, unitInterval) := ContinuousMap.projIccCM
  exact H.toContinuousMap.comp ((proj.comp ContinuousMap.fst).prodMk ContinuousMap.snd)

theorem homotopyExtend_apply {A Y : TopCat.{u}} {f g : C(A, Y)}
    (H : f.Homotopy g) (t : unitInterval) (a : A) :
    homotopyExtend H ((t : ℝ), a) = H (t, a) := by
  simp [homotopyExtend, ContinuousMap.projIccCM]

theorem homotopyExtend_apply_of_mem {A Y : TopCat.{u}} {f g : C(A, Y)}
    (H : f.Homotopy g) (t : ℝ) (ht : t ∈ unitInterval) (a : A) :
    homotopyExtend H (t, a) = H (⟨t, ht⟩, a) := by
  change H (Set.projIcc 0 1 (by norm_num : (0 : ℝ) ≤ 1) t, a) = H (⟨t, ht⟩, a)
  rw [Set.projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) ht]

theorem homotopyExtend_zero {A Y : TopCat.{u}} {f g : C(A, Y)}
    (H : f.Homotopy g) (a : A) : homotopyExtend H (0, a) = f a := by
  simpa using homotopyExtend_apply H (0 : unitInterval) a

theorem homotopyExtend_one {A Y : TopCat.{u}} {f g : C(A, Y)}
    (H : f.Homotopy g) (a : A) : homotopyExtend H (1, a) = g a := by
  simpa using homotopyExtend_apply H (1 : unitInterval) a

def cancelWaitMap {A Y : TopCat.{u}} {f g : C(A, Y)}
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

def cancelWaitTrack {A Y : TopCat.{u}} {f g : C(A, Y)}
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

theorem cancelWaitTrack_eval_zero {A Y : TopCat.{u}} {f g : C(A, Y)}
    (H : f.Homotopy g) (s : unitInterval) (a : A) :
    (cancelWaitTrack H) (s, a) 0 = g a := by
  change cancelWaitMap H ((s, a), 0) = g a
  simp [cancelWaitMap, homotopyExtend_one]

theorem cancelWaitTrack_eval_one {A Y : TopCat.{u}} {f g : C(A, Y)}
    (H : f.Homotopy g) (s : unitInterval) (a : A) :
    (cancelWaitTrack H) (s, a) 1 = g a := by
  change cancelWaitMap H ((s, a), 1) = g a
  simp only [cancelWaitMap]
  norm_num
  exact homotopyExtend_one H a

theorem cancelWaitTrack_at_one {A Y : TopCat.{u}} {f g : C(A, Y)}
    (H : f.Homotopy g) (a : A) (t : unitInterval) :
    (cancelWaitTrack H) (1, a) t = g a := by
  change cancelWaitMap H ((1, a), t) = g a
  simp [cancelWaitMap, homotopyExtend_one]

def evalPathFamily {B Y : TopCat.{u}}
    (F : B ⟶ TopCat.of C(unitInterval, Y)) (t : unitInterval) : B ⟶ Y :=
  TopCat.ofHom {
    toFun := fun b => F.hom b t
    continuous_toFun := by fun_prop
  }

def evalOuterHomotopy {B Y : TopCat.{u}}
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

def pathFamilyHomotopy {B Y : TopCat.{u}}
    (F : B ⟶ TopCat.of C(unitInterval, Y)) :
    (evalPathFamily F 0).hom.Homotopy (evalPathFamily F 1).hom := {
  toFun := fun x => F.hom.uncurry (x.2, x.1)
  continuous_toFun := (F.hom.uncurry).continuous.comp ContinuousMap.prodSwap.continuous
  map_zero_left := by intro b; rfl
  map_one_left := by intro b; rfl
}

theorem homotopicRelOfRange {A B Y : TopCat.{u}} (i : A ⟶ B)
    {f g : C(B, Y)} (H : f.Homotopy g)
    (h : ∀ (t : unitInterval) (a : A), H (t, i.hom a) = f (i.hom a)) :
    f.HomotopicRel g (Set.range i.hom) := by
  refine ⟨{ toHomotopy := H, prop' := ?_ }⟩
  intro t x hx
  rcases hx with ⟨a, rfl⟩
  exact h t a

theorem homotopicRel_of_backtrack {A B Y : TopCat.{u}} (i : A ⟶ B)
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

def Extension {A B Y : TopCat.{u}} (i : A ⟶ B) (a : C(A, Y)) :=
  { l : C(B, Y) // l.comp i.hom = a }

def extensionRel {A B Y : TopCat.{u}} (i : A ⟶ B) (a : C(A, Y)) :
    Extension i a → Extension i a → Prop :=
  fun l l' => l.val.HomotopicRel l'.val (Set.range i.hom)

def extensionSetoid {A B Y : TopCat.{u}} (i : A ⟶ B) (a : C(A, Y)) :
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

abbrev ExtensionClass {A B Y : TopCat.{u}} (i : A ⟶ B) (a : C(A, Y)) :=
  Quotient (extensionSetoid i a)

def hasTrack {A B Y : TopCat.{u}} (i : A ⟶ B) {a b : C(A, Y)}
    (α : a.Homotopy b) (x : Extension i a) (y : Extension i b) : Prop :=
  ∃ H : x.val.Homotopy y.val,
    ∀ (s : unitInterval) (z : A), H (s, i.hom z) = α (s, z)

theorem exists_track {A B Y : TopCat.{u}} (i : A ⟶ B)
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

theorem track_outputs_rel {A B Y : TopCat.{u}} (i : A ⟶ B)
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
        simp [Hback, ContinuousMap.Homotopy.trans_apply, hsR, hs'R, hH'])

noncomputable def chooseTrack {A B Y : TopCat.{u}} (i : A ⟶ B)
    (hi : HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes i)
    {a b : C(A, Y)} (α : a.Homotopy b) (x : Extension i a) : Extension i b :=
  Classical.choose (exists_track i hi α x)

theorem chooseTrack_hasTrack {A B Y : TopCat.{u}} (i : A ⟶ B)
    (hi : HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes i)
    {a b : C(A, Y)} (α : a.Homotopy b) (x : Extension i a) :
    hasTrack i α x (chooseTrack i hi α x) :=
  Classical.choose_spec (exists_track i hi α x)

noncomputable def extensionTransport {A B Y : TopCat.{u}} (i : A ⟶ B)
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

theorem extensionTransport_symm_left {A B Y : TopCat.{u}} (i : A ⟶ B)
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

theorem extensionTransport_symm_left_class {A B Y : TopCat.{u}} (i : A ⟶ B)
    (hi : HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes i)
    {a b : C(A, Y)} (α : a.Homotopy b) (x : ExtensionClass i a) :
    extensionTransport i hi α.symm (extensionTransport i hi α x) = x := by
  refine Quotient.inductionOn x ?_
  intro x
  exact extensionTransport_symm_left i hi α x

theorem extensionTransport_bijective {A B Y : TopCat.{u}} (i : A ⟶ B)
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

def postcomposeExtension {A B Y Z : TopCat.{u}} (i : A ⟶ B)
    (a : C(A, Y)) (φ : C(Y, Z)) :
    Extension i a → Extension i (φ.comp a) := fun x =>
  ⟨φ.comp x.val, by
    ext z
    change φ (x.val (i.hom z)) = φ (a z)
    exact congrArg φ (congrArg (fun m : C(A, Y) => m z) x.property)⟩

def postcomposeExtensionClass {A B Y Z : TopCat.{u}} (i : A ⟶ B)
    (a : C(A, Y)) (φ : C(Y, Z)) :
    ExtensionClass i a → ExtensionClass i (φ.comp a) :=
  Quotient.map (postcomposeExtension i a φ) (by
    intro x y h
    exact h.comp_continuousMap φ)

theorem extensionTransport_natural_postcompose {A B Y Z : TopCat.{u}}
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

/-- Surjectivity of postcomposition on extension classes is invariant under homotopy of the
boundary map. -/
theorem postcomposeExtensionClass_surjective_of_homotopy {A B Y Z : TopCat.{u}} (i : A ⟶ B)
    (hi : HomotopyHypothesis.Henry.Top.relativeFiniteCellComplexes i)
    {a b : C(A, Y)} (α : a.Homotopy b) (φ : C(Y, Z))
    (h : Function.Surjective (postcomposeExtensionClass i b φ)) :
    Function.Surjective (postcomposeExtensionClass i a φ) := by
  intro y
  let T' := extensionTransport i hi ((ContinuousMap.Homotopy.refl φ).comp α)
  obtain ⟨x', hx'⟩ := h (T' y)
  obtain ⟨x, rfl⟩ := (extensionTransport_bijective i hi α).2 x'
  refine ⟨x, (extensionTransport_bijective i hi ((ContinuousMap.Homotopy.refl φ).comp α)).1 ?_⟩
  exact (extensionTransport_natural_postcompose i hi α φ x).symm.trans hx'

end

end HomotopyHypothesis.Completion.Compression
